(ns cljscadld.extractor
  "Tool for extracting definitions and their cross-references
  via their static symbol usage."
  (:require [cljs.analyzer :as ana]
            [cljs.build.api :as bapi]
            [cljs.compiler :as comp]
            [cljs.tagged-literals :as tags]
            [cljs.util :as cutil]
            [clojure.tools.reader :as reader]
            [cljs.closure :as closure]
            [cljs.env :as env]
            [clojure.java.io :as io]
            [cljs.js-deps :as deps]
            [clojure.tools.reader.reader-types :as readers]
            [clojure.set :as set]
            [clojure.string :as str]
            [datomic.api :only [q db] :as d])
  (:import (java.util.jar JarFile)
           (java.io Closeable)))

(def ^:private ^:dynamic *collected-symbols*
  (atom {:symbols (set nil)}))

(defn- symbol-handler
  "Collects ``unresolved'' symbols."
  [warning-type env extra]
  (when (warning-type ana/*cljs-warnings*)
    (case warning-type
      :undeclared-var (reset! *collected-symbols*
                              {:symbols (conj
                                          (:symbols @*collected-symbols*) extra)})
      (str "default WARNING " warning-type " " extra))))

(defn- resolve-sym
  "Custom symbol resolution (returns a new ns/id)."
  [sym local-env global-env local-ns]
  (let [prefix (:prefix sym)
        local? (or (= prefix 'cljs.user) (= prefix local-ns))
        full-prefix ((keyword prefix) local-env)
        env (if local? local-env (get global-env (keyword full-prefix) {}))
        result (get env (keyword (:suffix sym)) nil)]
    (if (nil? result)
      (do (println (str "UNRESOLVED " sym))
          result)
      (symbol result))))

(defn- filter-out-macros
  "Filters out symbols that are in macro namespaces."
  [sym-deps all-macros]
  (group-by
    #(and
       (nil? ((keyword (:prefix %)) (:mreqs all-macros)))
       (nil? ((keyword (:suffix %)) (:muses all-macros))))
    sym-deps))

(defn- handle-prot
  "Handles protocol definitions."
  [prot-def local-ns]
  (let [prot-name (first prot-def)
        prot-meths (map first (:methods (:protocol-info (second prot-def))))
        result (mapcat (fn [x] [(keyword x) local-ns]) prot-meths)]
    (assoc (apply hash-map result) (keyword prot-name) local-ns)))

(defn- handle-defs
  "Handles other definitions."
  [defs local-ns]
  (let [result (mapcat (fn [x] [(keyword (first x)) local-ns]) defs)]
    (apply hash-map result)))

(defn- transform-ns
  "Extracts parsed namespace info. TODO: may not be needed"
  [inputs]
  (let [parsed-nss (fn [path] (map (fn [x]
                                     (filter #(not= (first %) (second %)) x))
                                   (map #(get-in % path) inputs)))
        nss-requires (parsed-nss [:ast :requires])
        nss-rmacros (parsed-nss [:ast :require-macros])
        nss-umacros (parsed-nss [:ast :use-macros])
        map-nss (fn [r] (map (fn [x]
                               (apply hash-map (mapcat (fn [y] [(keyword (first y)) (second y)]) x)))
                             r))
        nss (map #(keyword (:ns %)) inputs)
        res (zipmap nss (map-nss nss-requires))
        resu (zipmap nss (map-nss (parsed-nss [:ast :uses])))
        resm (zipmap nss (map-nss nss-rmacros))
        resum (zipmap nss (map-nss nss-umacros))]
    {:requires res :uses resu :macros resm :macrosu resum}))

(defn- list-jar
  "Returns files in the given jar's inner directory."
  [jar-path inner-dir]
  (if-let [jar (JarFile. jar-path)]
    (let [inner-dir (if (and (not= "" inner-dir) (not= "/" (last inner-dir)))
                      (str inner-dir "/")
                      inner-dir)
          entries (enumeration-seq (.entries jar))
          names (map #(.getName %) entries)
          snames (filter #(zero? (.indexOf % inner-dir)) names)
          fsnames (map #(subs % (count inner-dir)) snames)]
      fsnames)))

(defn- read-from-jar
  "Opens up an input stream from given jar's inner file."
  [jar-path inner-path]
  (if-let [jar (JarFile. jar-path)]
    (if-let [entry (.getJarEntry jar inner-path)]
      [(.getInputStream jar entry) inner-path])))

(defn- cljs-files-in-jar
  "Return a sequence of all .cljs and .cljc files in the JAR file."
  [jar-path]
  (filter
    #(let [name %]
       (and (or (.endsWith name ".cljs")
                (.endsWith name ".cljc"))
            (not= \. (first name))
            (not (contains? comp/cljs-reserved-file-names name))))
    (list-jar jar-path "")))

(defn- forms-seq-source
  "Custom form sequence reader to use with a source logging pushback reader."
  [^Closeable pbr filename]
  (let [eof-sentinel (Object.)
        opts (merge
               {:eof eof-sentinel}
               (if (and filename (= (cutil/ext filename) "cljc"))
                 {:read-cond :allow :features #{:cljs}}))
        data-readers tags/*cljs-data-readers*
        forms-seq_
        (fn forms-seq_ []
          (lazy-seq
            (let [form (binding [*ns* (create-ns ana/*cljs-ns*)
                                 reader/*data-readers* data-readers
                                 reader/*alias-map*
                                 (apply merge
                                        ((juxt :requires :require-macros)
                                          (ana/get-namespace ana/*cljs-ns*)))
                                 reader/resolve-symbol ana/resolve-symbol]
                         (reader/read opts pbr))]
              (if (identical? form eof-sentinel)
                (.close pbr)
                (cons form (forms-seq_))))))]
    (forms-seq_)))

(defn- retrieve-env
  "Returns a symbol resolution environment for a given unique id."
  [conn eid]
  (let [q-result (d/q `[:find ?n ?sym ?fid
                        :where
                        [~eid :project/files ?f]
                        [?f :file/namespace ?n]
                        [?f :file/forms ?d]
                        [?d :slice/fid ?fid]
                        [?d :slice/symbols ?sym]] (d/db conn))]
    (if (not-empty q-result)
      (reduce (fn [x y] (merge-with merge x y))
              (map (fn [z]
                     {(keyword (get z 0)) {(keyword (get z 1)) (get z 2)}}
                     )
                   q-result))
      {})))

(def ^:private ^:dynamic *error-log* (atom nil))

(defn extract-decls
  "Extract cross-ref declaration on a given path or in a given JAR."
  [cljs-paths eid conn]
  (let [unpacked (vector? cljs-paths)
        source (if unpacked (mapcat comp/cljs-files-in
                                    (closure/-paths (apply bapi/inputs cljs-paths)))
                            (cljs-files-in-jar cljs-paths))
        compiler-env (if-not (nil? env/*compiler*)
                       env/*compiler*
                       (env/default-compiler-env {}))
        dep-eids (d/q `[:find ?e :where
                        [~eid :project/dependsOn ?e]]
                      (d/db conn))]
    (binding [ana/*cljs-warning-handlers* (:warning-handlers {} ana/*cljs-warning-handlers*)
              env/*compiler* compiler-env]
      (let [inputs (deps/dependency-order
                     (map #(let [rdr (if unpacked (io/reader %)
                                                  (io/reader (first (read-from-jar cljs-paths %))))
                                 forms (forms-seq-source
                                         (readers/source-logging-push-back-reader (readers/push-back-reader rdr))
                                         (cutil/path %))]
                             (merge
                               (ana/parse-ns forms) {:source-file % :reader-ns rdr}))
                          source))
            local-env (atom {})
            global-env (atom (reduce merge (map #(retrieve-env conn (first %)) dep-eids)))
            nss-all (transform-ns inputs)
            nss-reqmap (:requires nss-all)]
        (println (map :ns inputs))
        (doseq [{:keys [source-file ns] :as ns-info} inputs]
          (when-not (boolean (ffirst
                               (d/q `[:find ?c :where [~eid :project/files ?c]
                                      [?c :file/namespace ~(str ns)]] (d/db conn))))
            @(d/transact conn [{:db/id          #db/id[:db.part/user -1],
                                :file/namespace (str ns)}
                               {:db/id     #db/id[:db.part/user -1],
                                :file/cljc (= (cutil/ext source-file) "cljc")}
                               {:db/id         eid,
                                :project/files #db/id[:db.part/user -1]}]))
          (let [fileid (ffirst
                         (d/q `[:find ?c :where [~eid :project/files ?c]
                                [?c :file/namespace ~(str ns)]] (d/db conn)))
                opts {:optimizations :none}
                nsk (keyword ns)
                ns-reqs (nsk nss-reqmap)
                ns-uses (reduce merge (map (fn [x] {(first x) (get-in @global-env [(keyword (second x)) (first x)])})
                                           (nsk (:uses nss-all))))
                ns-macs {:mreqs (nsk (:macros nss-all)) :muses (nsk (:macrosu nss-all))}]
            (cutil/debug-prn "Analyzing" (str source-file " " ns))
            (when-not (get-in @env/*compiler* [::ana/namespaces 'cljs.core :defs])
              (ana/analyze-file "cljs/core.cljs" opts))
            (reset! local-env (merge ns-uses ns-reqs @local-env))
            (binding [ana/*cljs-ns* 'cljs.user
                      ana/*unchecked-if* false
                      ana/*cljs-warning-handlers* [symbol-handler]]
              (let [env (merge-with merge (assoc (ana/empty-env) :build-options opts)
                                    {:ns {:excludes (get-in ns-info [:ast :excludes])}})
                    forms (:source-forms ns-info)]
                (doseq [form forms]
                  (try (ana/analyze env form nil opts)
                       (catch Exception e (swap! *error-log* conj
                                                 [source-file form (str "caught exception: " (.getMessage e))])))
                  (cutil/debug-prn "form: " form "\n")
                  (let [all-defs (get-in @env/*compiler* [::ana/namespaces 'cljs.user :defs])
                        d1 (first all-defs)
                        d1-info (second d1)
                        d1-sym (map (fn [x] {:prefix ns :suffix x :macro-present? false}) (keys all-defs))
                        sym-deps (set/difference (:symbols @*collected-symbols*) (set d1-sym))
                        {deps true macro-deps false} (filter-out-macros sym-deps ns-macs)
                        sym-mapping (map (fn [x] [x (resolve-sym x @local-env @global-env ns)]) deps)
                        {unresolved-sym true resolved-sym false} (group-by
                                                                   #(nil? (re-matches #"[s|0-9|\-]+" (str (second %))))
                                                                   sym-mapping)
                        entry-form (:source (meta form))
                        entry {:deps (map second resolved-sym) :unknown unresolved-sym :macro-deps macro-deps}
                        entry-h (str "s" (hash entry-form) (hash entry))]
                    (when (not-empty d1-info)
                      (let [def-info
                            (if (:protocol-symbol d1-info)
                              (handle-prot d1 entry-h)
                              (handle-defs all-defs entry-h))
                            def-filter (filter #(not (str/includes? % "t_cljs")) (map name (keys def-info)))]
                        (swap! local-env merge def-info)
                        (when-not (boolean (ffirst
                                             (d/q `[:find ?c :where [~fileid :file/forms ?c]
                                                    [?c :slice/fid ~entry-h]] (d/db conn))))
                          (let [tx-data (concat [{:db/id     #db/id[:db.part/user -1],
                                                  :slice/fid entry-h}
                                                 {:db/id      fileid,
                                                  :file/forms #db/id[:db.part/user -1]}
                                                 {:db/id      #db/id[:db.part/user -1],
                                                  :slice/code entry-form}
                                                 {:db/id         #db/id[:db.part/user -1],
                                                  :slice/rawDefs (str all-defs)}
                                                 {:db/id           #db/id[:db.part/user -1],
                                                  :slice/isPrivate (boolean (:private d1-info))}]
                                                (map (fn [x] {:db/id         #db/id[:db.part/user -1],
                                                              :slice/symbols (str x)}) def-filter)
                                                (map (fn [x] {:db/id           #db/id[:db.part/user -1],
                                                              :slice/dependsOn [[:slice/fid (str x)]]}) (:deps entry))
                                                (map (fn [x] {:db/id              #db/id[:db.part/user -1],
                                                              :slice/resolvedDeps (str x)}) resolved-sym)
                                                (map (fn [x] {:db/id             #db/id[:db.part/user -1],
                                                              :slice/missingDeps (str x)}) (:unknown entry))
                                                (map (fn [x] {:db/id           #db/id[:db.part/user -1],
                                                              :slice/macroDeps (str x)}) (:macro-deps entry)))]
                            (cutil/debug-prn "tx-data: " tx-data "\n")
                            @(d/transact conn tx-data)))))
                    (cutil/debug-prn "entry: " entry "\n"))
                  (reset! *collected-symbols* {:symbols (set nil)})
                  (swap! env/*compiler* update-in [::ana/namespaces 'cljs.user] {}))
                (.close (:reader-ns ns-info))
                (swap! global-env merge {nsk @local-env})
                (reset! local-env {})))))
        @global-env))))