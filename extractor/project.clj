(defproject extractor "0.1.0"
  :description "Tool for extracting definitions and their cross-references\n  via their static symbol usage."
  :url "https://github.com/hkuplg/cljscadld/"
  :license
  {:name "Eclipse Public License - v 1.0"
   :url "http://www.eclipse.org/legal/epl-v10.html"
   :distribution :repo}
  :repositories {"my.datomic.com" {:url "https://my.datomic.com/repo"
                                   :creds :gpg}}
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [com.datomic/datomic-pro "0.9.5530"]
                 [org.clojure/clojurescript "1.9.293"]])