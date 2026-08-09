(ns kotoba.sema-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.hir :as hir]
            [kotoba.sema :as sema]))

(deftest source-to-checked-hir
  (testing "untyped source produces the compatibility HIR profile"
    (let [result (sema/analyze "(defn main [] 42)")]
      (is (= :kotoba.hir/v2 (:format result)))
      (is (= 'main (:entry result)))
      (is (= :i64 (:result result)))
      (is (hir/valid? result))))
  (testing "typed source produces typed HIR"
    (let [result (sema/analyze "(defn main [] :string \"ok\")")]
      (is (= :kotoba.hir/v3 (:format result)))
      (is (= :string (get-in result [:functions 0 :result])))
      (is (hir/valid? result)))))

(deftest reader-and-schema-contracts
  (is (= 'defn (ffirst (sema/read-forms "(defn main [] 42)"))))
  (let [table {:app/item
               [:record :app/item
                [[:value :i64]
                 [:next [:option [:ref :app/item]]]]]}]
    (is (= table (sema/validate-schema-table! table)))
    (is (re-matches #"[0-9a-f]{64}"
                    (get (sema/schema-identities table) :app/item)))))

(deftest semantic-catalogs-are-on-the-classpath
  (is (some? (clojure.java.io/resource
              "kotoba/lang/capability-catalog.edn")))
  (is (some? (clojure.java.io/resource
              "kotoba/lang/guest-grammar.edn")))
  (is (seq sema/capability-registry))
  (is (seq sema/source-operation-registry)))
