(ns kotoba.compiler.case-uniqueness-test
  "`case` over integer constants, on both runtimes.

  ClojureScript cannot hash a JS `bigint`: `cljs.core/hash` reaches
  `goog.getUid`, which sets a property on the object, and a bigint is a
  primitive. `distinct` stays linear up to eight elements and only then
  converts to a hash set, so `desugar-case`'s uniqueness check
  `(count (distinct constants))` compiled a case with eight integer arms and
  threw `Cannot create property 'closure_uid_...' on bigint` at the ninth --
  on ClojureScript only, because a `.kotoba` integer literal is a bigint there
  and a Long on the JVM, where 64 arms were always fine.

  The visible cost was in the source people write. `aiueos/kotoba/sha256.kotoba`
  spells SHA-256's 64 round constants as a 63-deep nested `if`, which is what
  is left when `case` is not available for a constant table.

  These tests are `.cljc` on purpose: on the JVM every one of them passed
  before the fix, which is exactly why nothing noticed."
  (:require #?(:clj  [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer [deftest is testing] :include-macros true])
            [clojure.string :as str]
            [kotoba.sema :as sema]))

(defn- integer-case-source [n]
  (str "(defn k [i :i64] :i64 (case i "
       (str/join " " (map #(str % " " (+ 1000 %)) (range n)))
       " 0))\n(defn main [] :i64 (k 3))"))

(defn- analyzes? [source]
  (try (do (sema/analyze source) true)
       (catch #?(:clj Throwable :cljs :default) _ false)))

(defn- rejection-of [source]
  (try (do (sema/analyze source) nil)
       (catch #?(:clj Throwable :cljs :default) e (ex-message e))))

(deftest integer-case-past-the-hash-threshold-analyzes
  (testing "eight was the last arm that worked; nine is where it threw"
    (is (analyzes? (integer-case-source 8)))
    (is (analyzes? (integer-case-source 9))
        "a ninth integer arm is where `distinct` starts hashing")
    (is (analyzes? (integer-case-source 16)))
    (is (analyzes? (integer-case-source 32)))))

(deftest duplicate-integer-constants-are-still-refused
  (testing "the check still checks -- a uniqueness test that never fires is worse than the bug"
    (is (str/includes?
         (str (rejection-of "(defn k [i :i64] :i64 (case i 0 1 1 2 2 3 3 4 4 5 5 6 6 7 7 8 0 9 0))\n(defn main [] :i64 (k 0))"))
         "case constants must be unique"))))

(deftest an-integer-does-not-collide-with-its-own-text
  (testing "keying integers by decimal text must not make 5 equal to \"5\" or :5"
    ;; If the key were the bare string, these would read as duplicates and be
    ;; refused. They are different dispatch values and must both be admitted.
    (is (analyzes? "(defn k [x :keyword] :i64 (case x :5 1 :a 2 :b 3 :c 4 :d 5 :e 6 :f 7 :g 8 :h 9 0))\n(defn main [] :i64 (k :a))"))))

(deftest keyword-arms-were-never-affected
  (testing "keywords hash on every runtime, so nine of them always worked"
    (is (analyzes? "(defn k [x :keyword] :i64 (case x :a 1 :b 2 :c 3 :d 4 :e 5 :f 6 :g 7 :h 8 :i 9 0))\n(defn main [] :i64 (k :c))"))))
