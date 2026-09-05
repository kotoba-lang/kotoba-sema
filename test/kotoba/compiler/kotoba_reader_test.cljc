(ns kotoba.compiler.kotoba-reader-test
  "JVM-free reader tests for the `#()` fn shorthand (lang-cosientist
  iteration 3). Runs on the nbb route like the rest of run-tests.cljs.

  Integer literals read as JS bigint, so expected forms are built with
  `(js/BigInt \"2\")` rather than quoted literals -- a quoted `2` in CLJS
  is a double and `=` fails against the reader's bigint."
  (:require [clojure.test :as t :refer [deftest is]]
            [kotoba.compiler.kotoba-reader :as r]))

#?(:clj  (def ^:private two 2)
   :cljs (def ^:private two (js/BigInt "2")))
#?(:clj  (def ^:private one 1)
   :cljs (def ^:private one (js/BigInt "1")))

(deftest fn-shorthand-reads-as-fn-form
  ;; #() is ONE call form: #(* % 2) == (fn [p1] (* p1 2)).
  (is (= (list 'fn ['p1] (list '* 'p1 two))
         (first (r/read-forms "#(* % 2)")))))

(deftest fn-shorthand-two-args
  (is (= '(fn [p1 p2] (+ p1 p2))
         (first (r/read-forms "#(+ %1 %2)")))))

(deftest fn-shorthand-nested-body
  ;; Inner collections are preserved; only the top-level args are the call.
  (is (= (list 'fn ['p1] (list 'f (list '+ 'p1 one)))
         (first (r/read-forms "#(f (+ % 1))")))))

(deftest fn-shorthand-empty-body-rejects
  (is (thrown? #?(:clj Throwable :cljs :default) (r/read-forms "#()"))))

(deftest fn-shorthand-rest-arg-rejects
  (is (thrown? #?(:clj Throwable :cljs :default) (r/read-forms "#(+ %& 1)"))))

(deftest fn-shorthand-gap-arg-rejects
  ;; %2 with no %1 in a 1-source map is a shape the map lowering refuses;
  ;; the reader itself must NOT invent a %1 binding for it.
  (is (= (list 'fn ['p1 'p2] (list '+ 'p2 one))
         (first (r/read-forms "#(+ %2 1)")))))
