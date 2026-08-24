;; nbb --classpath "src:test:$(clojure -Spath -M:test)" run-tests.cljs
;;
;; The portable side of this suite. Not most of it: kotoba.compiler.frontend is
;; `.cljc` and claims two runtimes, but `test/kotoba/sema_test.clj` is `.clj`
;; and there is no fleet gate here, so until 2026-08-24 nothing had ever
;; executed its `:cljs` behaviour. What that hid: `desugar-case` checked
;; uniqueness with `distinct`, which hashes above eight elements, and
;; ClojureScript cannot hash the bigint a `.kotoba` integer literal is.
;;
;; Anything added to `test/` as `.cljc` belongs in BOTH lists below -- being
;; required is not being run. `scripts/verify-cljs-runner-completeness.cljs` in
;; the superproject measures this file against the directory.
(ns run-tests
  (:require [cljs.test :as t]
            [kotoba.compiler.case-uniqueness-test]
            [kotoba.compiler.host-nesting-test]
            [kotoba.compiler.oracle-reach-test]))

(defmethod t/report [:cljs.test/default :end-run-tests] [m]
  (println (str "\nnbb: " (:test m) " tests, " (:pass m) " passed, "
                (:fail m) " failed, " (:error m) " errors"))
  (when (pos? (+ (or (:fail m) 0) (or (:error m) 0)))
    (set! (.-exitCode js/process) 1)))

(t/run-tests 'kotoba.compiler.case-uniqueness-test
             'kotoba.compiler.host-nesting-test
             'kotoba.compiler.oracle-reach-test)
