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
            ;; a wrong argument count is refused in both directions
            [kotoba.compiler.call-arity-test]
            [kotoba.compiler.case-uniqueness-test]
            ;; boot-scratch: the writable region and a function's address
            [kotoba.compiler.boot-scratch-test]
            ;; fwstore: writing to pages the firmware allocated
            [kotoba.compiler.firmware-store-test]
            [kotoba.compiler.host-nesting-test]
            ;; a `let` body is an implicit `do`; the value is the last form
            [kotoba.compiler.let-body-test]
            [kotoba.compiler.kernel-xgetbv-test]
            ;; xsave: the write half -- CR4 and xsetbv
            [kotoba.compiler.kernel-xsetbv-test]
            ;; isr: the interrupt entry name and signature rules
            [kotoba.compiler.interrupt-entry-test]
            [kotoba.compiler.oracle-reach-test]
            [kotoba.compiler.parameter-annotation-test]
            [kotoba.compiler.defdesugar-test]
            [kotoba.compiler.match-test]
            [kotoba.compiler.parameter-inference-test]
            ;; boot-lit: the read-only literal heads, and (loader) the rule
            ;; that makes one of their addresses a bounded load's region root
            [kotoba.compiler.rodata-literal-test]
            ;; `[:map K V]` reached through the friendly surface: an integer
            ;; or string key, the order the entry chain is walked in, and the
            ;; byte-identity control on the keyword-keyed literal
            [kotoba.compiler.typed-map-key-types-test]
            ;; a loop's accumulator may be any admitted type, not only an i64
            [kotoba.compiler.loop-accumulator-type-test]
            ;; conj/disj on a typed set, and a set-item refusal that names
            ;; the set. Landed as `.cljc` without either list entry, so the
            ;; nbb half had never run -- and a suite that does not run a file
            ;; reports the same clean answer as one that runs it and passes.
            [kotoba.compiler.set-operations-test]
            ;; `count` on every collection that has a count primitive, and the
            ;; pair accessors reaching a bounded vector -- the heads the
            ;; language authority declared on three backends and nothing
            ;; implemented. The `case` this adds to inference dispatches on
            ;; `[op value-type]`, and ClojureScript is where a `case` over
            ;; composite constants has broken before, so it belongs here.
            [kotoba.compiler.collection-heads-test]
            ;; a declared type of the wrong SHAPE is refused, not crashed --
            ;; and 42 of the 76 programs that crashed did so only under nbb,
            ;; because ClojureScript hashes a bigint to answer `contains?`
            [kotoba.compiler.malformed-type-argument-test]))

(defmethod t/report [:cljs.test/default :end-run-tests] [m]
  (println (str "\nnbb: " (:test m) " tests, " (:pass m) " passed, "
                (:fail m) " failed, " (:error m) " errors"))
  (when (pos? (+ (or (:fail m) 0) (or (:error m) 0)))
    (set! (.-exitCode js/process) 1)))

(t/run-tests 'kotoba.compiler.call-arity-test
             'kotoba.compiler.case-uniqueness-test
             'kotoba.compiler.boot-scratch-test
             'kotoba.compiler.firmware-store-test
             'kotoba.compiler.host-nesting-test
             'kotoba.compiler.let-body-test
             'kotoba.compiler.kernel-xgetbv-test
             'kotoba.compiler.kernel-xsetbv-test
             'kotoba.compiler.interrupt-entry-test
             'kotoba.compiler.oracle-reach-test
             'kotoba.compiler.parameter-annotation-test
             'kotoba.compiler.defdesugar-test
             'kotoba.compiler.match-test
             'kotoba.compiler.parameter-inference-test
             'kotoba.compiler.rodata-literal-test
             'kotoba.compiler.typed-map-key-types-test
             'kotoba.compiler.loop-accumulator-type-test
             'kotoba.compiler.set-operations-test
             'kotoba.compiler.collection-heads-test
             'kotoba.compiler.malformed-type-argument-test)
