(ns kotoba.compiler.kotoba-reader-test
  "JVM-free reader tests for the `#()` fn shorthand (lang-cosientist
  iteration 3). Runs on the nbb route like the rest of run-tests.cljs.

  Integer literals read as JS bigint, so expected forms are built with
  `(js/BigInt \"2\")` rather than quoted literals -- a quoted `2` in CLJS
  is a double and `=` fails against the reader's bigint."
  (:require [clojure.string :as str]
            [clojure.test :as t :refer [deftest is]]
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

;; ── source-location, after the line index (build-scaling co-scientist it. 2) ──
;;
;; `source-location` used to re-derive line/column at every located node by
;; `subs`-ing the whole prefix and splitting it on newlines, which is O(offset)
;; per node and quadratic in source size. It is now a binary search over one
;; line-start index. These pin the three positions a binary search gets wrong
;; when its boundary condition is off: the very first form, a form that starts
;; exactly ON a line start, and a form on the last line.

(deftest locations-on-the-first-line
  (let [[a b] (r/read-forms "(a) (b)")]
    (is (= {:line 1 :column 1} (select-keys (meta a) [:line :column])))
    (is (= {:line 1 :column 5} (select-keys (meta b) [:line :column])))))

(deftest location-at-a-line-start
  ;; `(b)` begins at offset 4, which is itself a line start.
  (let [[_ b] (r/read-forms "(a)\n(b)")]
    (is (= {:line 2 :column 1 :offset 4}
           (select-keys (meta b) [:line :column :offset])))))

(deftest location-on-a-late-line-is-indented-from-that-line-not-the-file
  (let [source (str (apply str (repeat 200 "(a)\n")) "  (z)")
        forms (r/read-forms source)]
    (is (= {:line 201 :column 3} (select-keys (meta (last forms)) [:line :column])))))

(deftest locations-agree-with-counting-newlines-at-every-form
  ;; The property the fast path has to preserve, checked against the slow
  ;; definition rather than against remembered numbers.
  (let [source "(a)\n  (b (c))\n\n(d)\n     (e)\n"
        expected (fn [offset]
                   (let [prefix (subs source 0 offset)
                         nl (count (filter #(= \newline %) prefix))]
                     {:line (inc nl)
                      :column (inc (- offset (inc (or (str/last-index-of prefix "\n") -1))))}))]
    (doseq [form (r/read-forms source)]
      (is (= (expected (:offset (meta form)))
             (select-keys (meta form) [:line :column]))
          (str "form " (pr-str form)))))) 

;; ── set literals of exact integers ────────────────────────────────────────
;;
;; An exact Kotoba i64 literal reads as a JavaScript BigInt, `cljs.core/set`
;; switches to a hashed representation above eight elements, and nbb cannot
;; hash a BigInt. Nine integers in a set therefore threw a raw TypeError about
;; `closure_uid_...`, which reached the caller as `source reader rejected
;; input` with no reason attached to it at all.
;;
;; The limit is NOT lifted here -- reading the set without hashing gets past
;; the reader and hits the same barrier inside elaboration, which turns a
;; refusal into an internal compiler error. It is named instead.

(deftest eight-exact-integers-in-a-set-read
  (is (= 8 (count (first (r/read-forms "#{1 2 3 4 5 6 7 8}"))))))

(deftest nine-exact-integers-in-a-set-are-refused-by-name
  ;; ONE host, and the asymmetry is the point rather than an oversight. A
  ;; Clojure set hashes a BigInt without complaint, so on the JVM nine exact
  ;; integers read like any other nine values; the failure mode this refusal
  ;; names exists only where `cljs.core/set` does.
  ;;
  ;; Written as one assertion per host rather than skipped on the JVM, because
  ;; a skipped half says nothing and this half says something: it is the
  ;; control that keeps the refusal honest. If the reader ever started
  ;; refusing on the JVM too, the guard would have stopped being about the
  ;; host that has the problem.
  (let [e (try (r/read-forms "#{1 2 3 4 5 6 7 8 9}") nil
               (catch #?(:clj Throwable :cljs :default) error error))]
    #?(:clj
       (is (nil? e)
           "the JVM has no BigInt hashing problem, so nothing is refused there")
       :cljs
       (do
         (is (some? e) "nine exact integers in a set is refused")
         (is (str/includes? (ex-message e) "exact-integer")
             (str "the refusal names its reason, got: " (ex-message e)))
         (is (= 9 (:count (ex-data e))))))))

(deftest nine-keywords-in-a-set-still-read
  ;; The barrier is the BigInt, not the count -- keywords hash fine.
  (is (= 9 (count (first (r/read-forms "#{:a :b :c :d :e :f :g :h :i}"))))))
