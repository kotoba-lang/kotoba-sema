(ns kotoba.compiler.frontend
  ;; `clojure.set` is required on both runtimes, so `:require` is never
  ;; empty -- an empty `(:require)` (what results if EVERY item inside it
  ;; were individually `#?()`-conditional and none matched) fails ns-form
  ;; spec validation (confirmed live; see `kotoba.kir`'s ns form
  ;; for the fuller explanation). `#?@` (splicing) rather than `#?` here
  ;; because each branch below is more than one require-spec.
  (:require [clojure.set :as set]
            [kotoba.artifact.core :as artifact]
            [kotoba.compiler.schema :as schema]
            [kotoba.hir :as hir]
            [kotoba.kir.value :as value]
            #?@(:clj [[clojure.tools.reader :as reader]
                      [clojure.tools.reader.reader-types :as rt]]
                :cljs [[kotoba.compiler.kotoba-reader :as kr]
                       [kotoba.kir.cljs-i64 :as i64]])))

(defn- load-catalog-forbidden
  "P0: merge catalog forbidden-heads when guest-grammar.edn is on classpath."
  []
  #?(:clj
     (try
       (let [c (or (clojure.java.io/resource "kotoba/lang/guest-grammar.edn")
                   (clojure.java.io/resource "lang/guest-grammar.edn"))]
         (if c
           (with-open [r (clojure.java.io/reader c)]
             (let [edn (clojure.edn/read (java.io.PushbackReader. r))
                   heads (:forbidden-heads edn #{})]
               (into #{} (map (fn [x] (if (symbol? x) x (symbol (name x))))) heads)))
           #{}))
       (catch Exception _ #{}))
     :cljs #{}))

(def forbidden-heads
  (into '#{eval load load-file require use import ns-resolve resolve alter-var-root
           future pmap agent send send-off new . .. set! defmacro throw try catch
           locking dosync atom ref volatile!}
        (load-catalog-forbidden)))

;; The language-owned semantic catalog is vendored byte-for-byte from
;; kotoba-lang/kotoba-lang. The compiler derives both semantic-name -> wire ID
;; and friendly source-operation -> semantic-name maps from that one authority.
;; CLJS cannot synchronously read classpath resources, so its closed fallback
;; is checked against the resource by JVM tests.
(def ^:private capability-registry-cljs-fallback
  '{:identity/sign 1 :identity/verify 2 :hash/sha256 3 :http/post 4
    :log/read 5 :log/append 6 :clock/now 7 :state/transact 8
    :ui/commit 9 :ui/next-event 10 :llm/generate 11
    :storage/transact 12 :http/get-stream 13 :object/get-stream 14
    :object/put-block 15 :object/compare-and-set-ref 16
    :http/accept 17 :http/reply 18
    :fs/transact 19 :process/spawn 20 :secret/get 21
    :git/run 22 :entropy/draw 23})

(defn- load-capability-catalog []
  #?(:clj
     (try
       (let [c (clojure.java.io/resource "kotoba/lang/capability-catalog.edn")]
         (if c
           (with-open [r (clojure.java.io/reader c)]
             (clojure.edn/read (java.io.PushbackReader. r)))
           {:capabilities
            (into {} (map (fn [[name id]]
                            [name {:source-operation (symbol (namespace name) (clojure.core/name name))
                                   :effect name :compiler-wire-id id}]))
                  capability-registry-cljs-fallback)}))
       (catch Exception _
         {:capabilities
          (into {} (map (fn [[name id]]
                          [name {:source-operation (symbol (namespace name) (clojure.core/name name))
                                 :effect name :compiler-wire-id id}]))
                capability-registry-cljs-fallback)}))
     :cljs
     {:capabilities
      (into {} (map (fn [[name id]]
                      [name {:source-operation (symbol (namespace name) (clojure.core/name name))
                             :effect name :compiler-wire-id id}]))
            capability-registry-cljs-fallback)}))

(def capability-catalog (load-capability-catalog))

(def capability-registry
  "Semantic capability name -> stable compiler wire ID."
  (into {} (map (fn [[name entry]] [name (:compiler-wire-id entry)]))
        (:capabilities capability-catalog)))

(def source-operation-registry
  "Friendly qualified source operation -> semantic capability name."
  (into {} (map (fn [[name entry]] [(:source-operation entry) name]))
        (:capabilities capability-catalog)))

(def capability-id->name
  "Inverse of capability-registry for diagnostics and effect ceilings."
  (into {} (map (fn [[k v]] [v k]) capability-registry)))

(def arithmetic '#{+ - * quot bit-xor bit-and bit-or})
(def i32-operations
  '{i32-wrap 1 u32-wrap 1 i32-wrapping-add 2 i32-wrapping-mul 2 i32-xor 2
    i32-shift-left 2 i32-shift-right 2 u32-shift-right 2 xorshift32 1})
;; ADR-2607254600 D1/D2. `bit-and`/`bit-xor` were already 64-bit
;; (`i64.and` 0x83 / `i64.xor` 0x85) while the only shifts were 32-bit, so a
;; 64-bit lane rotation -- the body of Keccak-f[1600], and the natural shape of
;; u256 limb arithmetic -- could not be written at all. Wasm has had
;; `i64.shl`/`i64.shr_s`/`i64.shr_u` since the MVP; this was an unimplemented
;; op, not a spec limit.
;;
;; The shift count is restricted to a literal in [0,63], mirroring the existing
;; [0,31] rule for the i32 shifts. Wasm itself masks the count modulo the
;; width, so a dynamic count would be safe to emit; the literal rule is a
;; frontend admission choice that keeps the emitted shift auditable. A dynamic
;; count (needed for EVM SHL/SHR, whose amount is a stack value) is a separate
;; change with its own reasoning.
;;
;; Rotation is deliberately absent: with a literal count `n`, `64 - n` is also
;; a literal, so `rotl(x, n)` is exactly
;; `(bit-or (i64-shift-left x n) (u64-shift-right x (- 64 n)))`. Adding
;; `i64.rotl`/`i64.rotr` as single instructions is a follow-up once these
;; primitives are proven, not a prerequisite.
(def i64-operations
  '{bit-not 1 i64-shift-left 2 i64-shift-right 2 u64-shift-right 2})
(def comparisons '#{= < > <= >=})
(def heap-operations '{pair 2 pair-first 1 pair-second 1})
;; kgraph-* (ADR-2607198300): all-integer EAVT datom store, the native
;; (JVM/Node/browser-free) analog of kotoba-lang/kotoba's string/EDN-based
;; kgraph-assert!/kgraph-query -- this backend has no addressable buffer for
;; EDN text, so entity/attribute/value are caller-assigned integer ids.
(def kgraph-operations '{kgraph-assert! 3 kgraph-get 2 kgraph-count 1 kgraph-entity-at 2})
(def kernel-memory-operations
  '{kernel-load-u8 3 kernel-load-u8-4k 3 kernel-load-u8-16k 3
    kernel-store-u8 4 kernel-store-u8-4k 4
    kernel-load-u32 3 kernel-store-u32 4
    ;; (kernel-subregion base length offset sublen) -> base+offset, trapping
    ;; unless offset+sublen fits inside length. Listed here so its first
    ;; argument is checked as a base like every other kernel op's: a derived
    ;; window is only as good as the window it was derived from.
    kernel-subregion 4})
;; `kernel-in-u8`/`kernel-in-u32` are the READ half of x86 port I/O, and take
;; only the port -- `(kernel-in-u8 port)` -> the byte that port yields,
;; zero-extended to i64. Their absence, next to a write half that had been
;; here from the start, was not a small gap: PCI configuration space is
;; addressed by WRITING 0xCF8 and then READING 0xCFC, so with port I/O that
;; could only write, PCI enumeration -- and therefore every device driver --
;; could not be expressed in Kotoba at all and had to stay in C.
;;
;; A port read is an effect in both directions: it observes device state that
;; may differ on each read, and on many devices reading is itself a write
;; (interrupt acknowledgement, FIFO pop). It is therefore listed here among
;; the privileged operations, never treated as pure, and never oracled -- the
;; same treatment `kernel-out-u8` already receives.
;;
;; `kernel-read-msr`/`kernel-write-msr` are the model-specific registers, the
;; other half of x86's out-of-band CPU state. Unlike a port they are not a bus
;; transaction, but they are privileged for the same reason control registers
;; are: `rdmsr`/`wrmsr` fault outside ring 0, and what they name -- EFER's NX
;; enable, the APIC base address, the SYSCALL entry point (STAR/LSTAR/FMASK) --
;; is machine configuration, not a value.
;;
;; `(kernel-read-msr index)` -> the register's 64 bits, arity 1;
;; `(kernel-write-msr index value)` -> writes them, arity 2, mirroring
;; `kernel-out-*`. A read is never oracled: the value is whatever the CPU (or
;; firmware, or a previous write from another core) put there, and a compile
;; time answer would be an invention.
;;
;; The gap this closes is a duplication, not an absence: aiueos carries three
;; independent `read_msr`/`write_msr` inline-asm pairs -- apic.c, paging.c and
;; process.c -- because C had no other way to spell it. One primitive replaces
;; all three, and is what lets the SYSCALL transport setup (STAR, LSTAR, EFER,
;; FMASK) leave C at all.
;;
;; `kernel-cpuid-eax`/`-ebx`/`-ecx`/`-edx` are CPU FEATURE DETECTION, the
;; question every one of the six `cpuid` sites in aiueos is actually asking:
;; does this CPU support NX (paging.c), does it support SYSCALL (process.c),
;; what does this virtio device advertise (pci.c). Each site queries a leaf,
;; tests a bit, and DECIDES -- and the decision is exactly the part that
;; belongs in Kotoba rather than in inline asm.
;;
;; `(kernel-cpuid-eax leaf subleaf)` -> the EAX the CPU returned for that
;; (leaf, subleaf), zero-extended to i64; `-ebx`, `-ecx` and `-edx` the same
;; for their own result register. Arity 2 for all four, because `cpuid` reads
;; TWO inputs -- the leaf in `eax` and the subleaf in `ecx` -- and a leaf whose
;; subleaf was whatever happened to be in `ecx` is a different query. Leaves
;; that ignore the subleaf (0x80000001, the NX one) simply pass 0.
;;
;; FOUR primitives, each executing its own `cpuid`, is deliberate. One
;; instruction writes all four of `eax`/`ebx`/`ecx`/`edx`, so a single
;; primitive returning all of them would have to return a tuple -- a heap pair
;; chain, in a language whose kernel profile is trying to avoid exactly that --
;; or else be four primitives sharing hidden state between calls. Splitting it
;; keeps each one a PURE FUNCTION OF ITS TWO INPUTS, which is what makes it
;; safe to admit individually and safe to verify by arity alone. The cost is a
;; repeated `cpuid`; feature detection runs a handful of times at boot, so it
;; is not a cost that matters.
;;
;; Privileged, and never oracled, for the strongest form of the reason the MSR
;; read is: a `cpuid` result is a property of the MACHINE, not of the program.
;; A compile-time answer would not merely be an invention, it would be an
;; invention that the kernel then branches on -- "this CPU has NX" decided by a
;; compiler that has never seen the CPU.
(def kernel-privileged-operations
  '{kernel-boot-info 0 kernel-read-cr2 0 kernel-read-cr3 0 kernel-write-cr3 1 kernel-invlpg 1
    kernel-cli 0 kernel-sti 0 kernel-hlt 0 kernel-pause 0
    kernel-out-u8 2 kernel-out-u32 2
    kernel-in-u8 1 kernel-in-u32 1
    kernel-read-msr 1 kernel-write-msr 2
    kernel-cpuid-eax 2 kernel-cpuid-ebx 2 kernel-cpuid-ecx 2 kernel-cpuid-edx 2})
(def list-operations '#{list cons first second rest empty?})
(def predicate-operations '#{not zero? pos? neg?})
;; ADR-2607150000: and/or/when mirror kotoba-lang/kotoba's already-proven
;; desugar-and/desugar-or (runtime.clj) -- ported here rather than reinvented,
;; closing the divergence ADR-2607141600/2607150000 identified between the
;; two independently-evolved grammars. Keyword literals are now owned typed
;; values and are never reduced to probabilistic i64 hashes. The legacy
;; untagged pair-map lowering therefore fails closed when it encounters a
;; keyword key until the bounded typed-map ABI is implemented.
(def logical-operations '#{and or when})
(def map-operations '#{get assoc})
(def typed-map-operations '#{map-new map-get map-assoc})
(def typed-safe-value-operations
  '{bool-not 1 option-some 1 option-none 0 option-some? 1 option-value 2
    result-ok 1 result-err 1 result-ok? 1 result-value 2 result-error 2})
(def parametric-result-operations
  '{result-ok-of 2 result-err-of 2 result-ok?-of 2 result-value-of 3 result-error-of 3
    result-match-of 6})
(def variant-operations '#{variant-new variant-match})
(def generic-option-operations
  '#{option-some-of option-none-of option-some?-of option-value-of option-match})
(def canonical-list-operations '#{typed-list-new})
(def bytes-operations '{bytes-empty 0})
(def heterogeneous-vector-operations
  '#{hetero-vector-new hetero-vector-count hetero-vector-at
     hetero-vector-assoc hetero-vector-equal})
(def typed-set-operations
  '#{typed-set-new typed-set-count typed-set-contains typed-set-conj
     typed-set-disj typed-set-equal typed-set-nth})
(def canonical-typed-map-operations
  '#{typed-map-new typed-map-count typed-map-contains typed-map-get
     typed-map-entry-at typed-map-assoc typed-map-dissoc typed-map-equal})
(def record-operations '#{record-new record-get record-assoc record-equal})
(def typed-vector-operations
  '{vector-count 1 vector-get 3 vector-at 2 vector-drop 2 vector-assoc 3 vector-conj 2})
(def ^:private contextual-string-argument-indexes
  "Builtin argument positions whose declared type selects the closed string
  closure dispatcher. This is elaboration context, not dynamic overloading."
  '{string-byte-length #{0}
    string=? #{0 1}
    string-concat #{0 1}
    string-substring #{0}
    string-replace-all #{0 1 2}
    string-contains? #{0 1}
    string-split-count #{0 1}
    string-fold-case #{0}
    string-code-point-at #{0}
    keyword-from-string #{0}
    symbol #{0}
    string-index-contains #{1}
    string-index-get #{1}
    string-index-assoc #{1}
    document-string #{0}
    document-read #{0}
    document-edn-read #{0}
    xml-path-count #{0 1}
    xml-name-count #{0 1}
    xml-name-text #{0 1}
    xml-path-text #{0 1}
    xml-path-attr #{0 1 3}
    decimal-f64-parse #{0}
    decimal-f64x3-parse #{0}})
(def ^:private contextual-document-argument-indexes
  "Builtin argument positions whose declared type selects the closed document
  closure dispatcher. Ambiguous map keys remain uncontextualized."
  '{document-count #{0}
    document-kind #{0}
    document-sha256 #{0}
    document-print #{0}
    document-edn-print #{0}
    document-vector-at #{0}
    document-list-at #{0}
    document-map-entry-at #{0}
    document-vector-assoc #{0 2}
    document-vector-conj #{0 1}
    document-vector-drop #{0}
    document-vector-remove #{0}
    document-equal? #{0 1}
    document-set-contains? #{0 1}
    document-contains #{0}
    document-get #{0}
    document-assoc #{0 2}
    document-dissoc #{0}
    document-merge #{0 1}
    document-string-value #{0}
    document-keyword-value #{0}
    document-symbol-value #{0}
    document-bool-value #{0}
    document-i64-value #{0}
    document-f64-value #{0}})
(def ^:private contextual-f64-argument-indexes
  "Builtin positions whose operands are f64 values. Conversion constructors
  whose input is i64 are deliberately absent."
  '{f64-to-bits #{0}
    f64-to-i64-checked #{0} f64-to-i64-truncating #{0}
    f64-add #{0 1} f64-sub #{0 1} f64-mul #{0 1} f64-div #{0 1}
    f64-min #{0 1} f64-max #{0 1}
    f64-neg #{0} f64-abs #{0} f64-sqrt #{0}
    f64-sin-quarter-turn #{0} f64-cos-quarter-turn #{0}
    f64-sin-bounded #{0} f64-cos-bounded #{0}
    f64-exp-near-zero #{0} f64-log-near-one #{0}
    f64-atan2-bounded #{0 1} f64-exp-bounded #{0} f64-log-bounded #{0}
    f64-eq #{0 1} f64-lt #{0 1} f64-le #{0 1}
    f64-gt #{0 1} f64-ge #{0 1} f64-unordered #{0 1}
    f64-to-f32-rounded #{0}})
(def ^:private contextual-f32-argument-indexes
  "Builtin positions whose operands are f32 values."
  '{f32-to-bits #{0} f32-to-f64-exact #{0}
    f32-to-i64-checked #{0} f32-to-i64-truncating #{0}
    f32-add #{0 1} f32-sub #{0 1} f32-mul #{0 1} f32-div #{0 1}
    f32-min #{0 1} f32-max #{0 1}
    f32-neg #{0} f32-abs #{0} f32-sqrt #{0}
    f32-eq #{0 1} f32-lt #{0 1} f32-le #{0 1}
    f32-gt #{0 1} f32-ge #{0 1} f32-unordered #{0 1}})
(def ^:private contextual-vector-f64-argument-types
  "Typed vector operands and f64 item/fallback positions."
  '{vector-f64-count {0 :vector-f64}
    vector-f64-get {0 :vector-f64 2 :f64}
    vector-f64-at {0 :vector-f64}
    vector-f64-drop {0 :vector-f64}
    vector-f64-assoc {0 :vector-f64 2 :f64}
    vector-f64-conj {0 :vector-f64 1 :f64}})
(def typed-f64-vector-operations
  '{vector-f64-count 1 vector-f64-get 3 vector-f64-at 2 vector-f64-drop 2
    vector-f64-assoc 3 vector-f64-conj 2})
(def compact-graph-operations
  '{string-index-new 0 string-index-count 1 string-index-contains 2
    string-index-get 2 string-index-assoc 3
    disjoint-set-i64-new 1 disjoint-set-i64-count 1 disjoint-set-i64-union 3})
(def document-fixed-operations
  '{document-null 0 document-bool 1 document-i64 1 document-f64 1
    document-string 1 document-keyword 1 document-symbol 1 document-count 1 document-kind 1 document-sha256 1 document-print 1 document-read 1
    document-edn-print 1 document-edn-read 1
    document-vector-at 2 document-list-at 2 document-map-entry-at 2 document-vector-assoc 3 document-vector-conj 2
    document-vector-drop 2 document-vector-remove 2
    document-equal? 2 document-set-contains? 2 document-contains 2 document-get 2 document-assoc 3 document-dissoc 2
    document-merge 2 document-string-value 1 document-keyword-value 1 document-symbol-value 1 document-bool-value 1
    document-i64-value 1 document-f64-value 1})
(def document-variadic-operations '#{document-vector document-list document-set document-map})
(def sequencing-operations '#{do})
(def lazy-sequence-operations
  '#{lazy-cons lazy-first lazy-rest lazy-empty? lazy-map lazy-filter take drop})
(def string-operations '{string-byte-length 1 string-length 1 string-from-i64 1
                         bytes-task-byte-count 1 task-ready? 1
                         object-cas-won 1
                         bytes-response-byte-count 1 bool-result 1
                         http-response-status 1 log-read-byte-count 1
                         string=? 2 string-concat 2 string-substring 3
                         string-replace-all 3 string-contains? 2 string-split-count 2
                         string-fold-case 1
                         string-code-point-at 2
                         keyword-from-string 1 keyword-name 1 symbol 1})
(def xml-operations
  '{xml-path-count 2 xml-name-count 2 xml-name-text 3 xml-path-text 3 xml-path-attr 4})
(def decimal-operations '{decimal-f64-parse 1 decimal-f64x3-parse 1})
(def f64-operations
  '{f64-to-bits 1 f64-from-bits 1
    f64-add 2 f64-sub 2 f64-mul 2 f64-div 2 f64-min 2 f64-max 2
    f64-neg 1 f64-abs 1 f64-sqrt 1
    f64-sin-quarter-turn 1 f64-cos-quarter-turn 1
    f64-sin-bounded 1 f64-cos-bounded 1
    f64-exp-near-zero 1 f64-log-near-one 1 f64-atan2-bounded 2
    f64-exp-bounded 1 f64-log-bounded 1
    f64-eq 2 f64-lt 2 f64-le 2 f64-gt 2 f64-ge 2 f64-unordered 2
    i64-to-f64-checked 1 i64-to-f64-rounded 1
    f64-to-i64-checked 1 f64-to-i64-truncating 1})

(def f32-operations
  '{f32-to-bits 1 f32-from-bits 1
    f64-to-f32-rounded 1 f32-to-f64-exact 1
    i64-to-f32-checked 1 i64-to-f32-rounded 1
    f32-to-i64-checked 1 f32-to-i64-truncating 1
    f32-add 2 f32-sub 2 f32-mul 2 f32-div 2 f32-min 2 f32-max 2
    f32-neg 1 f32-abs 1 f32-sqrt 1
    f32-eq 2 f32-lt 2 f32-le 2 f32-gt 2 f32-ge 2 f32-unordered 2})
(def reserved-function-names
  (set/union forbidden-heads arithmetic comparisons (set (keys heap-operations))
             (set (keys kgraph-operations))
             (set (keys kernel-memory-operations))
             (set (keys kernel-privileged-operations))
             list-operations predicate-operations logical-operations map-operations typed-map-operations
             (set (keys typed-safe-value-operations))
             (set (keys parametric-result-operations))
             variant-operations
             generic-option-operations
             canonical-list-operations
             (set (keys bytes-operations))
             heterogeneous-vector-operations
             typed-set-operations
             canonical-typed-map-operations
             record-operations
             (set (keys typed-vector-operations))
             (set (keys typed-f64-vector-operations))
             (set (keys compact-graph-operations))
             (set (keys document-fixed-operations)) document-variadic-operations
             (set (keys string-operations))
             (set (keys xml-operations))
             (set (keys decimal-operations))
             (set (keys f64-operations))
             (set (keys f32-operations))
             (set (keys i32-operations))
             (set (keys i64-operations))
             lazy-sequence-operations
             '#{let if cap-call typed-cap-call ns defn defn- some some? nil? option-or vector-i64 vector-f64 vector-new vector-f64-new
                hetero-vector typed-set record match-result match-variant match-option}))
(def max-functions 1024)
(def max-arity-clauses 8)
(def max-expression-nodes 50000)
(def max-lowered-nodes 100000)
(def max-bindings 4096)
(def max-parameters 5)
(def max-symbol-chars 128)
(def max-list-items 128)
(def max-namespace-docstring-chars 4096)
(def max-function-docstring-chars 4096)
(def max-type-depth 8)
(def max-type-nodes 64)
(def max-variant-cases 32)
(def max-heterogeneous-vector-items 32)
(def max-typed-set-items 32)
(def max-typed-map-entries 31)
(def max-record-fields 32)
;; ADR-2607182410: bounds an optional `ns` `:capabilities` declaration set.
;; 256, not max-functions -- matches cap-call's own [0,255] id space (at
;; most 256 distinct capabilities can ever exist), not the unrelated
;; function-count limit.
(def max-namespace-capabilities 256)
(def value-types #{:i64 :f32 :f64 :string :keyword :symbol :map :bool :bytes
                   :option-i64 :result-i64
                   :vector-i64 :vector-f64 :string-index :disjoint-set-i64 :document})

(declare reject! closure-result-type?)

(defn- callable-type? [type]
  (and (vector? type) (= :fn (first type)) (<= 2 (count type) 6)))

(defn- callable-clauses [type]
  (when (callable-type? type) (subvec type 1)))

(defn- parametric-result-type? [type]
  (and (vector? type) (= 3 (count type)) (= :result (first type))))

(defn- variant-type? [type]
  (and (vector? type) (= 3 (count type)) (= :variant (first type))))

(defn- generic-option-type? [type]
  (and (vector? type) (= 2 (count type)) (= :option (first type))))

(defn- canonical-list-type? [type]
  (and (vector? type) (= 2 (count type)) (= :list (first type))))

(defn- stream-type? [type]
  (and (vector? type) (= 2 (count type)) (= :stream (first type))))

(defn- task-type? [type]
  (and (vector? type) (= 2 (count type)) (= :task (first type))))

(defn- linear-resource-type? [type]
  (or (stream-type? type) (task-type? type)))

(defn- heterogeneous-vector-type? [type]
  (and (vector? type) (= 2 (count type)) (= :vector (first type))))

(defn- typed-set-type? [type]
  (and (vector? type) (= 2 (count type)) (= :set (first type))))

(defn- canonical-typed-map-type? [type]
  (and (vector? type) (= 3 (count type)) (= :map (first type))))

(defn- record-type? [type]
  (and (vector? type) (= 3 (count type)) (= :record (first type))))

(defn- schema-ref-type? [type]
  (and (vector? type) (= 2 (count type)) (= :ref (first type))
       (keyword? (second type)) (namespace (second type))))

(defn- structured-type? [type]
  (or (parametric-result-type? type) (variant-type? type) (generic-option-type? type)
      (canonical-list-type? type)
      (stream-type? type) (task-type? type)
      (heterogeneous-vector-type? type) (typed-set-type? type)
      (canonical-typed-map-type? type) (record-type? type) (schema-ref-type? type)
      (callable-type? type)))

(defn- validate-value-type!
  ([type] (validate-value-type! type 0 (volatile! 0)))
  ([type depth nodes]
   (vswap! nodes inc)
   (when (> @nodes max-type-nodes)
     (reject! "value type exceeds node limit" type :kotoba.error/value-type-node-limit))
   (when (> depth max-type-depth)
     (reject! "value type exceeds depth limit" type :kotoba.error/value-type-depth-limit))
   (cond
     (callable-type? type)
     (let [clauses (callable-clauses type)
           arities (mapv (comp count first) clauses)]
       (when-not (and (seq clauses)
                      (every? #(and (vector? %) (= 2 (count %))
                                    (vector? (first %))
                                    (<= (count (first %)) 4))
                              clauses)
                      (= (count arities) (count (distinct arities))))
         (reject! "callable type requires one to five unique [parameter-types result-type] clauses"
                  type :kotoba.error/callable-type))
       (doseq [[parameter-types result-type] clauses]
         (when-not (every? #{:i64} parameter-types)
           (reject! "callable parameter types currently require the i64 closure ABI"
                    type :kotoba.error/callable-parameter-type))
         (when (or (callable-type? result-type) (linear-resource-type? result-type))
           (reject! "callable results cannot be callable or linear resources"
                    type :kotoba.error/callable-result-type))
         (validate-value-type! result-type (inc depth) nodes)
         (when-not (closure-result-type? result-type {})
           (reject! "callable result type is outside the admitted dispatcher profile"
                    type :kotoba.error/callable-result-type)))
       type)
     (contains? value-types type)
     type
     (schema-ref-type? type)
     type
     (parametric-result-type? type)
     (do (validate-value-type! (second type) (inc depth) nodes)
         (validate-value-type! (nth type 2) (inc depth) nodes)
         type)
     (generic-option-type? type)
     (do (validate-value-type! (second type) (inc depth) nodes)
         type)
     (canonical-list-type? type)
     (do (validate-value-type! (second type) (inc depth) nodes)
         type)
     (stream-type? type)
     (do (when-not (= :bytes (second type))
           (reject! "stream payload must be bytes" type))
         (validate-value-type! (second type) (inc depth) nodes)
         type)
     (task-type? type)
     (do (when-not (stream-type? (second type))
           (reject! "task payload must be a stream resource" type))
         (validate-value-type! (second type) (inc depth) nodes)
         type)
     (heterogeneous-vector-type? type)
     (let [item-types (second type)]
       (when-not (and (vector? item-types)
                      (<= (count item-types) max-heterogeneous-vector-items))
         (reject! "heterogeneous vector types must be a bounded vector" type :kotoba.error/hetero-vector-type))
       (vswap! nodes inc)
       (when (> @nodes max-type-nodes)
         (reject! "value type exceeds node limit" type :kotoba.error/value-type-node-limit))
       (doseq [item-type item-types]
         (validate-value-type! item-type (inc depth) nodes))
       type)
     (typed-set-type? type)
     (do (when (contains? #{:f32 :f64} (second type))
           (reject! "direct floating set items are outside the structured scalar ABI" type :kotoba.error/floating-set-item))
         (validate-value-type! (second type) (inc depth) nodes)
         type)
     (canonical-typed-map-type? type)
     (do (when (some #{:f32 :f64} [(second type) (nth type 2)])
           (reject! "direct floating map keys or values are outside the structured scalar ABI" type :kotoba.error/floating-map-kv))
         (validate-value-type! (second type) (inc depth) nodes)
         (validate-value-type! (nth type 2) (inc depth) nodes)
         type)
     (record-type? type)
     (let [[_ type-id fields] type]
       (when-not (and (keyword? type-id) (namespace type-id))
         (reject! "record type id must be a qualified keyword" type :kotoba.error/record-type-id))
       (when-not (and (vector? fields) (seq fields) (<= (count fields) max-record-fields)
                      (every? #(and (vector? %) (= 2 (count %)) (keyword? (first %))) fields)
                      (= (count fields) (count (distinct (map first fields)))))
         (reject! "record fields must be a non-empty unique bounded vector" type :kotoba.error/record-fields))
       (vswap! nodes + (+ 2 (* 2 (count fields))))
       (when (> @nodes max-type-nodes)
         (reject! "value type exceeds node limit" type :kotoba.error/value-type-node-limit))
       (doseq [[_ field-type] fields]
         (validate-value-type! field-type (inc depth) nodes))
       type)
     (variant-type? type)
     (let [[_ type-id cases] type]
       (when-not (and (keyword? type-id) (namespace type-id))
         (reject! "variant type id must be a qualified keyword" type :kotoba.error/variant-type-id))
       (when-not (and (vector? cases) (seq cases) (<= (count cases) max-variant-cases)
                      (every? #(and (vector? %) (= 2 (count %)) (keyword? (first %))) cases)
                      (= (count cases) (count (distinct (map first cases)))))
         (reject! "variant cases must be a non-empty unique bounded vector" type :kotoba.error/variant-cases))
       (vswap! nodes + (+ 2 (* 2 (count cases))))
       (when (> @nodes max-type-nodes)
         (reject! "value type exceeds node limit" type :kotoba.error/value-type-node-limit))
       (doseq [[_ payload-type] cases]
         (validate-value-type! payload-type (inc depth) nodes))
       type)
     :else (reject! "value type is outside the safe profile" type :kotoba.error/value-type-outside-profile))))

(defn- kotoba-integer?
  "True for a value that is (or stands for) a `.kotoba` integer literal --
  plain `integer?` on `:clj`. On `:cljs` a literal may be EITHER a JS
  `bigint` (read from `.kotoba` source via `kotoba.compiler.kotoba-reader`)
  OR a plain cljs number (synthesized directly by this namespace's own
  desugaring, e.g. `desugar-and`'s vacuous `1`, `when`'s trailing `0`, `get`'s
  default `0` -- ordinary Clojure literals in THIS file's source, never
  routed through the reader) -- both are valid until
  `kotoba.kir/eval-expr` coerces every literal to `bigint` via
  `cljs-i64/->bigint` at the single point it enters the runtime value
  stream. Plain cljs `integer?`/`int?` do not recognize `bigint`
  (confirmed live), so this checks both forms explicitly."
  [form]
  #?(:clj (integer? form) :cljs (or (i64/bigint-value? form) (integer? form))))

(defn- heterogeneous-vector-index!
  [index item-types form]
  (when-not (kotoba-integer? index)
    (reject! "heterogeneous vector index must be an integer literal" form :kotoba.error/hetero-vector-index))
  (let [host-index #?(:clj index
                      :cljs (if (i64/bigint-value? index) (js/Number index) index))]
    (when-not (and (integer? host-index) (<= 0 host-index)
                   (< host-index (count item-types)))
      (reject! "heterogeneous vector index must be in range" form :kotoba.error/hetero-vector-index-range))
    #?(:clj (long host-index) :cljs host-index)))

(defn- heterogeneous-vector-slice-index!
  "Return a host index for a compile-time heterogeneous-vector slice. Unlike
  an element index, the vector length itself is valid and denotes an empty
  suffix. Keeping this literal-only makes the resulting descriptor exact."
  [index item-types form]
  (when-not (kotoba-integer? index)
    (reject! "heterogeneous vector drop count must be an integer literal"
             form :kotoba.error/hetero-vector-slice-index))
  (let [host-index #?(:clj index
                      :cljs (if (i64/bigint-value? index) (js/Number index) index))]
    (when-not (and (integer? host-index) (<= 0 host-index)
                   (<= host-index (count item-types)))
      (reject! "heterogeneous vector drop count must be in range"
               form :kotoba.error/hetero-vector-slice-index-range))
    #?(:clj (long host-index) :cljs host-index)))

(defn- check-reader-depth! [source]
  (loop [index 0 depth 0 in-string? false escaped? false in-comment? false]
    (when (< index (count source))
      (let [ch (.charAt ^String source index)]
        (cond
          in-comment? (recur (inc index) depth false false (not= ch \newline))
          (and in-string? escaped?) (recur (inc index) depth true false false)
          (and in-string? (= ch \\)) (recur (inc index) depth true true false)
          (= ch \newline) (recur (inc index) depth in-string? false false)
          (= ch \;) (recur (inc index) depth in-string? false (not in-string?))
          (= ch \") (recur (inc index) depth (not in-string?) false false)
          in-string? (recur (inc index) depth true false false)
          (#{\( \[ \{} ch)
          (let [next-depth (inc depth)]
            (when (> next-depth 512)
              (throw (ex-info "reader nesting exceeds admission limit" {:phase :read})))
            (recur (inc index) next-depth false false false))
          (#{\) \] \}} ch) (recur (inc index) (max 0 (dec depth)) false false false)
          :else (recur (inc index) depth false false false))))))

(defn read-forms [source]
  (when-not (string? source)
    (throw (ex-info "source must be a string" {:phase :read})))
  (when (> (count source) (* 1024 1024))
    (throw (ex-info "source exceeds 1 MiB admission limit" {:phase :read})))
  (when (re-find #"#=" source)
    (throw (ex-info "reader evaluation is forbidden" {:phase :read})))
  (check-reader-depth! source)
  #?(:clj
     (let [r (rt/indexing-push-back-reader source)]
       (loop [out []]
         (when (> (count out) 10000)
           (throw (ex-info "too many top-level forms" {:phase :read})))
         (let [x (try
                   (reader/read {:read-cond :allow :features #{:kotoba} :eof ::eof} r)
                   (catch Exception error
                     (throw (ex-info "source reader rejected input"
                                     {:phase :read} error))))]
           (if (= x ::eof) out (recur (conj out x))))))
     ;; kotoba-reader (kr) is a purpose-built substitute for the JVM-only
     ;; clojure.tools.reader -- see its own ns docstring for why
     ;; cljs.tools.reader (the nominal ClojureScript sibling) isn't used
     ;; instead. It parses the whole source in one pass rather than one form
     ;; at a time, so the >10000 admission check runs post-hoc here instead
     ;; of per-iteration -- equivalent outcome, same 1 MiB source cap already
     ;; bounds how large that one pass can be.
     :cljs
     (let [out (try
                 (kr/read-forms source)
                 (catch :default error
                   (throw (ex-info "source reader rejected input"
                                   {:phase :read} error))))]
       (when (> (count out) 10000)
         (throw (ex-info "too many top-level forms" {:phase :read})))
       out)))

(defn- form-span [form]
  (let [{:keys [line column end-line end-column offset end-offset]} (meta form)]
    (when (and (integer? line) (integer? column))
      (cond-> {:line line :column column}
        (integer? end-line) (assoc :end-line end-line)
        (integer? end-column) (assoc :end-column end-column)
        (integer? offset) (assoc :offset offset)
        (integer? end-offset) (assoc :end-offset end-offset)))))

(defn- reject!
  "Reject a source form. Always attaches `:phase :subset`, a source `:span`
  when available, and a stable `:kotoba.error/code` (T3.1).

  Prefer an explicit specific code via the 3-arity. The 2-arity defaults to
  `:kotoba.error/subset-reject` so no reject site is code-less."
  ([message form]
   (reject! message form :kotoba.error/subset-reject))
  ([message form code]
   (let [m (meta form)
         span (or (when (map? form) (:span form))
                  (get m :span)
                  (form-span form))
         operation (or (get m :source-operation)
                       (when (and (seq? form) (symbol? (first form)) (namespace (first form)))
                         (keyword (namespace (first form)) (name (first form)))))
         code (or code :kotoba.error/subset-reject)]
     (throw (ex-info message
                     (cond-> {:phase :subset :form form :kotoba.error/code code}
                       span (assoc :span span)
                       operation (assoc :operation operation)))))))

(def pure-product-disallowed-heads
  "Control / ambient heads rejected under `:language-profile :pure-product`
  even when the general subset might admit them (see pure-product-profile.edn)."
  '#{cap-call doseq dotimes defmulti defmethod
     future pmap agent send send-off
     condp cond-> cond->> some-> some->> as-> -> ->>})

(defn- pure-product-form-head [form]
  (when (and (seq? form) (symbol? (first form)))
    (first form)))

(defn- check-pure-product-source-forms!
  "T2.1: writeable pure-product source must not declare capabilities or use
  disallowed sugar / cap-call. Empty effects are checked after analyze."
  [forms]
  (doseq [form forms]
    (when (and (seq? form) (= 'ns (first form)))
      (doseq [clause (drop 2 form)]
        (when (and (seq? clause) (= :capabilities (first clause)))
          (reject! "pure-product profile rejects :capabilities (guest must be effect-free)"
                   form
                   :kotoba.error/pure-product-capabilities))))
    (doseq [node (tree-seq
                   (fn [x]
                     (or (sequential? x)
                         (map? x)
                         (set? x)))
                   (fn [x]
                     (cond
                       (map? x) (concat (keys x) (vals x))
                       (set? x) (seq x)
                       :else (seq x)))
                   form)]
      (when-let [head (pure-product-form-head node)]
        (when (or (contains? forbidden-heads head)
                  (contains? pure-product-disallowed-heads head))
          (reject! (str "form outside pure-product profile: " head)
                   node
                   :kotoba.error/pure-product-forbidden))))))

(declare valid-name?)

(defn- namespace-parts
  "Parse the bounded namespace header. `:export` and `:capabilities`
  (ADR-2607182410) are the only admitted clauses, each at most once (in
  either order): `:export` grants host visibility but no ambient authority
  or module loading; `:capabilities` optionally declares the closed set of
  named capabilities (see capability-registry) the namespace's `cap-call`
  forms may use -- `analyze`'s `check-namespace-capabilities!` then requires
  this declared set to exactly match what's actually used (declare-then-
  check, mirroring the `:aiueos/imports` pattern). Import/require clauses
  remain fail-closed."
  [form]
  (let [[op namespace-symbol & tail] form]
    (when-not (and (= 'ns op) (symbol? namespace-symbol)
                   (nil? (namespace namespace-symbol))
                   (pos? (count (str namespace-symbol)))
                   (<= (count (str namespace-symbol)) max-symbol-chars))
      (reject! "invalid bounded namespace symbol" form :kotoba.error/namespace-symbol))
    (let [[docstring tail] (if (string? (first tail))
                             [(first tail) (rest tail)] [nil tail])]
      (when (and docstring (> (count docstring) max-namespace-docstring-chars))
        (reject! "namespace docstring exceeds admission limit" docstring :kotoba.error/namespace-docstring-limit))
      (when (> (count tail) 3)
        (reject! "namespace admits at most :export, :capabilities, and :schemas clauses" form :kotoba.error/namespace-clause-count))
      ;; ADR-2607182410: `:export`'s original (pre-existing, test-asserted)
      ;; rejection message is preserved VERBATIM for every clause shape it
      ;; already covered pre-`:capabilities` -- a non-`seq?` clause, an
      ;; unrecognized clause head, or a malformed `(:export ...)` -- so
      ;; existing callers/tests asserting on that exact string are
      ;; unaffected. Only a recognized-but-malformed `(:capabilities ...)`
      ;; clause gets the new, `:capabilities`-specific message (a shape no
      ;; pre-existing source could ever have produced).
      (doseq [clause tail]
        (when-not (seq? clause)
          (reject! "only a bounded :export vector is admitted in namespace clauses" clause :kotoba.error/namespace-export-clause))
        (case (first clause)
          :export (when-not (and (= 2 (count clause)) (vector? (second clause)))
                    (reject! "only a bounded :export vector is admitted in namespace clauses" clause :kotoba.error/namespace-export-clause))
          :capabilities (when-not (and (= 2 (count clause)) (set? (second clause)))
                          (reject! "only a bounded :capabilities set is admitted in namespace clauses" clause :kotoba.error/namespace-capabilities-clause))
          :schemas (when-not (and (= 2 (count clause)) (map? (second clause)))
                     (reject! "only a closed :schemas map is admitted in namespace clauses" clause :kotoba.error/namespace-schemas-clause))
          (reject! "only a bounded :export vector is admitted in namespace clauses" clause :kotoba.error/namespace-export-clause)))
      (when (not= (count tail) (count (distinct (map first tail))))
        (reject! "namespace admits each clause at most once" form :kotoba.error/namespace-clause-duplicate))
      (let [export-clause (first (filter #(= :export (first %)) tail))
            capabilities-clause (first (filter #(= :capabilities (first %)) tail))
            schemas-clause (first (filter #(= :schemas (first %)) tail))
            exports (when export-clause (vec (second export-clause)))
            capabilities (when capabilities-clause (set (second capabilities-clause)))
            ;; Defrecord descriptors are collected by the declaration expansion
            ;; that precedes this parse. Keep the authored table raw here so
            ;; analyze can merge those same-module nominal schemas before the
            ;; closed graph is validated once. Shape checks above still run
            ;; immediately; no unvalidated table reaches expression analysis.
            schemas (when schemas-clause (second schemas-clause))]
        (when (and exports
                   (or (> (count exports) max-functions)
                       (not= (count exports) (count (distinct exports)))
                       (not-every? valid-name? exports)))
          (reject! "namespace exports must be unique bounded function names" exports :kotoba.error/namespace-exports))
        (when (and capabilities
                   (or (> (count capabilities) max-namespace-capabilities)
                       (not-every? #(and (keyword? %) (namespace %)) capabilities)))
          (reject! "namespace :capabilities must be a bounded set of namespaced keywords" capabilities :kotoba.error/namespace-capabilities-shape))
        {:namespace namespace-symbol :exports exports :capabilities capabilities
         :schemas schemas
         ;; Populated from the once-validated merged graph in analyze.
         :schema-identities nil}))))

(declare desugar-expr desugar-result-expr desugar-bool-expr desugar-do desugar-list thread-form form-free-symbols
         nth-pair-second replace-recur valid-name?)

;; Closed namespace schema table used by descriptor-aware source elaboration.
;; It must be defined before closure dispatch helpers so their one-argument
;; canonicalization path observes the active per-function binding.
(def ^:dynamic *schemas* nil)

;; ADR-2607150000: bound (via `binding`) around each top-level defn's
;; desugaring pass in `analyze`, to an atom `loop`'s desugar-expr case
;; conjoins synthesized helper-function definitions onto -- the same
;; "collect synthesized functions on the side, inject them into `parsed`
;; afterward" pattern `map-get-helper`/`uses-map-get?` already established,
;; generalized to support MULTIPLE, uniquely-named helpers per defn (one
;; per `loop` occurrence) rather than one fixed shared name.
(def ^:dynamic *pending-loop-helpers* nil)

;; Optional override for synthesized loop-helper return type (default :i64).
;; T4.5 map/filter bind this to :vector-i64 so the accumulator can exit as a vector.
(def ^:dynamic *loop-result-type* :i64)

;; A synthesized loop-helper carries no param-type annotations (its captured
;; outer variables have types only knowable at its call site). During the
;; param-type resolution pass (resolve-loop-helper-param-types) these two are
;; bound so that infer-call-type, on reaching a still-unresolved loop-helper
;; call, RECORDS the argument types instead of type-checking the arguments
;; against the (placeholder) declared param-types. Both nil in the normal
;; check-value-types! pass, so ordinary type-checking is unchanged.
(def ^:dynamic *loop-helper-names* nil)
(def ^:dynamic *loop-helper-recorder* nil)

;; ADR-2607150000: loop-helper names are NOT `gensym` -- unlike and/or's
;; gensym'd `let`-local temp names (erased into numeric WASM local indices,
;; never appearing in the compiled bytes -- confirmed by repeated-compile
;; byte comparison), a loop-helper becomes a real EXPORTED top-level
;; function ("every function is exported by current backends," see
;; analyze's :effects comment below), so its NAME is literally baked into
;; the WASM export section. `gensym` uses a JVM-process-wide monotonic
;; counter, so two compiles of the IDENTICAL source in the same process
;; would get DIFFERENT loop-helper names and therefore DIFFERENT bytes --
;; confirmed empirically (compiled the same loop-using source twice in one
;; process: bytes differed). This compiler's own reproducible-build gates
;; (coverage_evidence.clj/release.clj) require byte-for-byte determinism,
;; so loop-helpers instead get a sequential name from *loop-counter*,
;; bound ONCE per `analyze` call (not per-defn) so the same source always
;; encounters `loop` forms in the same left-to-right desugaring order and
;; always assigns the same names.
(def ^:dynamic *loop-counter* nil)
(def ^:dynamic *function-arities* {})
(def ^:dynamic *lambda-counter* nil)
(def ^:dynamic *pending-lambdas* nil)
(def ^:dynamic *uses-apply?* nil)
(def ^:dynamic *uses-lazy?* nil)
(def ^:dynamic *lifting-lazy-thunk?* false)
(def ^:dynamic *lexical-bindings* #{})
(def ^:dynamic *lexical-callable-contracts* {})
(def ^:dynamic *function-callable-result-contracts* {})
(def ^:dynamic *expected-callable-contract* nil)
(def ^:dynamic *contextual-closure-result-type* nil)
(def ^:dynamic *required-closure-dispatchers* nil)

(def ^:private closure-flat-result-types
  #{:i64 :bool :f32 :f64 :string :bytes :vector-i64 :vector-f64 :document})

(defn- canonical-closure-result-type
  "Resolve a top-level schema reference before it becomes dispatcher identity.
  Nested references remain closed schema edges and are not recursively expanded."
  ([type] (canonical-closure-result-type type *schemas*))
  ([type schemas]
   (if (and (schema-ref-type? type) (map? schemas))
     (or (get schemas (second type)) type)
     type)))

(defn- closure-default-value-expr
  "Return a bounded inhabitant for a dispatcher result type, or nil when the
  descriptor cannot yet be represented by the closed trap synthesizer."
  [type]
  (cond
    (= :i64 type) 0
    (= :bool type) false
    (= :string type) ""
    (= :bytes type) '(bytes-empty)
    (= :keyword type) :kotoba.closure/trap
    (= :symbol type) '(symbol "")
    (= :f64 type) '(f64-from-bits 0)
    (= :f32 type) '(f32-from-bits 0)
    (= :vector-i64 type) '(vector-new)
    (= :vector-f64 type) '(vector-f64-new)
    (= :document type) '(document-null)
    (= :map type) '(map-new)
    (= :option-i64 type) '(option-none)
    (= :result-i64 type) '(result-ok 0)
    (= :string-index type) '(string-index-new)
    (= :disjoint-set-i64 type) '(disjoint-set-i64-new 0)

    (generic-option-type? type)
    (list 'option-none-of type)

    (canonical-list-type? type)
    (list 'typed-list-new type)

    (parametric-result-type? type)
    (if-let [ok-value (closure-default-value-expr (second type))]
      (list 'result-ok-of type ok-value)
      (when-let [error-value (closure-default-value-expr (nth type 2))]
        (list 'result-err-of type error-value)))

    (heterogeneous-vector-type? type)
    (let [values (mapv closure-default-value-expr (second type))]
      (when (every? some? values)
        (apply list 'hetero-vector-new type values)))

    (typed-set-type? type)
    (list 'typed-set-new type)

    (canonical-typed-map-type? type)
    (list 'typed-map-new type)

    (variant-type? type)
    (some (fn [[tag payload-type]]
            (when-let [payload (closure-default-value-expr payload-type)]
              (list 'variant-new type tag payload)))
          (nth type 2))

    (record-type? type)
    (let [values (mapv (comp closure-default-value-expr second) (nth type 2))]
      (when (every? some? values)
        (apply list 'record-new type values)))

    :else nil))

(defn- closure-result-type?
  ([type] (closure-result-type? type *schemas*))
  ([type schemas]
   (let [type (canonical-closure-result-type type schemas)
         valid? (try
                  (validate-value-type! type)
                  true
                  (catch #?(:clj Exception :cljs :default) _ false))]
     (and valid?
          (or (contains? closure-flat-result-types type)
              (and (or (record-type? type)
                       (generic-option-type? type)
                       (parametric-result-type? type)
                       (variant-type? type)
                       (canonical-list-type? type)
                       (heterogeneous-vector-type? type)
                       (typed-set-type? type)
                       (canonical-typed-map-type? type))
                   (some? (closure-default-value-expr type))))))))

(defn- dispatcher-result-label [result-type]
  (if (keyword? result-type)
    (name result-type)
    (str "t_" (artifact/sha256 result-type))))

(defn- invoke-dispatcher-name
  ([arity] (invoke-dispatcher-name :i64 arity))
  ([result-type arity]
   (when-not (closure-result-type? result-type {})
     (reject! "closure result type is outside the admitted dispatcher profile"
              result-type))
   (symbol (str "__kotoba_invoke"
                (when-not (= :i64 result-type)
                  (str "_" (dispatcher-result-label result-type)))
                "$arity" arity))))

(defn- request-invoke-dispatcher [result-type arity]
  (when *required-closure-dispatchers*
    (vswap! *required-closure-dispatchers* conj [result-type arity]))
  (invoke-dispatcher-name result-type arity))

(def ^:private non-shadowable-special-heads '#{let if do fn loop recur})

(defn- lexical-call-form? [form]
  (and (seq? form)
       (symbol? (first form))
       (contains? *lexical-bindings* (first form))
       (not (contains? non-shadowable-special-heads (first form)))))

(defn- callable-clause-for-arity [contract arity form]
  (or (some #(when (= arity (count (first %))) %) (callable-clauses contract))
      (reject! "callable contract does not admit this arity"
               form :kotoba.error/callable-arity)))

(defn- expression-callable-contract [form]
  (cond
    (symbol? form) (get *lexical-callable-contracts* form)
    (seq? form) (or (get *function-callable-result-contracts*
                         [(first form) (dec (count form))])
                    (get *function-callable-result-contracts* (first form)))
    :else nil))

(defn- desugar-lexical-call [result-type form]
  (let [[closure & args] form]
    (when (> (count args) 4)
      (reject! "direct closure call exceeds ABI arity four" form))
    (let [contract (get *lexical-callable-contracts* closure)
          [parameter-types contract-result]
          (when contract (callable-clause-for-arity contract (count args) form))
          result-type (or contract-result result-type)]
      (when parameter-types
        (doseq [[argument wanted] (map vector args parameter-types)]
          ;; The admitted callable ABI is i64-only today. This explicit check
          ;; keeps the contract useful if more physical argument types are
          ;; introduced later without silently widening old descriptors.
          (when-not (= :i64 wanted)
            (reject! "callable argument type is outside the admitted closure ABI"
                     argument :kotoba.error/callable-argument-type))))
      (apply list (request-invoke-dispatcher result-type (count args)) closure
             (map desugar-expr args)))))

(defn- desugar-result-expr
  "Desugar an expression in a context with a known closure result family.
  The expectation follows value-producing tail positions, while ordinary
  operands are desugared without inheriting it."
  [result-type form]
  (let [result-type (canonical-closure-result-type result-type)]
    (when-not (closure-result-type? result-type {})
      (reject! "closure result type is outside the admitted dispatcher profile"
               result-type))
    (binding [*contextual-closure-result-type* result-type]
      (desugar-expr form))))

(defn- desugar-bool-expr [form]
  (desugar-result-expr :bool form))

(defn- desugar-expected-value [result-type form]
  (let [result-type (canonical-closure-result-type result-type)]
    (if (closure-result-type? result-type {})
      (desugar-result-expr result-type form)
      (desugar-expr form))))

(defn- desugar-tail-expressions [result-type forms]
  (let [last-index (dec (count forms))]
    (mapv (fn [index form]
            (if (and result-type (= index last-index))
              (desugar-result-expr result-type form)
              (desugar-expr form)))
          (range (count forms)) forms)))

(defn- closed-vector-literal-type
  "Infer only descriptors that are completely determined by a closed vector
  literal. Unknown expressions return nil and keep the established i64-vector
  path, where ordinary type checking reports any mismatch."
  [form]
  (cond
    (kotoba-integer? form) :i64
    (value/f64-value? form) :f64
    (string? form) :string
    (keyword? form) :keyword
    (boolean? form) :bool
    (vector? form)
    (let [item-types (mapv closed-vector-literal-type form)]
      (cond
        (empty? item-types) :vector-i64
        (every? #{:i64} item-types) :vector-i64
        (every? #{:f64} item-types) :vector-f64
        (every? some? item-types) [:vector item-types]
        :else nil))
    :else nil))

(defn- nth-pair-second [expr n]
  (nth (iterate (fn [value] (list 'pair-second value)) expr) n))

(defn- lift-lambda [form]
  (let [expected-result *contextual-closure-result-type*
        expected-contract *expected-callable-contract*
        [_ params-or-clause & tail] form
        raw-clauses (if (vector? params-or-clause)
                      [[params-or-clause (first tail)]]
                      (mapv (fn [clause]
                              (when-not (and (seq? clause) (vector? (first clause))
                                             (= 2 (count clause)))
                                (reject! "multi-arity fn requires ([params] body) clauses" clause))
                              [(first clause) (second clause)])
                            (cons params-or-clause tail)))
        parsed (mapv (fn [[params body :as clause]]
                       (let [amp-index (first (keep-indexed #(when (= '& %2) %1) params))]
                         (if amp-index
                           (do
                             (when-not (and (= amp-index (- (count params) 2))
                                            (<= amp-index 4)
                                            (every? valid-name? (subvec params 0 amp-index))
                                            (valid-name? (peek params)))
                               (reject! "variadic fn clause requires [fixed ... & rest]" clause))
                             {:kind :variadic :fixed (subvec params 0 amp-index)
                              :rest-name (peek params) :body body :min-arity amp-index})
                           {:kind :fixed :params params :body body :arity (count params)})))
                     raw-clauses)
        fixed (filter #(= :fixed (:kind %)) parsed)
        variadics (filter #(= :variadic (:kind %)) parsed)
        _ (when (or (> (count variadics) 1)
                    (not= (count fixed) (count (distinct (map :arity fixed)))))
            (reject! "fn requires unique fixed arities and at most one variadic clause" form))
        fixed-by-arity (into {} (map (juxt :arity identity) fixed))
        variadic (first variadics)
        arities (sort (set/union (set (keys fixed-by-arity))
                                 (if variadic (set (range (:min-arity variadic) 5)) #{})))
        contract-results
        (when expected-contract
          (into {} (map (fn [[parameter-types result-type]]
                          [(count parameter-types) result-type]))
                (callable-clauses expected-contract)))
        _ (when (and expected-contract
                     (not= (set arities) (set (keys contract-results))))
            (reject! "fn arities do not match the declared callable result contract"
                     form :kotoba.error/callable-result-arity))
        clauses (mapv (fn [arity]
                        (if-let [{:keys [params body]} (get fixed-by-arity arity)]
                          [params body]
                          (let [{:keys [fixed rest-name body]} variadic
                                extras (mapv #(symbol (str "__kotoba_lambda_rest_arg_" %))
                                             (range (- arity (count fixed))))]
                            [(into (vec fixed) extras)
                             (list 'let [rest-name (apply list 'list extras)] body)])))
                      arities)]
    (when-not (and (seq clauses)
                   (every? (fn [[params body]]
                             (and (some? body) (<= (count params) 4)
                                  (every? valid-name? params)
                                  (= (count params) (count (distinct params)))))
                           clauses)
                   (= (count clauses) (count (distinct (map (comp count first) clauses)))))
      (reject! "fn value requires unique arities with zero to four unique parameters" form))
    (when (and (vector? params-or-clause) (not= 1 (count tail)))
      (reject! "single-arity fn value requires exactly one body" form))
    (let [lowered (mapv (fn [[params body]]
                          (let [clause-result (get contract-results (count params))]
                          {:params params :contract-result clause-result
                           :body (binding [*lexical-bindings*
                                           (into *lexical-bindings* params)]
                                   (if-let [result (or clause-result expected-result)]
                                     (desugar-result-expr result body)
                                     (desugar-expr body)))}))
                        clauses)
          captures (vec (sort-by str
                                 (apply set/union #{}
                                        (map (fn [{:keys [params body]}]
                                               (form-free-symbols body (set params)))
                                             lowered))))
          id (vswap! *lambda-counter* inc)]
      (doseq [{:keys [params]} lowered]
        (when (> (+ (count captures) (count params)) max-parameters)
          (reject! "fn captures plus parameters exceed ABI-supported arity" form)))
      (when *pending-lambdas*
        (swap! *pending-lambdas* into
               (mapv (fn [{:keys [params body contract-result]}]
                       (let [arity (count params)
                             helper-name (symbol (str "__kotoba_lambda_" id "_arity" arity))]
                         (cond-> {:id id :arity arity :captures captures
                          :helper {:name helper-name :params (into captures params)
                                   :result :i64 :result-inferred? true
                                   :effects #{} :body body
                                   :lazy-thunk? *lifting-lazy-thunk?*}}
                           contract-result (assoc :contract-result contract-result))))
                     lowered)))
      ;; Closure captures are always the internal i64 pair-chain ABI, even
      ;; when the lambda's result is a canonical `[:list T]` value.
      (list 'pair id
            (binding [*contextual-closure-result-type* nil]
              (desugar-list captures form))))))

(defn- lambda-dispatchers [lambda-infos required-dispatchers]
  (let [requested (into #{}
                        (mapcat (fn [{:keys [arity helper]}]
                                  [[:i64 arity] [(:result helper) arity]]))
                        lambda-infos)
        requested (into requested required-dispatchers)]
    (mapv
     (fn [[result-type arity]]
       (let [closure (symbol (str "__kotoba_closure_"
                                  (dispatcher-result-label result-type) "_" arity))
             args (mapv #(symbol (str "__kotoba_invoke_arg_" %)) (range arity))
             candidates (filter #(and (= arity (:arity %))
                                      (= result-type (get-in % [:helper :result])))
                                lambda-infos)
             ;; A closure id belonging to a different result family is a
             ;; type error at the dynamic boundary.  Produce a result-typed
             ;; trap instead of silently coercing it to false/zero.
             fallback (case result-type
                        :bool '(= (quot 1 0) 0)
                        :string '(if (= (quot 1 0) 0) "" "")
                        :vector-i64 '(vector-drop (vector-new) 1)
                        :document '(if (= (quot 1 0) 0)
                                     (document-null)
                                     (document-null))
                        (if-let [default (closure-default-value-expr result-type)]
                          (list 'if '(= (quot 1 0) 0) default default)
                          '(quot 1 0)))
             body (reduce
                   (fn [fallback {:keys [id captures helper]}]
                     (let [capture-chain (list 'pair-second closure)
                           capture-values
                           (map-indexed (fn [index _]
                                          (list 'pair-first
                                                (nth-pair-second capture-chain index)))
                                        captures)]
                       (list 'if (list '= (list 'pair-first closure) id)
                             (apply list (:name helper) (concat capture-values args))
                             fallback)))
                   fallback (reverse candidates))]
         {:name (invoke-dispatcher-name result-type arity) :params (into [closure] args)
          :result result-type :effects #{} :body body}))
     (sort-by (juxt (comp dispatcher-result-label first) second) requested))))

(def ^:private closure-apply-helper
  {:name '__kotoba_closure_apply
   :params '[__kotoba_apply_closure __kotoba_apply_args]
   :i64-pair-chain-param-indexes [1]
   :result :i64 :effects #{}
   :body
   '(if (= __kotoba_apply_args 0)
      (__kotoba_invoke$arity0 __kotoba_apply_closure)
      (let [a0 (pair-first __kotoba_apply_args)
            t1 (pair-second __kotoba_apply_args)]
        (if (= t1 0)
          (__kotoba_invoke$arity1 __kotoba_apply_closure a0)
          (let [a1 (pair-first t1) t2 (pair-second t1)]
            (if (= t2 0)
              (__kotoba_invoke$arity2 __kotoba_apply_closure a0 a1)
              (let [a2 (pair-first t2) t3 (pair-second t2)]
                (if (= t3 0)
                  (__kotoba_invoke$arity3 __kotoba_apply_closure a0 a1 a2)
                  (let [a3 (pair-first t3) t4 (pair-second t3)]
                    (if (= t4 0)
                      (__kotoba_invoke$arity4 __kotoba_apply_closure a0 a1 a2 a3)
                      0)))))))))})

(def ^:private lazy-take-helper-name '__kotoba_lazy_take)
(def ^:private lazy-drop-helper-name '__kotoba_lazy_drop)

(def ^:private lazy-take-helper
  {:name lazy-take-helper-name
   :params '[__kotoba_lazy_n __kotoba_lazy_seq]
   :result :i64 :effects #{}
   :body
   '(if (<= __kotoba_lazy_n 0)
      0
      (if (= __kotoba_lazy_seq 0)
        0
        (let [__kotoba_lazy_cell (__kotoba_invoke$arity0 __kotoba_lazy_seq)]
          (if (= __kotoba_lazy_cell 0)
            0
            (pair (__kotoba_invoke$arity0 (pair-first __kotoba_lazy_cell))
                  (__kotoba_lazy_take
                   (- __kotoba_lazy_n 1)
                   (__kotoba_invoke$arity0 (pair-second __kotoba_lazy_cell))))))))})

(def ^:private lazy-drop-helper
  {:name lazy-drop-helper-name
   :params '[__kotoba_lazy_n __kotoba_lazy_seq]
   :result :i64 :effects #{}
   :body
   '(if (<= __kotoba_lazy_n 0)
      __kotoba_lazy_seq
      (if (= __kotoba_lazy_seq 0)
        0
        (let [__kotoba_lazy_cell (__kotoba_invoke$arity0 __kotoba_lazy_seq)]
          (if (= __kotoba_lazy_cell 0)
            0
            (__kotoba_lazy_drop
             (- __kotoba_lazy_n 1)
             (__kotoba_invoke$arity0 (pair-second __kotoba_lazy_cell)))))))})

;; ADR-2607182410: bound (via `binding`, once per `analyze` call, same
;; lifetime as `*loop-counter*` above -- not per-defn) to a `volatile!` set
;; that `resolve-capability-keyword!` conjoins each named capability onto as
;; `(cap-call :some/name ...)` forms are desugared. `analyze` derefs it once
;; all defns are desugared to check an optional `ns` `:capabilities`
;; declaration (declared-but-unused / used-but-undeclared) -- see
;; `check-namespace-capabilities!`. `nil` outside `analyze` (e.g. from a
;; direct unit-test call to `desugar-expr`) means "don't track," not "reject
;; every keyword": tracking is a purely additional ns-level lint, never part
;; of resolving the keyword to its id.
(def ^:dynamic *used-capability-keywords* nil)

;; Product Value ABI v1 / pure-product: local option types for if-some/when-some.
;; Bound during analyze while desugaring a typed defn body so
;; `(if-some [x opt-param] …)` can lower to option-match with the real
;; `[:option T]` instead of hardcoding `[:option :i64]` (which broke
;; `[:option :string]` and other payloads).
(def ^:dynamic *local-option-types* nil)
;; All typed params + namespace `:schemas` so
;; `(if-some [v (record-get rec :opt-field)] …)` recovers `[:option T]`
;; from the record descriptor (T5.2 option-string-in-record gap).
(def ^:dynamic *local-types* nil)

(defn- capability-wire-id [capability form]
  (if-let [id (get capability-registry capability)]
    id
    (reject! (str "cap-call names an unregistered capability: " capability)
             form)))

(defn- effect-capability-id [id]
  ;; `.kotoba` policy literals are bigint under nbb while typed Wasm metadata
  ;; indices must remain host integers for ULEB encoding.
  #?(:clj id :cljs (i64/->bigint id)))

(defn- resolve-capability-keyword!
  "Resolve a `cap-call` NAME argument (a namespaced keyword, e.g.
  `:identity/sign`) against `capability-registry` to its [0,255] int id, at
  desugar time -- strictly before HIR/KIR construction, so every downstream
  consumer (validate-expr's arity/range check, direct-facts'
  effect-extraction, ir.cljc, every backend, admission.cljc, verifier.clj)
  sees the EXACT SAME plain-integer `cap-call` shape the pre-existing
  `(cap-call <int> value)` form has always produced -- none of them are
  aware a keyword was ever written. An unregistered keyword is a hard
  parse-time rejection (closed-world/deny-by-default for names, mirroring
  the existing [0,255]-range check for the integer form)."
  [kw form]
  (let [id (capability-wire-id kw form)]
    (when *used-capability-keywords*
      (vswap! *used-capability-keywords* conj kw))
    id))

(defn- capability-keyword-for-symbol
  "Map a namespaced call head `clock/now` to registered keyword `:clock/now`."
  [op]
  (when (and (symbol? op) (namespace op))
    (let [kw (keyword (namespace op) (name op))]
      (when (contains? capability-registry kw) kw))))

(defn- attach-source-operation
  "Preserve reader span and the authored operation name on elaborated forms."
  [form elaborated source-operation]
  (let [location (select-keys (meta form)
                              [:line :column :end-line :end-column :offset :end-offset])
        span (form-span form)
        m (cond-> {:source-operation source-operation}
            (seq location) (merge location)
            span (assoc :span span)
            (meta form) (merge (meta form)))]
    (if (or (coll? elaborated) (symbol? elaborated))
      (with-meta elaborated (merge (meta elaborated) m))
      elaborated)))

(defn- elaborate-named-operation
  "W1 safety elaboration validates an ordinary namespaced operation and keeps
  it named until parameter/result types are available. The later contextual
  elaboration pass lowers it to `typed-cap-call`; authors never write numeric
  capability IDs, type envelopes, or portable-effect envelopes."
  [form op kw args]
  (when-not (= 1 (count args))
    (reject! (str "named operation " (pr-str op)
                  " requires exactly one request value")
             form))
  (let [_ (resolve-capability-keyword! kw form)
        elaborated (list op (desugar-expr (first args)))]
    (attach-source-operation form elaborated kw)))

(defn- desugar-list [args form]
  (when (> (count args) max-list-items)
    (reject! "list item count exceeds admission limit" form))
  (if (canonical-list-type? *contextual-closure-result-type*)
    (let [type *contextual-closure-result-type*
          item-type (second type)]
      (apply list 'typed-list-new type
             (map #(desugar-expected-value item-type %) args)))
    (reduce (fn [tail item] (list 'pair (desugar-expr item) tail))
            0 (reverse args))))

;; Synthesized `let` temporaries for `and` / `or` / comparison chains.
;;
;; These used to be `gensym`, which made the emitted KIR different on every
;; compile: the same source produced `and-tmp__11125` in one run and
;; `and-tmp__11129` in the next, because the counter is process-global and
;; depends on how much compiled before it. Anything that compares precompiled
;; KIR therefore could not use `and`/`or` at all -- measured in
;; kotoba-lang/murakumo, whose `infer_schedule_core.kotoba` says in a comment:
;;
;;   Nested `if` (not `and`/`or`) so the precompiled KIR is gensym-stable for
;;   the drift gate.
;;
;; That is language profile 5's headline ergonomics being unavailable in exactly
;; the code that most wants them. A deterministic name fixes it: the name is a
;; function of the chain position, so the same source always yields the same KIR.
;;
;; Capture is prevented by construction rather than by luck: the names live under
;; the reserved `__kotoba_` prefix, which `reject-reserved-binding!` now refuses
;; in any user binding or parameter position. Shadowing between nested chains is
;; harmless anyway -- a temp is read only in its own `if` test and else branch,
;; both outside any inner binding -- but relying on that alone would leave a real
;; program able to capture one by writing the name.
(defn- chain-temp [prefix depth]
  (symbol (str "__kotoba_" prefix "_" depth)))

;; Every other synthesized `let` temporary. Bound ONCE per `analyze` call, the
;; same lifetime and for the same reason as `*loop-counter*` above: the same
;; source encounters the same desugars in the same left-to-right order, so it
;; always gets the same names.
;;
;; These were `gensym`, whose counter is process-global, so the emitted KIR
;; differed on every compile. `and`/`or`/comparison chains were made
;; deterministic first (they could be named by position); these could not,
;; because a temp such as `doseq`'s cursor is still live after the body runs,
;; so a nested `doseq` naming its cursor the same thing would capture it. A
;; per-compilation counter keeps uniqueness exactly as gensym did while making
;; the sequence a function of the source.
;;
;; The consumer-side cost this removes is real: kotoba-lang/murakumo carries a
;; `normalize-kir-gensyms` that rewrites `or-tmp__N` / `binding-some__N` so its
;; drift gate can compare structure instead of counter values.
;;
;; Falls back to `gensym` when unbound, so a desugar helper called outside
;; `analyze` still produces correct (if unstable) names rather than colliding.
(def ^:dynamic *synthetic-counter* nil)

(defn- synthetic [prefix]
  (if *synthetic-counter*
    (symbol (str "__kotoba_" prefix "_" (vswap! *synthetic-counter* inc)))
    (gensym (str prefix "__"))))

(defn- reserved-binding-name? [value]
  (and (simple-symbol? value) (= "__kotoba_" (subs (str value) 0 (min 9 (count (str value)))))))

(defn- reject-reserved-source-symbols!
  "`__kotoba_` is the prefix every synthesized binding uses. Deterministic
  synthesized names are only safe if a program cannot write one: a user local
  called `__kotoba_and_2` would be shadowed by the temp `(and x <expr>)` binds,
  and `<expr>` is user code evaluated inside that scope -- real capture, not a
  theoretical one.

  Checked once over the SOURCE forms, before any desugaring, because after
  desugaring the synthesized names are indistinguishable from written ones. The
  prefix is reserved outright rather than only in binding position: a program
  that cannot mention the name cannot capture, shadow or read one."
  [forms]
  (doseq [value (mapcat #(tree-seq coll? seq %) forms)]
    (when (reserved-binding-name? value)
      (reject! "symbol uses the reserved __kotoba_ prefix" value))))

(defn- desugar-and
  "`(and a b c ...)` -> nested `let`/`if`, ported from kotoba-lang/kotoba's
  runtime.clj `desugar-and` (verified live there, ADR-2607150000): binds
  each argument's value once (never re-evaluated) and branches on it.
  `(and)` is vacuously truthy (1); `(and a)` is just a."
  [args]
  (cond
    (empty? args) 1
    (empty? (rest args)) (desugar-bool-expr (first args))
    :else (let [tmp (chain-temp "and" (count args))]
            (list 'let [tmp (desugar-bool-expr (first args))]
                  (list 'if tmp (desugar-and (rest args)) tmp)))))

(defn- desugar-or
  "Mirror of desugar-and for `(or a b c ...)`. `(or)` is vacuously falsy
  (0); `(or a)` is just a."
  [args]
  (cond
    (empty? args) 0
    (empty? (rest args)) (desugar-bool-expr (first args))
    :else (let [tmp (chain-temp "or" (count args))]
            (list 'let [tmp (desugar-bool-expr (first args))]
                  (list 'if tmp tmp (desugar-or (rest args)))))))

(defn- desugar-cond
  "Lowers `(cond test value ... :else fallback)` to the already admitted
  nested `if` core. Tests retain left-to-right, at-most-once evaluation.
  `:else` is syntax here, not a runtime keyword value, and must be last so
  unreachable clauses cannot be hidden accidentally. An empty cond has the
  profile's ordinary false/nil sentinel value, 0."
  [args form]
  (when (odd? (count args))
    (reject! "cond requires test/result pairs" form :kotoba.error/cond-pairs))
  (letfn [(lower [clauses]
            (if (empty? clauses)
              0
              (let [[test result & remaining] clauses]
                (if (= :else test)
                  (do (when (seq remaining)
                        (reject! "cond :else clause must be last" form))
                      (desugar-expr result))
                  (list 'if (desugar-bool-expr test)
                        (desugar-expr result)
                        (lower remaining))))))]
    (lower args)))

(defn- desugar-condp
  "Lowers the portable `(condp predicate dispatch test result ... default?)`
  subset to a single dispatch binding and left-to-right nested `if` calls.
  The predicate must be a statically resolvable, unqualified two-argument
  function symbol. Clojure's `:>>` extension is deliberately outside this
  bounded slice. With no default, a miss traps like `case`."
  [args form]
  (when (< (count args) 2)
    (reject! "condp requires a predicate and dispatch expression" form))
  (let [[predicate dispatch & clauses] args]
    (when-not (and (symbol? predicate) (nil? (namespace predicate)))
      (reject! "condp predicate must be an unqualified function symbol" form))
    (when (some #{:>>} clauses)
      (reject! "condp :>> clauses are not supported by this portable profile" form))
    (let [default? (odd? (count clauses))
          default (if default? (last clauses) '(quot 1 0))
          pairs (partition 2 (if default? (butlast clauses) clauses))
          tmp (synthetic "condp")]
      (list 'let [tmp (desugar-expr dispatch)]
            (reduce (fn [fallback [test result]]
                      (list 'if
                            (desugar-bool-expr
                             (list predicate (desugar-expr test) tmp))
                            (desugar-expr result)
                            fallback))
                    (desugar-expr default)
                    (reverse pairs))))))

(defn- desugar-cond-thread [args form last?]
  (when (or (empty? args) (odd? (count (rest args))))
    (reject! (str (if last? "cond->>" "cond->")
                  " requires an initial value followed by test/form pairs") form))
  (reduce (fn [value [test step]]
            (when-not (and (seq? step) (symbol? (first step)))
              (reject! (str (if last? "cond->>" "cond->")
                            " update must be a non-empty call form") step))
            (let [tmp (synthetic "cond-thread")
                  threaded (thread-form tmp step last?)]
              (list 'let [tmp value]
                    (list 'if (desugar-bool-expr test)
                          (desugar-expr threaded)
                          tmp))))
          (desugar-expr (first args))
          (partition 2 (rest args))))

(defn- desugar-dotimes [args form]
  (let [[binding & body] args]
    (when-not (and (vector? binding) (= 2 (count binding))
                   (symbol? (first binding)) (nil? (namespace (first binding))))
      (reject! "dotimes requires [unqualified-symbol count]" form))
    (let [[index count-form] binding
          limit (synthetic "dotimes-limit")
          iteration (list* 'do (concat body [(list 'recur (list '+ index 1))]))]
      (desugar-expr
       (list 'let [limit count-form]
             (list 'loop [index 0]
                   (list 'if (list '< index limit) iteration 0)))))))

(defn- annotate-doseq-collection-kinds
  "Lexically mark pair-sequence symbols used as doseq collections. Pair and
  owned-vector values have different backend representations, so this
  provenance must be resolved before the syntax-only doseq desugar."
  [root]
  (letfn [(kind-of [form env]
            (cond
              (symbol? form) (get env form)
              (vector? form) :vector
              (and (seq? form)
                   (contains? #{'list 'cons 'rest
                                '__kotoba_pair_sequence}
                              (first form))) :pair
              :else nil))
          (walk-bindings [bindings env]
            (loop [pairs (seq (partition 2 bindings))
                   current env
                   out []]
              (if-let [[name value] (first pairs)]
                (let [value* (walk-form value current)
                      kind (kind-of value* current)
                      next-env (if (symbol? name)
                                 (cond-> (dissoc current name)
                                   kind (assoc name kind))
                                 current)]
                  (recur (next pairs) next-env (conj out name value*)))
                [(vec out) current])))
          (walk-doseq-binding [binding env]
            (loop [tokens (seq binding) current env out []]
              (if-not tokens
                [(vec out) current]
                (let [item (first tokens)
                      collection (second tokens)
                      collection* (walk-form collection current)
                      kind (kind-of collection* current)
                      collection* (if (and (= :pair kind)
                                           (symbol? collection*))
                                    (list '__kotoba_pair_sequence collection*)
                                    collection*)
                      after-item (if (symbol? item)
                                   (dissoc current item)
                                   current)]
                  (let [[remaining next-env group-out]
                        (loop [remaining (nnext tokens)
                               modifier-env after-item
                               group-out (conj out item collection*)]
                          (if (and remaining (keyword? (first remaining)))
                            (let [modifier (first remaining)
                                  value (second remaining)]
                              (if (= modifier :let)
                                (let [[value* next-env]
                                      (if (and (vector? value)
                                               (even? (count value)))
                                        (walk-bindings value modifier-env)
                                        [(walk-form value modifier-env)
                                         modifier-env])]
                                  (recur (nnext remaining) next-env
                                         (conj group-out modifier value*)))
                                (recur (nnext remaining) modifier-env
                                       (conj group-out modifier
                                             (walk-form value modifier-env)))))
                            [remaining modifier-env group-out]))]
                    (if remaining
                      (recur remaining next-env group-out)
                      [(vec group-out) next-env]))))))
          (walk-form [form env]
            (let [result
                  (cond
                    (seq? form)
                    (let [[op & args] form]
                      (case op
                        let
                        (let [[bindings & body] args]
                          (if (and (vector? bindings) (even? (count bindings)))
                            (let [[bindings* body-env] (walk-bindings bindings env)]
                              (list* 'let bindings*
                                     (map #(walk-form % body-env) body)))
                            (apply list op (map #(walk-form % env) args))))

                        doseq
                        (let [[binding & body] args]
                          (if (and (vector? binding) (<= 2 (count binding)))
                            (let [[binding* body-env]
                                  (walk-doseq-binding binding env)]
                              (list* 'doseq binding*
                                     (map #(walk-form % body-env) body)))
                            (apply list op (map #(walk-form % env) args))))

                        (apply list op (map #(walk-form % env) args))))
                    (vector? form) (mapv #(walk-form % env) form)
                    (map? form) (into {} (map (fn [[k v]]
                                                [(walk-form k env)
                                                 (walk-form v env)]))
                                      form)
                    (set? form) (set (map #(walk-form % env) form))
                    :else form)]
              (if (and (seq (meta form))
                       (or (coll? result) (symbol? result)))
                (with-meta result (meta form))
                result)))]
    (walk-form root {})))

(defn- desugar-doseq [args form]
  (let [[binding & body] args]
    (when-not (vector? binding)
      (reject! "doseq requires a binding vector" form))
    (letfn [(valid-item? [item]
              (and (symbol? item) (nil? (namespace item))))
            (parse-modifier [modifier modifier-value]
              (case modifier
                :let
                (do
                  (when-not (and (vector? modifier-value)
                                 (even? (count modifier-value))
                                 (every? valid-item? (take-nth 2 modifier-value))
                                 (= (count (take-nth 2 modifier-value))
                                    (count (distinct (take-nth 2 modifier-value)))))
                    (reject! "doseq :let requires unique unqualified symbol/value bindings"
                             form))
                  [:let modifier-value])
                :when [:when modifier-value]
                :while [:while modifier-value]
                (reject! "doseq supports only :let, :when, and :while modifiers"
                         form)))
            (pair-sequence-form? [collection]
              (and (seq? collection)
                   (contains? #{'list 'cons 'rest
                                '__kotoba_pair_sequence}
                              (first collection))))
            (parse-groups []
              (loop [tokens (seq binding) groups [] current nil]
                (cond
                  (nil? tokens)
                  (cond-> groups current (conj current))

                  (nil? current)
                  (let [item (first tokens)
                        collection (second tokens)]
                    (when-not (and (valid-item? item) (next tokens))
                      (reject! "doseq requires [unqualified-symbol collection] binding pairs"
                               form))
                    (recur (nnext tokens) groups
                           {:item item
                            :collection collection
                            :pair-sequence? (pair-sequence-form? collection)
                            :modifiers []}))

                  (keyword? (first tokens))
                  (do
                    (when-not (next tokens)
                      (reject! "doseq modifiers require keyword/value pairs" form))
                    (recur (nnext tokens) groups
                           (update current :modifiers conj
                                   (parse-modifier (first tokens) (second tokens)))))

                  (valid-item? (first tokens))
                  (recur tokens (conj groups current) nil)

                  :else
                  (reject! "doseq requires binding pairs separated only by :let/:when/:while modifiers"
                           form))))
            (lower-group [{:keys [item collection modifiers pair-sequence?]}
                          group-body limit]
              (let [iteration-signal
                    (reduce
                     (fn [inner [modifier modifier-value]]
                       (case modifier
                         :let (list 'let modifier-value inner)
                         :when (list 'if modifier-value inner 1)
                         :while (list 'if modifier-value inner 0)))
                     (list* 'do (concat group-body [1]))
                     (reverse modifiers))
                    values (synthetic "doseq-values")
                    length (synthetic "doseq-length")
                    block-signal
                    (fn [indices]
                      (reduce
                       (fn [continuation index]
                         (list 'if (list '< index length)
                               (list 'if
                                     (list 'let
                                           [item (list 'vector-at values index)]
                                           iteration-signal)
                                     continuation
                                     0)
                               1))
                       1
                       (reverse indices)))
                    blocks (map block-signal (partition-all 16 (range limit)))
                    unrolled
                    (reduce (fn [continuation block]
                              (list 'if block continuation 0))
                            0
                            (reverse blocks))
                    pair-unrolled
                    ((fn step [index cursor-expr]
                       (let [cursor (synthetic "doseq-cursor")]
                         (list 'let [cursor cursor-expr]
                               (if (= index limit)
                                 (list 'if (list '= cursor 0)
                                       0
                                       (list 'quot 1 0))
                                 (let [next-cursor (synthetic "doseq-next")]
                                   (list 'if (list '= cursor 0)
                                         0
                                         (list 'let
                                               [next-cursor
                                                (list 'pair-second cursor)]
                                               (list 'if
                                                     (list 'let
                                                           [item (list 'pair-first cursor)]
                                                           iteration-signal)
                                                     (step (inc index) next-cursor)
                                                     0))))))))
                     0 values)
                    bounded
                    (if pair-sequence?
                      pair-unrolled
                      (if (< limit value/vector-literal-item-limit)
                        (list 'if (list '< limit length)
                              (list 'quot 1 0)
                              unrolled)
                        unrolled))]
                (list 'let [values (if (and pair-sequence?
                                            (seq? collection)
                                            (= '__kotoba_pair_sequence
                                               (first collection)))
                                     (second collection)
                                     collection)]
                      (if pair-sequence?
                        bounded
                        (list 'let [length (list 'vector-count values)]
                              bounded)))))]
      (let [groups (parse-groups)
            group-count (count groups)]
        (when-not (<= 1 group-count 4)
          (reject! "doseq supports at most four collection bindings"
                   form))
        (let [lowered
              (reduce (fn [inner group]
                        (lower-group group [inner]
                                     (cond
                                       (= 4 group-count) 2
                                       (= 3 group-count) 4
                                       (= 2 group-count) 16
                                       (:pair-sequence? group) 32
                                       :else value/vector-literal-item-limit)))
                      (list* 'do (concat body [0]))
                      (reverse groups))]
          (desugar-expr lowered))))))

(defn- thread-form [value step last?]
  (cond
    (symbol? step) (list step value)
    (and (seq? step) (symbol? (first step)))
    (if last?
      (apply list (first step) (concat (rest step) [value]))
      (list* (first step) value (rest step)))
    :else (reject! "thread step must be a symbol or non-empty call" step)))

(defn- desugar-thread [args form last?]
  (when (empty? args)
    (reject! (if last? "->> requires an initial value" "-> requires an initial value") form))
  (desugar-expr (reduce #(thread-form %1 %2 last?) (first args) (rest args))))

(defn- desugar-as-thread [args form]
  (let [[initial name & steps] args]
    (when-not (and (<= 2 (count args)) (symbol? name) (nil? (namespace name)))
      (reject! "as-> requires an initial value, an unqualified binding symbol, and optional forms" form))
    (desugar-expr
     (reduce (fn [value step] (list 'let [name value] step))
             initial steps))))

(defn- resolve-ref-type
  "Expand `[:ref :schema/name]` through `*schemas*` when available."
  [type]
  (if (and (vector? type)
           (= 2 (count type))
           (= :ref (first type))
           (map? *schemas*))
    (or (get *schemas* (second type)) type)
    type))

(defn- record-field-type
  "Field type from a record descriptor or `[:ref …]` schema name, else nil."
  [rec-type field]
  (let [rec (resolve-ref-type rec-type)]
    (when (and (record-type? rec) (keyword? field))
      (some (fn [[k t]] (when (= k field) t))
            (nth rec 2)))))

(defn- resolve-option-type
  "Best-effort option type for sugar lowering (Product Value ABI v1).

  Prefer an explicit typed local (`*local-option-types*`), then syntactic
  constructors `(option-some-of T …)` / `(option-none-of T)`, then
  `(record-get … :field)` when the field is itself `[:option T]` (T5.2
  option-string-in-record). Fall back to `[:option :i64]` only for legacy
  monomorphic option-i64 paths."
  [value-form]
  (cond
    (and (symbol? value-form) (nil? (namespace value-form))
         (map? *local-option-types*))
    (get *local-option-types* value-form)

    (and (seq? value-form)
         (contains? '#{option-some-of option-none-of option-some?-of
                       option-value-of option-match}
                    (first value-form))
         (vector? (second value-form))
         (= :option (first (second value-form))))
    (second value-form)

    ;; `(record-get TYPE value field)` (post rewrite) or
    ;; `(record-get value field)` (pre rewrite, typed local).
    (and (seq? value-form)
         (= 'record-get (first value-form)))
    (let [args (vec (rest value-form))
          field-type
          (cond
            (and (= 3 (count args)) (keyword? (nth args 2)))
            (record-field-type (nth args 0) (nth args 2))

            (and (= 2 (count args))
                 (symbol? (nth args 0))
                 (keyword? (nth args 1))
                 (map? *local-types*))
            (record-field-type (get *local-types* (nth args 0)) (nth args 1))

            :else nil)]
      (if (and (vector? field-type) (= :option (first field-type)))
        field-type
        [:option :i64]))

    :else [:option :i64]))

(defn- option-payload-fallback
  "Typed bottom value for option-value-of's unused fallback arm.
  Must match payload type so typecheck accepts the if-some lowering."
  [payload-type]
  (cond
    (= payload-type :i64) 0
    (= payload-type :bool) false
    (= payload-type :string) ""
    (= payload-type :keyword) :none
    (= payload-type :f64) 0.0
    (= payload-type :f32) 0.0
    :else 0))

(defn- desugar-some-thread [args form last?]
  (when (empty? args)
    (reject! (if last? "some->> requires an initial option" "some-> requires an initial option") form))
  (letfn [(lower [option-form steps]
            (if (empty? steps)
              (desugar-expr option-form)
              (let [tmp (if *loop-counter*
                          (symbol (str "some-thread__" (vswap! *loop-counter* inc)))
                          (synthetic "some-thread"))
                    option-type (or (resolve-option-type option-form) [:option :i64])
                    payload-type (when (and (vector? option-type) (= :option (first option-type)))
                                   (second option-type))
                    payload (list 'option-value-of option-type tmp
                                  (option-payload-fallback payload-type))
                    threaded (thread-form payload (first steps) last?)]
                (list 'let [tmp (desugar-expr option-form)]
                      (list 'if (list 'option-some?-of option-type tmp)
                            (lower threaded (rest steps))
                            (list 'option-none-of option-type))))))]
    (lower (first args) (rest args))))

(defn- desugar-binding-if [args form when?]
  (let [[binding & bodies] args]
    (when-not (and (vector? binding) (= 2 (count binding)))
      (reject! (if when? "when-let requires one binding pair"
                           "if-let requires one binding pair") form))
    (when (if when? (empty? bodies) (not (<= 1 (count bodies) 2)))
      (reject! (if when? "when-let requires at least one body expression"
                           "if-let requires then and optional else expressions") form))
    (let [[pattern value] binding
          tmp (synthetic "binding-if")
          then-form (if when?
                      (if (= 1 (count bodies)) (first bodies) (cons 'do bodies))
                      (first bodies))
          else-form (if when? 0 (if (= 2 (count bodies)) (second bodies) 0))]
      (desugar-expr
       (list 'let [tmp (desugar-bool-expr value)]
             (list 'if tmp (list 'let [pattern tmp] then-form) else-form))))))

(defn- desugar-binding-some [args form when?]
  (let [[binding & bodies] args]
    (when-not (and (vector? binding) (= 2 (count binding)))
      (reject! (if when? "when-some requires one binding pair"
                           "if-some requires one binding pair") form))
    (when (if when? (empty? bodies) (not (<= 1 (count bodies) 2)))
      (reject! (if when? "when-some requires at least one body expression"
                           "if-some requires then and optional else expressions") form))
    (let [[pattern value] binding
          ;; Deterministic, like every other synthesized temp. This was already
          ;; deterministic but kept the old `binding-some__N` shape, which has
          ;; two costs: it still matches the `.+__\d+` gensym pattern, so the
          ;; conformance digest normalized it away and could not see a change in
          ;; it; and it borrowed `*loop-counter*`, so adding or removing a
          ;; `loop` renumbered it for no reason.
          tmp (synthetic "binding-some")
          option-type (or (resolve-option-type value) [:option :i64])
          then-form (if when?
                      (if (= 1 (count bodies)) (first bodies) (desugar-do bodies))
                      (first bodies))
          else-form (if when? 0 (if (= 2 (count bodies)) (second bodies) 0))
          payload-type (when (and (vector? option-type) (= :option (first option-type)))
                         (second option-type))
          fallback (option-payload-fallback payload-type)]
      (when-not (and (vector? option-type) (= :option (first option-type)))
        (reject! "if-some/when-some value must have an option type; use match-option with an explicit type or a typed local"
                 form))
      (desugar-expr
       (list 'let [tmp value]
             (list 'if (list 'option-some?-of option-type tmp)
                   (list 'let [pattern (list 'option-value-of option-type tmp fallback)]
                         then-form)
                   else-form))))))

(defn- desugar-case [args form]
  (when (empty? args) (reject! "case requires a dispatch expression" form))
  (let [[dispatch & clauses] args
        default? (odd? (count clauses))
        default (if default? (last clauses) '(quot 1 0))
        pairs (partition 2 (if default? (butlast clauses) clauses))
        groups (map first pairs)
        constants (mapcat #(if (seq? %) % [%]) groups)
        literal? #(or (kotoba-integer? %) (keyword? %) (boolean? %) (string? %))]
    (when-not (every? literal? constants)
      (reject! "case constants must be bounded integer, keyword, boolean, or string literals" form))
    (when-not (= (count constants) (count (distinct constants)))
      (reject! "case constants must be unique" form))
    (let [tmp (synthetic "case")]
      (list 'let [tmp (desugar-expr dispatch)]
            (reduce (fn [fallback [group result]]
                      (let [members (if (seq? group) group [group])
                            test (if (= 1 (count members))
                                   (list '= tmp (desugar-expr (first members)))
                                   (desugar-or
                                    (map #(list '= tmp (desugar-expr %)) members)))]
                        (list 'if test
                              (desugar-expr result) fallback)))
                    (desugar-expr default)
                    (reverse pairs))))))

(defn- desugar-comparison-chain [op args form]
  (when (and (not= op '=) (empty? args))
    (reject! "ordered comparison requires at least one operand" form))
  ;; Comparisons are `:bool`-typed, so a chain folds to `true`/`false` rather
  ;; than 1/0 — otherwise the chain is an i64 that cannot compose with `and`,
  ;; `or`, `not` or another comparison.
  (letfn [(chain [left remaining]
            (if (empty? remaining)
              true
              (let [right (chain-temp "cmp" (count remaining))]
                (list 'let [right (desugar-expr (first remaining))]
                      (list 'if (list op left right)
                            (chain right (rest remaining)) false)))))]
    (if (empty? args)
      true
      (let [left (chain-temp "cmp" (inc (count args)))]
        (list 'let [left (desugar-expr (first args))]
              (chain left (rest args)))))))


(defn- desugar-do
  "ADR-2607180900 L2: `(do a b c)` -> nested `let` returning last expression."
  [args]
  (cond
    (empty? args) 0
    (empty? (rest args)) (desugar-expr (first args))
    :else (let [tmp (synthetic "do-tmp")]
            (list 'let [tmp (desugar-expr (first args))]
                  (desugar-do (rest args))))))

(defn- desugar-map
  "Lower a bounded literal into the owned typed-map KIR operation. Keys are
  canonical keywords only; values are checked i64 expressions. Sorting by
  canonical keyword text makes KIR reproducible without hashing identity."
  [form]
  (when (> (count form) max-list-items)
    (reject! "map entry count exceeds admission limit" form))
  (when-not (every? keyword? (keys form))
    (reject! "map keys must be bounded keywords" form))
  (apply list 'map-new
         (mapcat (fn [[k v]] [k (desugar-expr v)])
                 (sort-by (comp str key) form))))

(defn- document-reader-f64-form?
  "The JVM reader represents an f64 literal as a Double. The JVM-free reader
  preserves its exact bits as `(f64-from-bits <i64>)`; recognize that closed
  reader shape here so contextual document literals elaborate identically."
  [form]
  (and (seq? form)
       (true? (:kotoba.reader/f64-literal (meta form)))
       (= 'f64-from-bits (first form))
       (= 2 (count form))
       (kotoba-integer? (second form))))

(defn- document-literal-key-frame [text]
  (str (count text) ":" text))

(defn- document-literal-sort-key
  "Stable, host-independent ordering used only to make elaborated KIR
  reproducible. Runtime document constructors still own canonical EDN order."
  [form]
  (cond
    (nil? form) "00:nil"
    (boolean? form) (str "01:" form)
    (kotoba-integer? form) (str "02:" form)
    (value/f64-value? form) (str "03:" (value/f64-to-i64-bits form))
    (document-reader-f64-form? form) (str "03:" (second form))
    (string? form) (str "04:" form)
    (keyword? form) (str "05:" form)
    (symbol? form) (str "06:" form)
    (vector? form) (str "07:["
                        (apply str
                               (map #(document-literal-key-frame
                                      (document-literal-sort-key %))
                                    form))
                        "]")
    (set? form) (str "08:{"
                     (apply str
                            (map document-literal-key-frame
                                 (sort (map document-literal-sort-key form))))
                     "}")
    (map? form) (str "09:{"
                     (apply str
                            (sort
                             (map (fn [[key item]]
                                    (str (document-literal-key-frame
                                          (document-literal-sort-key key))
                                         (document-literal-key-frame
                                          (document-literal-sort-key item))))
                                  form)))
                     "}")
    (seq? form) (str "10:("
                     (apply str
                            (map #(document-literal-key-frame
                                   (document-literal-sort-key %))
                                 form))
                     ")")
    :else (str "99:" (pr-str form))))

(defn- attach-literal-location [literal elaborated]
  (let [location (select-keys (meta literal)
                              [:line :column :end-line :end-column :offset :end-offset])]
    (if (and (seq location) (coll? elaborated))
      (with-meta elaborated (merge (meta elaborated) location))
      elaborated)))

(defn- elaborate-document-literal
  "Elaborate one closed EDN-shaped tree into the existing document
  constructors. Nothing below `(document ...)` is evaluated as Kotoba code."
  [literal]
  (let [nodes (volatile! 0)]
    (letfn [(charge! [form depth]
              (when (> depth value/document-depth-limit)
                (reject! "document literal exceeds depth limit" form))
              (when (> (vswap! nodes inc) value/document-node-limit)
                (reject! "document literal exceeds node limit" form)))
            (walk [form depth]
              (charge! form depth)
              (attach-literal-location
               form
               (cond
                 (nil? form) '(document-null)
                 (boolean? form) (list 'document-bool form)
                 (kotoba-integer? form) (list 'document-i64 form)
                 (value/f64-value? form) (list 'document-f64 form)
                 (document-reader-f64-form? form) (list 'document-f64 form)
                 (string? form) (list 'document-string form)
                 (keyword? form) (list 'document-keyword form)
                 (symbol? form) (list 'document-symbol (list 'symbol (str form)))
                 (vector? form)
                 (do (when (> (count form) value/document-container-item-limit)
                       (reject! "document vector literal exceeds item limit" form))
                     (list* 'document-vector (map #(walk % (inc depth)) form)))
                 (set? form)
                 (do (when (> (count form) value/document-container-item-limit)
                       (reject! "document set literal exceeds item limit" form))
                     (list* 'document-set
                            (map #(walk % (inc depth))
                                 (sort-by document-literal-sort-key form))))
                 (map? form)
                 (do (when (> (count form) value/document-container-item-limit)
                       (reject! "document map literal exceeds entry limit" form))
                     (list* 'document-map
                            (mapcat (fn [[key item]]
                                      [(if (keyword? key)
                                         key
                                         (walk key (inc depth)))
                                       (walk item (inc depth))])
                                    (sort-by (comp document-literal-sort-key key) form))))
                 (seq? form)
                 (do (when (> (count form) value/document-container-item-limit)
                       (reject! "document list literal exceeds item limit" form))
                     (list* 'document-list (map #(walk % (inc depth)) form)))
                 :else (reject! "document requires a closed EDN literal tree" form))))]
      (walk literal 0))))

(defn- contextual-document-literal?
  "True only for syntax that is unambiguously a closed document value.

  Simple symbols and lists remain expressions: a document-typed parameter must
  still pass through as a parameter, and a call returning :document must still
  execute. Namespaced symbols are admitted as inert document data because they
  cannot name lexical values in the safe source profile. Explicit document
  syntax remains the escape hatch for simple symbols and EDN list values."
  [form]
  (cond
    (or (nil? form)
        (boolean? form)
        (kotoba-integer? form)
        (value/f64-value? form)
        (document-reader-f64-form? form)
        (string? form)
        (keyword? form)) true
    (symbol? form) (some? (namespace form))
    (vector? form) (every? contextual-document-literal? form)
    (set? form) (every? contextual-document-literal? form)
    (map? form) (every? (fn [[key item]]
                          (and (contextual-document-literal? key)
                               (contextual-document-literal? item)))
                        form)
    :else false))

(def ^:private string-from-i64-helper-name '__kotoba_string_from_i64)
(def ^:private string-from-i64-nat-helper-name '__kotoba_string_from_i64_nat)

(def ^:private string-from-i64-nat-helper
  "Unsigned decimal digits for string-from-i64 (Product Value ABI v1).
  Uses only string-substring/string-concat already qualified for wasm."
  {:name string-from-i64-nat-helper-name
   :params '[n]
   :param-types [:i64]
   :result :string
   :effects #{}
   :body '(if (< n 10)
            (string-substring "0123456789" n (+ n 1))
            (string-concat
             (__kotoba_string_from_i64_nat (quot n 10))
             (string-substring "0123456789" (- n (* (quot n 10) 10))
                               (+ (- n (* (quot n 10) 10)) 1))))})

(def ^:private string-from-i64-helper
  "Signed decimal printer for string-from-i64 surface (Product Value ABI v1)."
  {:name string-from-i64-helper-name
   :params '[n]
   :param-types [:i64]
   :result :string
   :effects #{}
   :body '(if (< n 0)
            (string-concat "-" (__kotoba_string_from_i64_nat (- 0 n)))
            (__kotoba_string_from_i64_nat n))})

(defn- uses-string-from-i64? [form]
  (cond
    (seq? form) (or (= string-from-i64-helper-name (first form))
                    (= string-from-i64-nat-helper-name (first form))
                    (some uses-string-from-i64? (rest form)))
    (coll? form) (some uses-string-from-i64? form)
    :else false))

(def ^:private map-get-helper-name '__kotoba_map_get)

(def ^:private map-get-helper
  "Compiler-synthesized recursive linear scan over a desugar-map cons-list,
  injected into a module's function set only when `get` is actually used
  (analyze's uses-map-get? scan) -- ADR-2607150000. Written directly in
  already-primitive form (if/=/pair-first/pair-second/self-call), not run
  through desugar-expr. Each recursive step costs 1 unit of this
  compiler's existing fixed 512-instruction-call fuel budget (ir.clj/
  backend/wasm.clj/core.clj's `default-fuel`/global fuel counter) -- a
  map lookup on a long map, or a miss, can exhaust it; not a new limit,
  the existing one now also bounds map-walk depth."
  {:name map-get-helper-name
   :params '[m k default]
   :result :i64
   :effects #{}
   :body '(if (= m 0)
            default
            (if (= (pair-first (pair-first m)) k)
              (pair-second (pair-first m))
              (__kotoba_map_get (pair-second m) k default)))})

(defn- uses-map-get? [form]
  (cond
    (seq? form) (or (= map-get-helper-name (first form))
                    (some uses-map-get? (rest form)))
    (coll? form) (some uses-map-get? form)
    :else false))

(def ^:private map-without-helper-name '__kotoba_map_without)

(def ^:private map-without-helper
  "Compiler-synthesized recursive filter over a desugar-map cons-list,
  removing every entry whose key equals `k` while preserving the relative
  order of the rest -- `assoc`'s desugar (below) calls this on the OLD map
  before prepending the new pair, so re-`assoc`-ing an existing key no
  longer leaves the old entry as dead weight (a real bug found and fixed
  in the same ADR-2607150000 line of work that first landed assoc: the
  original desugar only ever prepended, `get`'s first-match-wins scan made
  the RESULT correct but the map grew without bound under repeated
  re-assoc of the same key). Injected only when `assoc` is actually used
  (`uses-map-without?`), same pattern as `map-get-helper`. Recurses through
  the WHOLE tail even after a match (not just the first hit) so any
  pre-existing duplicate from before this fix, or a hand-built map literal
  with a repeated key, is fully cleaned up, not just shadowed once more."
  {:name map-without-helper-name
   :params '[m k]
   :result :i64
   :effects #{}
   :body '(if (= m 0)
            0
            (if (= (pair-first (pair-first m)) k)
              (__kotoba_map_without (pair-second m) k)
              (pair (pair-first m) (__kotoba_map_without (pair-second m) k))))})

(defn- uses-map-without? [form]
  (cond
    (seq? form) (or (= map-without-helper-name (first form)) (some uses-map-without? (rest form)))
    (coll? form) (some uses-map-without? form)
    :else false))

(defn- destructure-binding
  "Expands ONE `[pattern value-expr]` `let`/`defn`-param binding into a flat
  seq of `[symbol expr]` pairs (ADR-2607150000/ADR 0207). PATTERN is a plain
  symbol, a positional vector `[a [b c] & rest]`, or a map using `:keys`,
  `:or`, `:as`, and Clojure-shaped explicit entries such as
  `{{:keys [name]} :user}`. Composite patterns recurse through ordinary `nth`
  and an internal destructuring lookup; the later type-directed pass selects
  the exact heterogeneous-vector, typed-map, record, or legacy accessor.

  VALUE-EXPR must already be desugared. Every composite pattern binds one
  deterministic synthetic temp first, so neither the original expression nor
  a nested projection is evaluated more than once."
  [pattern value-expr]
  (letfn [(supported-pattern? [candidate]
            (or (symbol? candidate) (vector? candidate) (map? candidate)))
          (expand [candidate value]
            (cond
              (symbol? candidate) [[candidate value]]

              (vector? candidate)
              (let [tmp (synthetic "destr-vector")
                    [positional rest-part] (split-with (complement #{'&}) candidate)]
                (when-not (every? supported-pattern? positional)
                  (reject! "vector destructuring items must be symbols or nested vector/map patterns"
                           candidate))
                (when (and (seq rest-part)
                           (or (not= 2 (count rest-part))
                               (not (symbol? (second rest-part)))))
                  (reject! "`&` in vector destructuring must be followed by exactly one rest-binding symbol"
                           candidate))
                (into [[tmp value]]
                      (concat
                       (mapcat (fn [[index item-pattern]]
                                 (expand item-pattern (list 'nth tmp index)))
                               (map-indexed vector positional))
                       ;; A rest binding retains the established homogeneous
                       ;; vector contract. Heterogeneous rest needs an exact
                       ;; sliced descriptor and is rejected by type checking
                       ;; until that representation is admitted explicitly.
                       (when-let [rest-name (second rest-part)]
                         [[rest-name (list 'vector-drop tmp (count positional))]]))))

              (map? candidate)
              (let [keys-vec (get candidate :keys [])
                    defaults (get candidate :or {})
                    as-name (:as candidate)
                    explicit (apply dissoc candidate [:keys :or :as])
                    explicit (sort-by (comp pr-str val) explicit)
                    direct-symbols
                    (into (set keys-vec)
                          (keep (fn [[binding-pattern _]]
                                  (when (symbol? binding-pattern) binding-pattern)))
                          explicit)]
                (when-not (and (vector? keys-vec) (every? symbol? keys-vec)
                               (map? defaults) (every? symbol? (keys defaults))
                               (every? direct-symbols (keys defaults))
                               (or (nil? as-name) (symbol? as-name))
                               (every? (fn [[binding-pattern lookup-key]]
                                         (and (supported-pattern? binding-pattern)
                                              (keyword? lookup-key)))
                                       explicit)
                               (or (seq keys-vec) (seq explicit) as-name))
                  (reject! (str "map destructuring requires :keys, :as, or keyword-valued "
                                "explicit entries, with :or defaults for direct symbol bindings")
                           candidate))
                (let [tmp (synthetic "destr-map")
                      entries (concat (map (fn [name] [name (keyword name)]) keys-vec)
                                      explicit)]
                  (into [[tmp value]]
                        (concat
                         (mapcat
                          (fn [[binding-pattern lookup-key]]
                            (let [lookup
                                  (if (and (symbol? binding-pattern)
                                           (contains? defaults binding-pattern))
                                    (list '__kotoba_destructure_get tmp lookup-key
                                          (desugar-expr (get defaults binding-pattern)))
                                    (list '__kotoba_destructure_get tmp lookup-key))]
                              (expand binding-pattern lookup)))
                          entries)
                         (when as-name [[as-name tmp]])))))

              :else (reject! "unsupported destructuring pattern" candidate)))]
    (expand pattern value-expr)))

(defn- form-free-symbols
  "Symbols FORM references as VALUES (never call-heads) that aren't in
  BOUND -- a purely syntactic free-variable scan for `loop`'s closure
  conversion (see desugar-expr's `loop` case). Operates on an ALREADY
  DESUGARED form, so every `let` it sees has plain-symbol bindings only
  (destructuring has already been expanded away by this point) -- no need
  to reason about vector/map patterns here."
  [form bound]
  (cond
    (symbol? form) (if (contains? bound form) #{} #{form})
    (seq? form)
    (let [[op & args] form]
      (if (= op 'let)
        (let [[bindings & body] args]
          (loop [pairs (partition 2 bindings) bound bound acc #{}]
            (if-let [[name value] (first pairs)]
              (recur (next pairs) (conj bound name) (set/union acc (form-free-symbols value bound)))
              (apply set/union acc (map #(form-free-symbols % bound) body)))))
        (apply set/union #{} (map #(form-free-symbols % bound) args))))
    (coll? form) (apply set/union #{} (map #(form-free-symbols % bound) form))
    :else #{}))

(defn- replace-recur
  "Walks the already-desugared loop BODY, replacing every `(recur a b ...)`
  with a call to HELPER-NAME carrying the new loop-binding values (A/B/...)
  followed by CAPTURED's outer-variable values UNCHANGED (they never vary
  across iterations, only the loop's own bindings do). A `recur` belonging
  to a NESTED loop is never seen here -- desugar-expr's `loop` case already
  resolved it (into an ordinary call to ITS OWN gensym'd helper) as part of
  desugaring this loop's body, before replace-recur ever runs."
  [form helper-name loop-names captured]
  (cond
    (seq? form)
    (let [[op & args] form]
      (if (= op 'recur)
        (do (when-not (= (count args) (count loop-names))
              (reject! "recur argument count must match loop bindings" form))
            (list* helper-name (concat args captured)))
        (cons op (map #(replace-recur % helper-name loop-names captured) args))))
    :else form))

(defn- top-level-function-symbol? [value]
  (and (symbol? value)
       (nil? (namespace value))
       (not (contains? *lexical-bindings* value))
       (contains? *function-arities* value)))

(defn- callback-supported-arities [callback]
  (cond
    (top-level-function-symbol? callback)
    (get *function-arities* callback)

    (and (seq? callback) (= 'fn (first callback)))
    (let [[_ params-or-clause & tail] callback
          clauses (if (vector? params-or-clause)
                    [params-or-clause]
                    (when (every? #(and (seq? %) (vector? (first %)))
                                  (cons params-or-clause tail))
                      (map first (cons params-or-clause tail))))]
      (when clauses
        (apply set/union
               (map (fn [params]
                      (let [amp-index (first (keep-indexed #(when (= '& %2) %1) params))]
                        (if amp-index
                          (set (range amp-index 5))
                          #{(count params)})))
                    clauses))))

    :else nil))

(defn- callback-closure [kind callback arity]
  (when-let [arities (callback-supported-arities callback)]
    (when-not (contains? arities arity)
      (reject! (str (name kind) " callback does not provide arity " arity)
               callback)))
  (if (top-level-function-symbol? callback)
    (desugar-expr (list 'fn-ref callback))
    (desugar-expr callback)))

(defn- synthesize-lazy-map [callback colls form]
  (let [arity (count colls)
        helper-name (synthetic "lazy_map")
        callback-param (symbol (str helper-name "_callback"))
        coll-params (mapv #(symbol (str helper-name "_coll_" %)) (range arity))
        callback-value (callback-closure :lazy-map callback arity)
        resolver
        (binding [*lifting-lazy-thunk?* true]
          (lift-lambda
           (list 'fn []
                 (list 'if
                       (apply list 'or (map #(list 'lazy-empty? %) coll-params))
                       0
                       (list 'pair
                             (list 'fn []
                                   (apply list 'invoke callback-param
                                          (map #(list 'lazy-first %) coll-params)))
                             (list 'fn []
                                   (apply list helper-name callback-param
                                          (map #(list 'lazy-rest %) coll-params))))))))
        helper {:name helper-name
                :params (into [callback-param] coll-params)
                :result :i64 :effects #{} :body resolver}]
    (when (> (count (:params helper)) max-parameters)
      (reject! "lazy-map callback plus sources exceed ABI-supported arity" form))
    (when *pending-loop-helpers*
      (swap! *pending-loop-helpers* conj helper))
    (apply list helper-name callback-value (map desugar-expr colls))))

(defn- synthesize-lazy-filter [callback coll]
  (let [helper-name (synthetic "lazy_filter")
        callback-param (symbol (str helper-name "_callback"))
        coll-param (symbol (str helper-name "_coll"))
        value (symbol (str helper-name "_value"))
        callback-value (callback-closure :lazy-filter callback 1)
        resolver
        (binding [*lifting-lazy-thunk?* true]
          (lift-lambda
           (list 'fn []
                 (list 'if (list 'lazy-empty? coll-param)
                       0
                       (list 'let [value (list 'lazy-first coll-param)]
                             (list 'if (list 'invoke :bool callback-param value)
                                   (list 'pair
                                         (list 'fn [] value)
                                         (list 'fn []
                                               (list helper-name callback-param
                                                     (list 'lazy-rest coll-param))))
                                   (list 'invoke
                                         (list helper-name callback-param
                                               (list 'lazy-rest coll-param)))))))))
        helper {:name helper-name :params [callback-param coll-param]
                :result :i64 :effects #{} :body resolver}]
    (when *pending-loop-helpers*
      (swap! *pending-loop-helpers* conj helper))
    (list helper-name callback-value (desugar-expr coll))))

(defn- desugar-expr* [form contextual-result-type]
  (cond
    ;; A closed EDN-shaped value in a :document context is already fully
    ;; typed by its consumer. Elaborate it directly so authors do not have to
    ;; wrap ordinary data in document syntax. The predicate deliberately
    ;; excludes executable lists and lexical symbols.
    (and (= :document contextual-result-type)
         (contextual-document-literal? form))
    (elaborate-document-literal form)

    ;; Under nbb, compiler-synthesized integer literals are ordinary JS
    ;; numbers while source integers are bigint. Classify the integral host
    ;; form before the broader f64 predicate so generated loop indices/defaults
    ;; stay i64 in typed modules.
    (kotoba-integer? form) form
    (value/f64-value? form) (list 'f64-from-bits (value/f64-to-i64-bits form))
    (keyword? form) form
    (boolean? form) form
    (nil? form) '(option-none)
    (map? form) (desugar-map form)
    ;; Top-level constants admit only bounded, non-empty keyword sets. Lower
    ;; them into the typed-set profile in canonical order so raw set iteration
    ;; order is never observable in KIR or an artifact.
    (set? form) (list* 'typed-set-new [:set :keyword]
                       (sort-by pr-str form))
    ;; Vector literals now enter the owned bounded vector-i64 profile rather
    ;; than the legacy untagged pair arena. Binding and parameter vectors are
    ;; consumed by their enclosing forms and never reach this branch.
    ;; here because `let`'s OWN bindings vector never reaches this branch:
    ;; the `let` case below fully owns processing it directly (via
    ;; destructure-binding) and never routes it back through desugar-expr
    ;; as a bare value. `defn` params are consumed entirely inside
    ;; `analyze`, before any desugar-expr call, for the same reason.
    (vector? form)
    (do (when (> (count form) value/vector-literal-item-limit)
          (reject! "vector literal exceeds item limit" form))
        (let [item-types (mapv closed-vector-literal-type form)]
          (cond
            (or (empty? item-types) (every? #{:i64} item-types))
            (apply list 'vector-new (map desugar-expr form))

            (every? #{:f64} item-types)
            (apply list 'vector-f64-new (map desugar-expr form))

            (every? some? item-types)
            (let [type [:vector item-types]]
              (list* 'hetero-vector-new type
                     (mapv (fn [item-type item]
                             (desugar-expected-value item-type item))
                           item-types form)))

            :else
            (apply list 'vector-new (map desugar-expr form)))))
    (not (seq? form)) form
    ;; `(:field r)` — the Clojure keyword accessor. Desugars to the 2-arity
    ;; `record-get`, which `rewrite-record-projection` then resolves against the
    ;; value's inferred type (ADR 0189/0190). Keeping it a desugar means no new
    ;; head reaches validation, inference or any backend.
    (and (keyword? (first form)) (= 2 (count form)))
    (list 'record-get (desugar-expr (second form)) (first form))
    :else
    (let [[op & args] form]
      (cond
        (lexical-call-form? form)
        (desugar-lexical-call (or contextual-result-type :i64) form)

        (contains? contextual-string-argument-indexes op)
        (let [string-indexes (get contextual-string-argument-indexes op)]
          (apply list op
                 (map-indexed (fn [index arg]
                                ((if (contains? string-indexes index)
                                   #(desugar-result-expr :string %)
                                   desugar-expr)
                                 arg))
                              args)))

        (contains? contextual-document-argument-indexes op)
        (let [document-indexes (get contextual-document-argument-indexes op)]
          (apply list op
                 (map-indexed (fn [index arg]
                                ((if (contains? document-indexes index)
                                   #(desugar-result-expr :document %)
                                   desugar-expr)
                                 arg))
                              args)))

        (contains? '#{document-vector document-list document-set} op)
        (apply list op (map #(desugar-result-expr :document %) args))

        (= 'document-map op)
        (apply list op
               (map-indexed (fn [index arg]
                              ((if (odd? index)
                                 #(desugar-result-expr :document %)
                                 desugar-expr)
                               arg))
                            args))

        (contains? contextual-f64-argument-indexes op)
        (let [f64-indexes (get contextual-f64-argument-indexes op)]
          (apply list op
                 (map-indexed (fn [index arg]
                                ((if (contains? f64-indexes index)
                                   #(desugar-result-expr :f64 %)
                                   desugar-expr)
                                 arg))
                              args)))

        (contains? contextual-f32-argument-indexes op)
        (let [f32-indexes (get contextual-f32-argument-indexes op)]
          (apply list op
                 (map-indexed (fn [index arg]
                                ((if (contains? f32-indexes index)
                                   #(desugar-result-expr :f32 %)
                                   desugar-expr)
                                 arg))
                              args)))

        (contains? contextual-vector-f64-argument-types op)
        (let [expected-types (get contextual-vector-f64-argument-types op)]
          (apply list op
                 (map-indexed (fn [index arg]
                                (if-let [expected (get expected-types index)]
                                  (desugar-result-expr expected arg)
                                  (desugar-expr arg)))
                              args)))

        (= 'vector-f64-new op)
        (apply list op (map #(desugar-result-expr :f64 %) args))

        (contains? typed-vector-operations op)
        (do
          (when-not (= (get typed-vector-operations op) (count args))
            (reject! "typed vector operation arity mismatch" form))
          (apply list op
                 (map-indexed (fn [index arg]
                                ((if (zero? index)
                                   #(desugar-result-expr :vector-i64 %)
                                   desugar-expr)
                                 arg))
                              args)))

        :else
        (case op
        list (binding [*contextual-closure-result-type* contextual-result-type]
               (desugar-list args form))
        fn (binding [*contextual-closure-result-type* contextual-result-type]
             (lift-lambda form))
        if (apply list 'if
                  (map-indexed (fn [index arg]
                                 (cond
                                   (zero? index) (desugar-bool-expr arg)
                                   contextual-result-type
                                   (desugar-result-expr contextual-result-type arg)
                                   :else (desugar-expr arg)))
                               args))
        fn-ref
        (if (contains? *function-arities* 'fn-ref)
          (apply list 'fn-ref (map desugar-expr args))
          (do
            (when-not (and (= 1 (count args)) (symbol? (first args)))
              (reject! "fn-ref requires one top-level function symbol" form))
            (let [function-name (first args)
                  arities (get *function-arities* function-name)]
              (when-not (seq arities)
                (reject! "fn-ref requires a declared top-level function" function-name))
              (when (some #(> % 4) arities)
                (reject! "fn-ref target exceeds closure ABI arity four" function-name))
              (lift-lambda
               (cons 'fn
                     (mapv (fn [arity]
                             (let [params (mapv #(symbol (str "__kotoba_fn_ref_arg_" %))
                                                (range arity))]
                               (list params (apply list function-name params))))
                           (sort arities)))))))
        invoke
        (if (contains? *function-arities* 'invoke)
          (apply list 'invoke (map desugar-expr args))
          (let [declared-result (first args)
                typed? (closure-result-type? declared-result)
                _ (when (and (or (keyword? declared-result)
                                 (structured-type? declared-result))
                             (not typed?))
                    (reject! "closure result type is outside the admitted dispatcher profile"
                             declared-result))
                ;; A computed head is dynamic, but its result family often is
                ;; not: consumers such as string-length, record-get, and typed
                ;; function returns already provide a closed result context.
                ;; Reuse that context so ordinary source can say `(invoke f x)`
                ;; and reserve an explicit descriptor for genuinely ambiguous
                ;; positions. No context retains the historical :i64 default.
                result-type (cond
                              typed? (canonical-closure-result-type declared-result)
                              contextual-result-type
                              (canonical-closure-result-type contextual-result-type)
                              :else :i64)
                call-args (if typed? (rest args) args)]
            (when-not (<= 1 (count call-args) 5)
              (reject! "invoke requires an optional admitted result descriptor, a closure, and zero to four arguments"
                       form))
            (let [[closure & invoke-args] call-args]
              (apply list (request-invoke-dispatcher result-type (count invoke-args))
                     (desugar-result-expr result-type closure)
                     (map desugar-expr invoke-args)))))
        apply
        (if (contains? *function-arities* 'apply)
          (apply list 'apply (map desugar-expr args))
          (do
            (when-not (<= 2 (count args) 6)
              (reject! "apply requires a closure, up to four fixed arguments, and a final argument collection" form))
            (when *uses-apply?* (vreset! *uses-apply?* true))
            (let [closure (first args)
                  call-args (rest args)
                  trailing (last call-args)
                  fixed (butlast call-args)
                  argument-list (reduce (fn [tail value]
                                          (list 'pair (desugar-expr value) tail))
                                        (desugar-expr trailing)
                                        (reverse fixed))]
              (list '__kotoba_closure_apply (desugar-expr closure) argument-list))))
        lazy-cons
        (do
          (when-not (= 2 (count args))
            (reject! "lazy-cons requires a head and lazy tail expression" form))
          (when *uses-lazy?* (vreset! *uses-lazy?* true))
          (binding [*lifting-lazy-thunk?* true]
            (lift-lambda
             (list 'fn []
                   (list 'pair
                         (list 'fn [] (first args))
                         (list 'fn [] (second args)))))))
        lazy-first
        (do
          (when-not (= 1 (count args))
            (reject! "lazy-first requires one lazy sequence" form))
          (when *uses-lazy?* (vreset! *uses-lazy?* true))
          (let [lazy-seq (synthetic "lazy_seq")
                cell (synthetic "lazy_cell")]
            (list 'let [lazy-seq (desugar-expr (first args))]
                  (list 'if (list '= lazy-seq 0)
                        0
                        (list 'let [cell (list (invoke-dispatcher-name 0) lazy-seq)]
                              (list 'if (list '= cell 0)
                                    0
                                    (list (invoke-dispatcher-name 0)
                                          (list 'pair-first cell))))))))
        lazy-rest
        (do
          (when-not (= 1 (count args))
            (reject! "lazy-rest requires one lazy sequence" form))
          (when *uses-lazy?* (vreset! *uses-lazy?* true))
          (let [lazy-seq (synthetic "lazy_seq")
                cell (synthetic "lazy_cell")]
            (list 'let [lazy-seq (desugar-expr (first args))]
                  (list 'if (list '= lazy-seq 0)
                        0
                        (list 'let [cell (list (invoke-dispatcher-name 0) lazy-seq)]
                              (list 'if (list '= cell 0)
                                    0
                                    (list (invoke-dispatcher-name 0)
                                          (list 'pair-second cell))))))))
        lazy-empty?
        (do
          (when-not (= 1 (count args))
            (reject! "lazy-empty? requires one lazy sequence" form))
          (when *uses-lazy?* (vreset! *uses-lazy?* true))
          (let [lazy-seq (synthetic "lazy_seq")]
            (list 'let [lazy-seq (desugar-expr (first args))]
                  (list 'if (list '= lazy-seq 0)
                        true
                        (list '= (list (invoke-dispatcher-name 0) lazy-seq) 0)))))
        lazy-map
        (do
          (when-not (<= 2 (count args) 5)
            (reject! "lazy-map requires a callback and one to four lazy sequences" form))
          (when *uses-lazy?* (vreset! *uses-lazy?* true))
          (synthesize-lazy-map (first args) (vec (rest args)) form))
        lazy-filter
        (do
          (when-not (= 2 (count args))
            (reject! "lazy-filter requires a unary predicate and lazy sequence" form))
          (when *uses-lazy?* (vreset! *uses-lazy?* true))
          (synthesize-lazy-filter (first args) (second args)))
        take
        (do
          (when-not (= 2 (count args))
            (reject! "take requires a count and lazy sequence" form))
          (when *uses-lazy?* (vreset! *uses-lazy?* true))
          (list lazy-take-helper-name
                (desugar-expr (first args))
                (desugar-expr (second args))))
        drop
        (do
          (when-not (= 2 (count args))
            (reject! "drop requires a count and lazy sequence" form))
          (when *uses-lazy?* (vreset! *uses-lazy?* true))
          (list lazy-drop-helper-name
                (desugar-expr (first args))
                (desugar-expr (second args))))
        document
        (do (when-not (= 1 (count args))
              (reject! "document requires exactly one closed literal tree" form))
            (elaborate-document-literal (first args)))

        ;; ADR-2607150000: `let` gets its own case (previously handled only
        ;; by the generic default case below) for two reasons: (1) bug fix
        ;; -- the default case's `(map desugar-expr args)` called
        ;; desugar-expr on the WHOLE bindings vector as one opaque arg;
        ;; since vectors aren't `seq?`, it passed through UNCHANGED,
        ;; silently skipping map/keyword/nested-vector desugaring inside
        ;; binding VALUES (`(let [m {:a 1}] (get m :a))` failed with
        ;; "value type is outside the safe profile" before this fix,
        ;; confirmed live). (2) destructuring: each binding's PATTERN may
        ;; now be a vector `[a b & rest]` or a map `{:keys [a b]}`, not
        ;; just a plain symbol (destructure-binding above expands either
        ;; into flat symbol bindings). Malformed bindings (not an even
        ;; vector) pass through unchanged so validate-expr's own existing
        ;; "let requires an even binding vector" check still fires with
        ;; its original, clearer error.
        let (let [[bindings & body] args]
              (if (and (vector? bindings) (even? (count bindings)))
                ;; Lower bindings sequentially.  A value may call a closure
                ;; introduced by an earlier binding, while its own pattern is
                ;; deliberately not visible until that value has finished.
                (letfn [(lower-bindings [remaining env contracts lowered]
                          (if-let [[pattern value] (first remaining)]
                            (let [value-contract
                                  (binding [*lexical-callable-contracts* contracts]
                                    (expression-callable-contract value))
                                  expanded
                                  (binding [*lexical-bindings* env
                                            *lexical-callable-contracts* contracts]
                                    (destructure-binding pattern
                                                         (desugar-expr value)))
                                  next-env (into env (map first expanded))
                                  next-contracts
                                  (if (and (symbol? pattern) value-contract)
                                    (assoc contracts pattern value-contract)
                                    contracts)]
                              (lower-bindings (rest remaining) next-env next-contracts
                                              (into lowered expanded)))
                            [(vec (mapcat identity lowered)) env contracts]))]
                  (let [[lowered-bindings body-env body-contracts]
                        (lower-bindings (partition 2 bindings)
                                        *lexical-bindings*
                                        *lexical-callable-contracts* [])]
                    (list* 'let lowered-bindings
                           ;; `mapv`, not bare `map`: forcing must remain in
                           ;; the dynamic extent of the compiler counters.
                           (binding [*lexical-bindings* body-env
                                     *lexical-callable-contracts* body-contracts]
                             (desugar-tail-expressions contextual-result-type body)))))
                ;; Preserve malformed input so validate-expr emits its
                ;; established even-binding-vector diagnostic.
                (list* 'let bindings (mapv desugar-expr body))))

        ;; `do` sequencing: evaluate each subexpression in order, discard all
        ;; but the last (which is the value). Unlike `let`, a `do` subexpression
        ;; is NOT substituted into a body -- so a side-effecting form here runs
        ;; exactly once, in order, even if its result is unused (kernel MMIO
        ;; ops). A single-expression `do` collapses to that expression. `do` is
        ;; kept as a first-class head through desugaring (a nested-`let`
        ;; desugaring would DCE-drop unused side-effecting subexprs).
        do (do (when (empty? args) (reject! "do requires at least one expression" form :kotoba.error/do-empty))
               (if (= 1 (count args))
                 (if contextual-result-type
                   (desugar-result-expr contextual-result-type (first args))
                   (desugar-expr (first args)))
                 (list* 'do (desugar-tail-expressions contextual-result-type args))))

        ;; ADR-2607150000: `loop`/`recur` desugars to a compiler-synthesized
        ;; recursive helper function (like `get`'s __kotoba_map_get, but
        ;; freshly gensym'd per loop occurrence rather than one shared fixed
        ;; name) -- no backend/codegen change, since ordinary recursive
        ;; `defn` calls already work and are already fuel-metered. Any free
        ;; variable the loop body references from its ENCLOSING scope is
        ;; captured as an EXTRA helper parameter (form-free-symbols does a
        ;; purely syntactic scan -- no environment lookup needed: an
        ;; over/under-capture mistake still fails SAFELY later, as a hard
        ;; :unbound-symbol or arity-mismatch compile error from validate-expr,
        ;; never silently wrong runtime behavior). Threading the captured
        ;; values through recur unchanged is handled by replace-recur.
        loop
        (let [[bindings & body] args]
          (when-not (and (vector? bindings) (even? (count bindings))
                         (every? symbol? (take-nth 2 bindings)))
            (reject! "loop requires an even vector of plain-symbol bindings (destructure inside the body instead)" form))
          (when-not (= 1 (count body))
            (reject! "loop requires exactly one body expression (this profile has no `do`)" form))
          (let [loop-names (vec (take-nth 2 bindings))
                loop-inits (mapv desugar-expr (take-nth 2 (rest bindings)))
                desugared-body (desugar-expr (first body))
                captured (vec (sort-by str (form-free-symbols desugared-body (set loop-names))))
                helper-name (symbol (str "__kotoba_loop_" (vswap! *loop-counter* inc)))
                helper-params (into loop-names captured)]
            (when (> (count helper-params) max-parameters)
              (reject! "loop bindings plus captured outer variables exceed this compiler's ABI-supported arity" form))
            (when *pending-loop-helpers*
              (swap! *pending-loop-helpers* conj
                     {:name helper-name :params helper-params
                      :result (or *loop-result-type* :i64) :effects #{}
                      :loop-helper? true
                      :body (replace-recur desugared-body helper-name loop-names captured)}))
            (list* helper-name (concat loop-inits captured))))
        cons (do (when-not (= 2 (count args)) (reject! "cons requires two operands" form))
                 (list 'pair (desugar-expr (first args)) (desugar-expr (second args))))
        first (do (when-not (= 1 (count args)) (reject! "first requires one operand" form))
                  (list 'pair-first (desugar-expr (first args))))
        second (do (when-not (= 1 (count args)) (reject! "second requires one operand" form))
                   (list 'pair-first (list 'pair-second (desugar-expr (first args)))))
        rest (do (when-not (= 1 (count args)) (reject! "rest requires one operand" form))
                 (list 'pair-second (desugar-expr (first args))))
        empty? (do (when-not (= 1 (count args)) (reject! "empty? requires one operand" form))
                   (list '= (desugar-expr (first args)) 0))
        ;; `not`/`not=` desugar through `if`, not through `(= x 0)`: comparisons
        ;; are `:bool`-typed now, so comparing their result to an i64 literal is
        ;; a type error. `if` accepts a boolean or a legacy 0/1 integer test, so
        ;; both an i64 operand and a bool one keep working, and the result is
        ;; `:bool` either way.
        not (do (when-not (= 1 (count args)) (reject! "not requires one operand" form))
                (list 'if (desugar-expr (first args)) false true))
        not= (if (= 2 (count args))
               (list 'if (list '= (desugar-expr (first args))
                                  (desugar-expr (second args)))
                     false true)
               (list 'if (desugar-comparison-chain '= args form) false true))
        zero? (do (when-not (= 1 (count args)) (reject! "zero? requires one operand" form))
                  (list '= (desugar-expr (first args)) 0))
        pos? (do (when-not (= 1 (count args)) (reject! "pos? requires one operand" form))
                 (list '> (desugar-expr (first args)) 0))
        neg? (do (when-not (= 1 (count args)) (reject! "neg? requires one operand" form))
                 (list '< (desugar-expr (first args)) 0))
        = (if (= 2 (count args))
            (list '= (desugar-expr (first args)) (desugar-expr (second args)))
            (desugar-comparison-chain '= args form))
        < (if (= 2 (count args))
            (list '< (desugar-expr (first args)) (desugar-expr (second args)))
            (desugar-comparison-chain '< args form))
        > (if (= 2 (count args))
            (list '> (desugar-expr (first args)) (desugar-expr (second args)))
            (desugar-comparison-chain '> args form))
        <= (if (= 2 (count args))
             (list '<= (desugar-expr (first args)) (desugar-expr (second args)))
             (desugar-comparison-chain '<= args form))
        >= (if (= 2 (count args))
             (list '>= (desugar-expr (first args)) (desugar-expr (second args)))
             (desugar-comparison-chain '>= args form))
        and (desugar-and args)
        or (desugar-or args)
        -> (desugar-thread args form false)
        ->> (desugar-thread args form true)
        as-> (desugar-as-thread args form)
        some-> (desugar-some-thread args form false)
        some->> (desugar-some-thread args form true)
        cond (desugar-cond args form)
        condp (desugar-condp args form)
        cond-> (desugar-cond-thread args form false)
        cond->> (desugar-cond-thread args form true)
        dotimes (desugar-dotimes args form)
        doseq (desugar-doseq args form)
        assert (do
                 (when-not (= 1 (count args))
                   (reject! "assert requires exactly one condition; messages are not supported"
                            form))
                 (list 'if (desugar-bool-expr (first args)) 0 '(quot 1 0)))
        case (desugar-case args form)
        if-let (desugar-binding-if args form false)
        when-let (desugar-binding-if args form true)
        if-some (desugar-binding-some args form false)
        when-some (desugar-binding-some args form true)
        if-not (do (when-not (<= 2 (count args) 3)
                     (reject! "if-not requires then and optional else expressions" form))
                   ;; Negate by swapping the branches, not by `(= test 0)` —
                   ;; the test may now be `:bool`.
                   (let [[test then else] args]
                     (list 'if (desugar-bool-expr test)
                           (if (= 3 (count args)) (desugar-expr else) 0)
                           (desugar-expr then))))
        when-not (do (when (empty? args)
                       (reject! "when-not requires a test expression" form))
                     (let [[test & body] args
                           then (cond
                                  (empty? body) 0
                                  (= 1 (count body)) (desugar-expr (first body))
                                  :else (list* 'do (mapv desugar-expr body)))]
                       ;; Negate by swapping the branches (see if-not).
                       (list 'if (desugar-bool-expr test) 0 then)))
        when (do (when (empty? args)
                   (reject! "when requires a test expression" form))
                 (let [[test & body] args
                       then (if (= 1 (count body))
                              (desugar-expr (first body))
                              (list* 'do (mapv desugar-expr body)))]
                   (list 'if (desugar-bool-expr test) then 0)))
        get (do (when-not (<= 2 (count args) 3)
                  (reject! "get requires a value, a key, and an optional default" form))
                ;; Keep the authored head until the type-directed rewrite can
                ;; select map-get, typed-map-get, or record-get. Every selected
                ;; primitive is still closed and validated before lowering.
                (list* 'get (mapv desugar-expr args)))
        assoc (do (when-not (and (>= (count args) 3) (odd? (count args)))
                    (reject! "assoc requires a map followed by one or more key/value pairs" form))
                  (let [[m & kvs] args]
                    (apply list 'map-assoc (desugar-expr m)
                           (mapcat (fn [[k v]] [(desugar-expr k) (desugar-expr v)])
                                   (partition 2 kvs)))))
        some (do (when-not (= 1 (count args)) (reject! "some requires one i64 operand" form))
                 (list 'option-some (desugar-expr (first args))))
        some? (do (when-not (= 1 (count args)) (reject! "some? requires one option operand" form))
                  (list 'option-some? (desugar-expr (first args))))
        nil? (do (when-not (= 1 (count args)) (reject! "nil? requires one option operand" form))
                 (list 'bool-not (list 'option-some? (desugar-expr (first args)))))
        vector-i64 (do (when (> (count args) value/vector-literal-item-limit)
                         (reject! "vector-i64 exceeds item limit" form))
                       (apply list 'vector-new (map desugar-expr args)))
        bytes (do (when-not (empty? args)
                    (reject! "bytes currently constructs only the canonical empty value" form))
                  '(bytes-empty))
        vector-f64 (do (when (> (count args) value/vector-literal-item-limit)
                         (reject! "vector-f64 exceeds item limit" form))
                       (apply list 'vector-f64-new
                              (map #(desugar-result-expr :f64 %) args)))
        match-result
        (do
          (when-not (= 4 (count args))
            (reject! "match-result requires value, type, ok branch, and err branch" form))
          (let [[result type ok-branch err-branch] args]
            (when-not (and (seq? ok-branch) (= 3 (count ok-branch))
                           (= 'ok (first ok-branch)) (symbol? (second ok-branch)))
              (reject! "match-result requires exactly one (ok binder body) branch" form))
            (when-not (and (seq? err-branch) (= 3 (count err-branch))
                           (= 'err (first err-branch)) (symbol? (second err-branch)))
              (reject! "match-result requires exactly one (err binder body) branch" form))
            (list 'result-match-of type (desugar-expected-value type result)
                  (second ok-branch) (desugar-expr (nth ok-branch 2))
                  (second err-branch) (desugar-expr (nth err-branch 2)))))
        result-match-of
        (do (when-not (= 6 (count args))
              (reject! "result-match-of requires type, value, and two bound branches" form))
            (let [[type value ok-binder ok-body err-binder err-body] args]
              (when-not (and (symbol? ok-binder) (symbol? err-binder))
                (reject! "result-match-of requires symbol binders" form))
              (list 'result-match-of type (desugar-expected-value type value)
                    ok-binder (desugar-expr ok-body)
                    err-binder (desugar-expr err-body))))
        variant-new
        (do (when-not (= 3 (count args))
              (reject! "variant-new requires type, case tag, and payload" form))
            (let [[type tag payload] args
                  canonical-type (canonical-closure-result-type type)
                  payload-type (when (variant-type? canonical-type)
                                 (some (fn [[case-tag case-type]]
                                         (when (= case-tag tag) case-type))
                                       (nth canonical-type 2)))]
              (list 'variant-new type tag
                    (if payload-type
                      (desugar-expected-value payload-type payload)
                      (desugar-expr payload)))))
        match-variant
        (do (when (< (count args) 3)
              (reject! "match-variant requires value, type, and exhaustive branches" form))
            (let [[value type & branches] args]
              (when-not (every? #(and (seq? %) (= 3 (count %))
                                      (keyword? (first %)) (symbol? (second %))) branches)
                (reject! "match-variant branches require (:case binder body)" form))
              (list 'variant-match type (desugar-expected-value type value)
                    (mapv (fn [[tag binder body]] [tag binder (desugar-expr body)]) branches))))
        variant-match
        (do (when-not (= 3 (count args))
              (reject! "variant-match requires type, value, and lowered branches" form))
            (let [[type value branches] args]
              (when-not (and (vector? branches)
                             (every? #(and (vector? %) (= 3 (count %))
                                           (keyword? (first %)) (symbol? (second %)))
                                     branches))
                (reject! "variant-match lowered branches are invalid" form))
              (list 'variant-match type (desugar-expected-value type value)
                    (mapv (fn [[tag binder body]] [tag binder (desugar-expr body)]) branches))))
        option-some-of
        (do (when-not (= 2 (count args)) (reject! "option-some-of requires type and payload" form))
            (list 'option-some-of (first args)
                  (desugar-expected-value (second (first args)) (second args))))
        option-none-of
        (do (when-not (= 1 (count args)) (reject! "option-none-of requires one type" form))
            (list 'option-none-of (first args)))
        option-some?-of
        (do (when-not (= 2 (count args)) (reject! "option-some?-of requires type and value" form))
            (list 'option-some?-of (first args)
                  (desugar-expected-value (first args) (second args))))
        option-value-of
        (do (when-not (= 3 (count args)) (reject! "option-value-of requires type, value, and fallback" form))
            (list 'option-value-of (first args)
                  (desugar-expected-value (first args) (second args))
                  (desugar-expected-value (second (first args)) (nth args 2))))
        option-or
        (do (when-not (= 2 (count args))
              (reject! "option-or requires an option value and a fallback" form))
            ;; Keep this surface head until the type-directed rewrite pass.
            ;; The payload descriptor is intentionally absent from authored
            ;; source and cannot be recovered reliably during syntactic
            ;; desugaring for calls to functions returning [:option T].
            (list 'option-or (desugar-expr (first args))
                  (desugar-expr (second args))))
        ;; `match-option` lowers to this internal form. Nested matches cause
        ;; the enclosing match's recursive desugaring to visit that lowered
        ;; form again, so it must preserve the type descriptor and binder.
        ;; Falling through to generic call desugaring turns descriptor vectors
        ;; into runtime `vector-new` values and makes project linking
        ;; non-idempotent.
        option-match
        (do (when-not (= 5 (count args))
              (reject! "option-match requires type, value, none body, binder, and some body" form))
            (let [[type value none-body binder some-body] args]
              (when-not (symbol? binder)
                (reject! "option-match requires a symbol binder" form))
              (list 'option-match type (desugar-expected-value type value)
                    (desugar-expr none-body) binder (desugar-expr some-body))))
        match-option
        (do (when-not (= 4 (count args))
              (reject! "match-option requires value, type, none branch, and some branch" form))
            (let [[value type none-branch some-branch] args]
              (when-not (and (seq? none-branch) (= 2 (count none-branch))
                             (= 'none (first none-branch)))
                (reject! "match-option requires exactly one (none body) branch" form))
              (when-not (and (seq? some-branch) (= 3 (count some-branch))
                             (= 'some (first some-branch)) (symbol? (second some-branch)))
                (reject! "match-option requires exactly one (some binder body) branch" form))
              (list 'option-match type (desugar-expected-value type value)
                    (desugar-expr (second none-branch)) (second some-branch)
                    (desugar-expr (nth some-branch 2)))))
        hetero-vector
        (do (when (empty? args)
              (reject! "hetero-vector requires a type descriptor" form))
            (let [type (first args)
                  item-types (when (heterogeneous-vector-type? type) (second type))]
              (list* 'hetero-vector-new type
                     (if (= (count item-types) (count (rest args)))
                       (mapv (fn [item-type item]
                               (desugar-expected-value item-type item))
                             item-types (rest args))
                       (mapv desugar-expr (rest args))))))
        typed-list-new
        (do (when (empty? args)
              (reject! "typed-list-new requires a type descriptor" form))
            (let [type (first args)
                  item-type (when (canonical-list-type? type) (second type))]
              (list* 'typed-list-new type
                     (mapv #(if item-type
                              (desugar-expected-value item-type %)
                              (desugar-expr %))
                           (rest args)))))
        hetero-vector-new
        (do (when (empty? args)
              (reject! "hetero-vector-new requires a type descriptor" form))
            (let [type (first args)
                  item-types (when (heterogeneous-vector-type? type) (second type))]
              (list* 'hetero-vector-new type
                     (if (= (count item-types) (count (rest args)))
                       (mapv (fn [item-type item]
                               (desugar-expected-value item-type item))
                             item-types (rest args))
                       (mapv desugar-expr (rest args))))))
        hetero-vector-count
        (do (when-not (= 2 (count args))
              (reject! "hetero-vector-count requires type and value" form))
            (list 'hetero-vector-count (first args)
                  (desugar-expected-value (first args) (second args))))
        hetero-vector-at
        (do (when-not (= 3 (count args))
              (reject! "hetero-vector-at requires type, value, and literal index" form))
            (list 'hetero-vector-at (first args)
                  (desugar-expected-value (first args) (second args)) (nth args 2)))
        hetero-vector-assoc
        (do (when-not (= 4 (count args))
              (reject! "hetero-vector-assoc requires type, value, literal index, and item" form))
            (let [[type value index item] args
                  item-type (when (and (heterogeneous-vector-type? type)
                                       (integer? index)
                                       (<= 0 index)
                                       (< index (count (second type))))
                              (nth (second type) index))]
              (list 'hetero-vector-assoc type
                    (desugar-expected-value type value)
                    index
                    (if item-type
                      (desugar-expected-value item-type item)
                      (desugar-expr item)))))
        hetero-vector-equal
        (do (when-not (= 3 (count args))
              (reject! "hetero-vector-equal requires type and two values" form))
            (list 'hetero-vector-equal (first args)
                  (desugar-expected-value (first args) (second args))
                  (desugar-expected-value (first args) (nth args 2))))
        typed-set
        (do (when (empty? args)
              (reject! "typed-set requires a type descriptor" form))
            (let [type (first args)
                  item-type (when (typed-set-type? type) (second type))]
              (list* 'typed-set-new type
                     (mapv #(if item-type
                              (desugar-expected-value item-type %)
                              (desugar-expr %))
                           (rest args)))))
        typed-set-new
        (do (when (empty? args)
              (reject! "typed-set-new requires a type descriptor" form))
            (let [type (first args)
                  item-type (when (typed-set-type? type) (second type))]
              (list* 'typed-set-new type
                     (mapv #(if item-type
                              (desugar-expected-value item-type %)
                              (desugar-expr %))
                           (rest args)))))
        typed-set-count
        (do (when-not (= 2 (count args))
              (reject! "typed-set-count requires type and value" form))
            (list 'typed-set-count (first args)
                  (desugar-expected-value (first args) (second args))))
        typed-set-contains
        (do (when-not (= 3 (count args))
              (reject! "typed-set-contains requires type, value, and item" form))
            (list 'typed-set-contains (first args)
                  (desugar-expected-value (first args) (second args))
                  (desugar-expected-value
                   (when (typed-set-type? (first args)) (second (first args)))
                   (nth args 2))))
        typed-set-conj
        (do (when-not (= 3 (count args))
              (reject! "typed-set-conj requires type, value, and item" form))
            (list 'typed-set-conj (first args)
                  (desugar-expected-value (first args) (second args))
                  (desugar-expected-value
                   (when (typed-set-type? (first args)) (second (first args)))
                   (nth args 2))))
        typed-set-disj
        (do (when-not (= 3 (count args))
              (reject! "typed-set-disj requires type, value, and item" form))
            (list 'typed-set-disj (first args)
                  (desugar-expected-value (first args) (second args))
                  (desugar-expected-value
                   (when (typed-set-type? (first args)) (second (first args)))
                   (nth args 2))))
        typed-set-equal
        (do (when-not (= 3 (count args))
              (reject! "typed-set-equal requires type and two values" form))
            (list 'typed-set-equal (first args)
                  (desugar-expected-value (first args) (second args))
                  (desugar-expected-value (first args) (nth args 2))))
        typed-set-nth
        (do (when-not (= 3 (count args))
              (reject! "typed-set-nth requires type, value, and index" form))
            (list 'typed-set-nth (first args)
                  (desugar-expected-value (first args) (second args))
                  (desugar-expr (nth args 2))))
        typed-map-new
        (do (when-not (and (seq args) (odd? (count args)))
              (reject! "typed-map-new requires type and key/value pairs" form))
            (let [type (first args)
                  [key-type value-type] (when (canonical-typed-map-type? type)
                                          (rest type))]
              (list* 'typed-map-new type
                     (into []
                           (mapcat (fn [[key item]]
                                     [(if key-type
                                        (desugar-expected-value key-type key)
                                        (desugar-expr key))
                                      (if value-type
                                        (desugar-expected-value value-type item)
                                        (desugar-expr item))]))
                           (partition 2 (rest args))))))
        typed-map-count
        (do (when-not (= 2 (count args))
              (reject! "typed-map-count requires type and value" form))
            (list 'typed-map-count (first args)
                  (desugar-expected-value (first args) (second args))))
        typed-map-contains
        (do (when-not (= 3 (count args))
              (reject! "typed-map-contains requires type, value, and key" form))
            (list 'typed-map-contains (first args)
                  (desugar-expected-value (first args) (second args))
                  (desugar-expected-value
                   (when (canonical-typed-map-type? (first args))
                     (second (first args)))
                   (nth args 2))))
        typed-map-get
        (do (when-not (= 3 (count args))
              (reject! "typed-map-get requires type, value, and key" form))
            (list 'typed-map-get (first args)
                  (desugar-expected-value (first args) (second args))
                  (desugar-expected-value
                   (when (canonical-typed-map-type? (first args))
                     (second (first args)))
                   (nth args 2))))
        typed-map-entry-at
        (do (when-not (= 3 (count args))
              (reject! "typed-map-entry-at requires type, value, and index" form))
            (list 'typed-map-entry-at (first args)
                  (desugar-expected-value (first args) (second args))
                  (desugar-expr (nth args 2))))
        typed-map-assoc
        (do (when-not (= 4 (count args))
              (reject! "typed-map-assoc requires type, value, key, and item" form))
            (list 'typed-map-assoc (first args)
                  (desugar-expected-value (first args) (second args))
                  (desugar-expected-value
                   (when (canonical-typed-map-type? (first args))
                     (second (first args)))
                   (nth args 2))
                  (desugar-expected-value
                   (when (canonical-typed-map-type? (first args))
                     (nth (first args) 2))
                   (nth args 3))))
        typed-map-dissoc
        (do (when-not (= 3 (count args))
              (reject! "typed-map-dissoc requires type, value, and key" form))
            (list 'typed-map-dissoc (first args)
                  (desugar-expected-value (first args) (second args))
                  (desugar-expected-value
                   (when (canonical-typed-map-type? (first args))
                     (second (first args)))
                   (nth args 2))))
        typed-map-equal
        (do (when-not (= 3 (count args))
              (reject! "typed-map-equal requires type and two values" form))
            (list 'typed-map-equal (first args)
                  (desugar-expected-value (first args) (second args))
                  (desugar-expected-value (first args) (nth args 2))))
        record
        (do (when (empty? args)
              (reject! "record requires a type descriptor" form))
            (let [type (canonical-closure-result-type (first args))
                  field-types (mapv second (nth type 2 nil))]
              (list* 'record-new type
                     (map-indexed (fn [index value]
                                    (desugar-expected-value
                                     (nth field-types index nil) value))
                                  (rest args)))))
        record-new
        (do (when (empty? args)
              (reject! "record-new requires a type descriptor" form))
            (let [type (canonical-closure-result-type (first args))
                  field-types (mapv second (nth type 2 nil))]
              (list* 'record-new type
                     (map-indexed (fn [index value]
                                    (desugar-expected-value
                                     (nth field-types index nil) value))
                                  (rest args)))))
        record-get
        (do (when-not (contains? #{2 3} (count args))
              (reject! "record-get requires (value field) or (type value field)" form))
            ;; 2-arity is the projection sugar: the schema is recovered from the
            ;; value's inferred type by rewrite-record-projections, which runs
            ;; after desugar and before validation. Lowering only ever sees the
            ;; canonical 3-arity form.
            (if (= 2 (count args))
              (list 'record-get (desugar-expr (first args)) (second args))
              (let [type (canonical-closure-result-type (first args))]
                (list 'record-get type
                      (desugar-expected-value type (second args)) (nth args 2)))))
        record-assoc
        (do (when-not (= 4 (count args))
              (reject! "record-assoc requires type, value, literal field, and replacement" form))
            (let [type (canonical-closure-result-type (first args))
                  field-type (some (fn [[field field-type]]
                                     (when (= field (nth args 2)) field-type))
                                   (nth type 2 nil))]
              (list 'record-assoc type (desugar-expected-value type (second args))
                    (nth args 2) (desugar-expected-value field-type (nth args 3)))))
        record-equal
        (do (when-not (= 3 (count args))
              (reject! "record-equal requires type and two values" form))
            (let [type (canonical-closure-result-type (first args))]
              (list 'record-equal type
                    (desugar-expected-value type (second args))
                    (desugar-expected-value type (nth args 2)))))
        result-ok-of (do (when-not (= 2 (count args)) (reject! "result-ok-of requires type and payload" form))
                         (list 'result-ok-of (first args)
                               (desugar-expected-value (second (first args)) (second args))))
        result-err-of (do (when-not (= 2 (count args)) (reject! "result-err-of requires type and payload" form))
                          (list 'result-err-of (first args)
                                (desugar-expected-value (nth (first args) 2 nil) (second args))))
        result-ok?-of (do (when-not (= 2 (count args)) (reject! "result-ok?-of requires type and result" form))
                          (list 'result-ok?-of (first args)
                                (desugar-expected-value (first args) (second args))))
        result-value-of (do (when-not (= 3 (count args)) (reject! "result-value-of requires type, result, and fallback" form))
                            (list 'result-value-of (first args)
                                  (desugar-expected-value (first args) (second args))
                                  (desugar-expected-value (second (first args)) (nth args 2))))
        result-error-of (do (when-not (= 3 (count args)) (reject! "result-error-of requires type, result, and fallback" form))
                            (list 'result-error-of (first args)
                                  (desugar-expected-value (first args) (second args))
                                  (desugar-expected-value (nth (first args) 2 nil) (nth args 2))))
        ;; ADR-2607182410: `(cap-call :some/name value)` -> `(cap-call <int>
        ;; (desugar-expr value))`, resolving the keyword against
        ;; capability-registry BEFORE validate-expr/direct-facts ever see the
        ;; form -- everything downstream keeps working exactly as it does
        ;; for the pre-existing literal-int form, byte-for-byte. Only
        ;; intercepts when the FIRST arg is actually a keyword; any other
        ;; shape (correct int form, or a malformed call of any other arity)
        ;; falls through to the identical generic case below, unchanged, so
        ;; validate-expr's own existing arity/range check still fires with
        ;; its original message for every case this desugar step doesn't
        ;; specifically own. `(rest args)` (not a fixed `[value]`
        ;; destructure) preserves whatever argument count followed the
        ;; keyword, so a malformed `(cap-call :kw)` or `(cap-call :kw a b)`
        ;; still reaches validate-expr's "requires ... one value" rejection
        ;; instead of being silently coerced into a well-formed 2-arg call.
        cap-call
        (if (and (seq args) (keyword? (first args)))
          (let [kw (first args)
                elaborated (list* 'cap-call (resolve-capability-keyword! kw form)
                                  (map desugar-expr (rest args)))]
            (attach-source-operation form elaborated kw))
          (apply list op (map desugar-expr args)))
        typed-cap-call
        (if (and (seq args) (keyword? (first args)))
          (let [[capability request-type result-type request & extra] args
                elaborated (list* 'typed-cap-call
                                  (resolve-capability-keyword! capability form)
                                  request-type result-type
                                  (when (<= 4 (count args))
                                    (desugar-expected-value request-type request))
                                  (map desugar-expr extra))]
            (attach-source-operation form elaborated capability))
          (if (and (= 4 (count args))
                   (kotoba-integer? (first args)))
            (let [[capability request-type result-type request] args]
              (list 'typed-cap-call capability request-type result-type
                    (desugar-expected-value request-type request)))
            (apply list op (map desugar-expr args))))
        xorshift32
        (do
          (when-not (= 1 (count args))
            (reject! "xorshift32 requires one state value" form))
          (let [x0 (synthetic "xorshift32_0")
                x1 (synthetic "xorshift32_1")
                x2 (synthetic "xorshift32_2")
                x3 (synthetic "xorshift32_3")]
            (list 'let [x0 (list 'u32-wrap (desugar-expr (first args)))
                         x1 (list 'u32-wrap (list 'i32-xor x0 (list 'i32-shift-left x0 13)))
                         x2 (list 'u32-wrap (list 'i32-xor x1 (list 'u32-shift-right x1 17)))
                         x3 (list 'u32-wrap (list 'i32-xor x2 (list 'i32-shift-left x2 5)))]
                  x3)))
        ;; Product Value ABI v1: surface aliases that lower to ops already
        ;; qualified on every product backend (wasm / KIR / native string slice).
        string-length
        (do (when-not (= 1 (count args))
              (reject! "string-length requires one string" form))
            (list 'string-byte-length
                  (desugar-result-expr :string (first args))))
        string-from-i64
        (do (when-not (= 1 (count args))
              (reject! "string-from-i64 requires one i64" form))
            (list string-from-i64-helper-name (desugar-expr (first args))))
        ;; T4.2: bounded multi-part join → nested string-concat (max 8 parts).
        ;; Works on every backend that already has string-concat (wasm/KIR/js).
        string-join
        (do (when (zero? (count args))
              (reject! "string-join requires a separator string" form))
            (when (> (count (rest args)) 8)
              (reject! "string-join exceeds max 8 parts" form))
            (let [sep (desugar-result-expr :string (first args))
                  parts (mapv #(desugar-result-expr :string %) (rest args))]
              (cond
                (empty? parts) ""
                (= 1 (count parts)) (first parts)
                :else
                (reduce (fn [acc part]
                          (list 'string-concat acc
                                (list 'string-concat sep part)))
                        (first parts)
                        (rest parts)))))
        ;; T4.5/stdlib sugar: inc/dec → arithmetic already dual-backend green.
        inc
        (do (when-not (= 1 (count args))
              (reject! "inc requires one i64" form))
            (list '+ (desugar-expr (first args)) 1))
        dec
        (do (when-not (= 1 (count args))
              (reject! "dec requires one i64" form))
            (list '- (desugar-expr (first args)) 1))
        ;; T4.5: bounded reduce over vector-i64 → zero-charge loop.
        ;; With an explicit init, admits arithmetic, inline, named, or stored
        ;; binary callbacks.  Without an init, the callback must provide the
        ;; Clojure-compatible zero and binary arities: empty vectors invoke
        ;; arity zero, while non-empty vectors start with their first item.
        reduce
        (do
          (when-not (#{2 3} (count args))
            (reject! "reduce requires callback+collection or callback+init+collection" form))
          (if (= 2 (count args))
            (let [[f-form coll-form] args
                  named? (top-level-function-symbol? f-form)
                  _ (when (and named?
                               (not (every? (get *function-arities* f-form) [0 2])))
                      (reject! "named no-init reduce callback must provide arities 0 and 2" f-form))
                  inline? (and (seq? f-form) (= 'fn (first f-form)))
                  _ (when inline?
                      (let [[_ params-or-clause & tail] f-form
                            clauses (when-not (vector? params-or-clause)
                                      (cons params-or-clause tail))
                            arities (when (and (seq clauses)
                                               (every? #(and (seq? %)
                                                             (vector? (first %)))
                                                       clauses))
                                      (mapv #(count (first %)) clauses))]
                        (when-not (= #{0 2} (set arities))
                          (reject! "inline no-init reduce callback must define exactly [] and [acc value] arities"
                                   f-form))))
                  callback* (desugar-expr (if named? (list 'fn-ref f-form) f-form))
                  coll* (desugar-result-expr :vector-i64 coll-form)
                  callback (synthetic "reduce_callback")
                  v (synthetic "reduce_v")
                  i (synthetic "reduce_i")
                  acc (synthetic "reduce_acc")]
              (desugar-expr
               (list 'let [callback callback* v coll*]
                     (list 'if (list '= (list 'vector-count v) 0)
                           (list (invoke-dispatcher-name 0) callback)
                           (list 'loop [i 1 acc (list 'vector-at v 0)]
                                 (list 'if (list '< i (list 'vector-count v))
                                       (list 'recur
                                             (list '+ i 1)
                                             (list (invoke-dispatcher-name 2) callback acc
                                                   (list 'vector-at v i)))
                                       acc))))))
            (let [[f-form init-form coll-form] args
                  init* (desugar-expr init-form)
                  coll* (desugar-result-expr :vector-i64 coll-form)
                  v (synthetic "reduce_v")
                  i (synthetic "reduce_i")
                  acc (synthetic "reduce_acc")
                  primitive? (and (symbol? f-form)
                                  (not (contains? *lexical-bindings* f-form))
                                  (contains? '#{+ - * bit-and bit-or bit-xor} f-form))
                  named? (top-level-function-symbol? f-form)
                  stored? (not (or primitive? named?
                                   (and (seq? f-form) (= 'fn (first f-form)))))
                  callback (when stored? (synthetic "reduce_callback"))
                  step
                  (cond
                    primitive?
                    (list f-form acc (list 'vector-at v i))

                    (and (seq? f-form) (= 'fn (first f-form)))
                    (let [[_ params & body] f-form]
                      (when-not (and (vector? params) (= 2 (count params))
                                     (every? symbol? params)
                                     (= 1 (count body)))
                        (reject! "reduce fn must be (fn [acc x] single-expr)" f-form))
                      (let [[a b] params]
                        (list 'let [a acc
                                    b (list 'vector-at v i)]
                              (binding [*lexical-bindings*
                                        (into *lexical-bindings* params)]
                                (desugar-expr (first body))))))

                    ;; Named binary module function (fail-closed if unbound / wrong arity).
                    named?
                    (list f-form acc (list 'vector-at v i))

                    :else
                    (list (invoke-dispatcher-name 2) callback acc
                          (list 'vector-at v i)))]
              ;; Re-enter desugar so loop → __kotoba_loop_N under *pending-loop-helpers*.
              (desugar-expr
               (list 'let (vec (concat (when stored? [callback f-form]) [v coll*]))
                     (list 'loop [i 0 acc init*]
                           (list 'if (list '< i (list 'vector-count v))
                                 (list 'recur (list '+ i 1) step)
                                 acc)))))))
        ;; Bounded eager map over one to five vector-i64 sources.  One/two
        ;; sources stay direct for stable KIR; three-to-five source handles
        ;; share one typed heterogeneous-vector state value, so synthesized
        ;; loop helpers stay inside the five-word ABI even with a callback.
        map
        (do
          (when-not (<= 2 (count args) 6)
            (reject! "map requires a callback and one to five vector-i64 collections" form))
          (let [[f-form & coll-forms] args
                n-colls (count coll-forms)
                top-level? (top-level-function-symbol? f-form)
                primitive? (and (= 1 n-colls)
                                (symbol? f-form)
                                (not (contains? *lexical-bindings* f-form))
                                (contains? '#{inc dec} f-form))
                inline? (and (seq? f-form) (= 'fn (first f-form)))
                stored? (not (or top-level? primitive? inline?))
                _ (when (and top-level?
                             (not (contains? (get *function-arities* f-form) n-colls)))
                    (reject! "named map callback does not support the source arity" f-form))
                inline-parts
                (when inline?
                  (let [[_ params & body] f-form]
                    (when-not (and (vector? params)
                                   (= n-colls (count params))
                                   (every? symbol? params)
                                   (= (count params) (count (distinct params)))
                                   (= 1 (count body)))
                      (reject! (str n-colls
                                    "-source map fn requires matching unique parameters and one expression")
                               f-form))
                    [params (first body)]))
                _ (when (and stored? (> n-colls 4))
                    (reject! "stored map callbacks support at most four sources" f-form))
                packed? (> n-colls 2)
                source-type [:vector (vec (repeat n-colls :vector-i64))]
                source-values (mapv #(desugar-result-expr :vector-i64 %) coll-forms)
                sources (when packed? (synthetic "map_sources"))
                direct-sources (when-not packed?
                                 (mapv #(synthetic (str "map_source_" %))
                                       (range n-colls)))
                callback (when stored? (synthetic "map_callback"))
                i (synthetic "map_i")
                acc (synthetic "map_acc")
                source-at (fn [index]
                            (if packed?
                              (list 'hetero-vector-at source-type sources index)
                              (nth direct-sources index)))
                items (mapv (fn [index]
                              (list 'vector-at (source-at index) i))
                            (range n-colls))
                mapped
                (cond
                  (and primitive? (= 'inc f-form)) (list '+ (first items) 1)
                  (and primitive? (= 'dec f-form)) (list '- (first items) 1)
                  inline?
                  (let [[params body] inline-parts]
                    (list 'let (vec (mapcat vector params items))
                          (binding [*lexical-bindings*
                                    (into *lexical-bindings* params)]
                            (desugar-expr body))))
                  top-level? (apply list f-form items)
                  :else (apply list (invoke-dispatcher-name n-colls)
                               callback items))
                exhausted (apply list 'or
                                 (map-indexed
                                  (fn [index _]
                                    (list '>= i
                                          (list 'vector-count (source-at index))))
                                  coll-forms))
                source-bindings
                (if packed?
                  [sources (apply list 'hetero-vector source-type source-values)]
                  (vec (mapcat vector direct-sources source-values)))]
            (binding [*loop-result-type* :vector-i64]
              (desugar-expr
               (list 'let
                     (vec (concat (when stored? [callback f-form])
                                  source-bindings))
                     (list 'loop [i 0 acc (list 'vector-i64)]
                           (list 'if exhausted
                                 acc
                                 (list 'recur (list '+ i 1)
                                       (list 'vector-conj acc mapped)))))))))
        ;; T4.5: bounded filter over vector-i64 → zero-charge loop + vector-conj.
        ;; (filter (fn [x] pred) coll) or (filter named-pred coll).
        filter
        (do
          (when-not (= 2 (count args))
            (reject! "filter requires pred and one vector-i64 collection" form))
          (let [[p-form coll-form] args
                coll* (desugar-result-expr :vector-i64 coll-form)
                v (synthetic "filter_v")
                i (synthetic "filter_i")
                acc (synthetic "filter_acc")
                x (synthetic "filter_x")
                named? (top-level-function-symbol? p-form)
                stored? (not (or named?
                                 (and (seq? p-form) (= 'fn (first p-form)))))
                callback (when stored? (synthetic "filter_callback"))
                pred-body
                (cond
                  (and (seq? p-form) (= 'fn (first p-form)))
                  (let [[_ params & body] p-form]
                    (when-not (and (vector? params) (= 1 (count params))
                                   (every? symbol? params)
                                   (= 1 (count body)))
                      (reject! "filter pred must be (fn [x] single-expr)" p-form))
                    (let [[px] params]
                      ;; Bind user param to element; desugar body in that scope.
                      (list 'let [px x]
                            (binding [*lexical-bindings*
                                      (into *lexical-bindings* params)]
                              (desugar-expr (first body))))))

                  named?
                  (list p-form x)

                  :else
                  (list (invoke-dispatcher-name :bool 1) callback x))]
            (binding [*loop-result-type* :vector-i64]
              (desugar-expr
               (list 'let (vec (concat (when stored? [callback p-form]) [v coll*]))
                     (list 'loop [i 0 acc (list 'vector-i64)]
                           (list 'if (list '< i (list 'vector-count v))
                                 (list 'let [x (list 'vector-at v i)]
                                       (list 'recur (list '+ i 1)
                                             (list 'if pred-body
                                                   (list 'vector-conj acc x)
                                                   acc)))
                                 acc)))))))
        ;; W1: friendly namespaced ops elaborate before validation sees them.
        (if-let [kw (capability-keyword-for-symbol op)]
          (elaborate-named-operation form op kw args)
          (if (and (symbol? op) (namespace op))
            (reject! (str "named operation " (pr-str op)
                          " is not a registered capability")
                     form)
            (apply list op (map desugar-expr args)))))))))

(defn- desugar-expr [form]
  (let [contextual-result-type *contextual-closure-result-type*
        result (binding [*contextual-closure-result-type* nil]
                 (desugar-expr* form contextual-result-type))
        location (select-keys (meta form)
                              [:line :column :end-line :end-column :offset :end-offset])]
    (if (and (seq location) (or (coll? result) (symbol? result)))
      (with-meta result (merge (meta result) location))
      result)))

(defn- valid-name? [value]
  (and (simple-symbol? value) (<= (count (name value)) max-symbol-chars)))

(defn- charge-node! [budget form]
  (when (> (vswap! budget inc) max-expression-nodes)
    (reject! "program expression budget exhausted" form)))

(declare validate-expr)

(defn- validate-bindings [bindings locals functions depth budget]
  (when-not (and (vector? bindings) (even? (count bindings)))
    (reject! "let requires an even binding vector" bindings))
  (when-not (= (count (take-nth 2 bindings)) (count (distinct (take-nth 2 bindings))))
    (reject! "duplicate let binding" bindings))
  (when (> (quot (count bindings) 2) max-bindings)
    (reject! "let binding count exceeds admission limit" bindings))
  (loop [pairs (partition 2 bindings) env locals]
    (if-let [[name value] (first pairs)]
      (do
        (when-not (and (valid-name? name) (not (contains? forbidden-heads name)))
          (reject! "invalid local binding" name))
        (validate-expr value env functions (inc depth) budget)
        (recur (next pairs) (conj env name)))
      env)))

(defn validate-expr [form locals functions depth budget]
  (charge-node! budget form)
  (when (> depth 256)
    (reject! "expression nesting exceeds admission limit" form))
  (cond
    (kotoba-integer? form)
    #?(:clj (if (<= Long/MIN_VALUE form Long/MAX_VALUE) form
                (reject! "integer literal is outside i64" form))
       :cljs (if (i64/in-i64-range? form) form
                 (reject! "integer literal is outside i64" form)))
    (string? form)
    (try
      (value/bounded-string! form value/string-literal-byte-limit)
      form
      (catch #?(:clj Exception :cljs :default) error
        (reject! (ex-message error) form)))
    (keyword? form)
    (try
      (value/bounded-keyword! form value/keyword-value-byte-limit)
      form
      (catch #?(:clj Exception :cljs :default) error
        (reject! (ex-message error) form)))
    (boolean? form) form
    (symbol? form) (if (contains? locals form) form
                       (reject! "unbound or dynamic symbol is forbidden" form))
    (seq? form)
    (let [[op & args] form]
      (when-not (simple-symbol? op) (reject! "computed or namespaced calls are forbidden" form))
      (when (or (contains? forbidden-heads op) (re-find #"[.]" (name op)))
        (reject! "dynamic loading, interop, mutation, and metaprogramming are forbidden"
                 form :kotoba.error/ambient-forbidden))
      (cond
        (= op 'let)
        (let [[bindings & body] args]
          (when-not (= 1 (count body)) (reject! "let requires one result expression" form))
          (validate-expr (first body)
                         (validate-bindings bindings locals functions depth budget)
                         functions (inc depth) budget))

        (= op 'if)
        (do (when-not (= 3 (count args)) (reject! "if requires test, then, else" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (= op 'do)
        (do (when (empty? args) (reject! "do requires at least one expression" form :kotoba.error/do-empty))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (= op 'cap-call)
        (let [[cap-id value :as call-args] args]
          (when-not (and (= 2 (count call-args)) (kotoba-integer? cap-id) (<= 0 cap-id 255))
            (reject! "cap-call requires a literal capability id in [0,255] and one value" form))
          (validate-expr value locals functions (inc depth) budget))

        (= op 'typed-cap-call)
        (let [[cap-id request-type result-type request :as call-args] args]
          (when-not (and (= 4 (count call-args)) (kotoba-integer? cap-id) (<= 0 cap-id 255))
            (reject! "typed-cap-call requires a literal capability id in [0,255], request type, result type, and one request" form))
          (validate-value-type! request-type)
          (validate-value-type! result-type)
          (validate-expr request locals functions (inc depth) budget))

        (contains? arithmetic op)
            (do (when (or (empty? args) (and (contains? '#{quot bit-xor bit-and bit-or} op) (not= 2 (count args))))
              (reject! "invalid arithmetic arity" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? i64-operations op)
        (do (when-not (= (get i64-operations op) (count args))
              (reject! "i64 operation arity mismatch" form))
            (when (contains? '#{i64-shift-left i64-shift-right u64-shift-right} op)
              (when-not (and (kotoba-integer? (second args)) (<= 0 (second args) 63))
                (reject! "i64 shift count must be an integer literal in [0,63]" form)))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? i32-operations op)
        (do (when-not (= (get i32-operations op) (count args))
              (reject! "i32 operation arity mismatch" form))
            (when (contains? '#{i32-shift-left i32-shift-right u32-shift-right} op)
              (when-not (and (kotoba-integer? (second args)) (<= 0 (second args) 31))
                (reject! "i32 shift count must be an integer literal in [0,31]" form)))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? comparisons op)
        (do (when-not (= 2 (count args)) (reject! "comparison requires two operands" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? heap-operations op)
        (do (when-not (= (get heap-operations op) (count args))
              (reject! "heap operation arity mismatch" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? kgraph-operations op)
        (do (when-not (= (get kgraph-operations op) (count args))
              (reject! "kgraph operation arity mismatch" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? string-operations op)
        (do (when-not (= (get string-operations op) (count args))
              (reject! "string operation arity mismatch" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? xml-operations op)
        (do (when-not (= (get xml-operations op) (count args))
              (reject! "XML operation arity mismatch" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? decimal-operations op)
        (do (when-not (= (get decimal-operations op) (count args))
              (reject! "decimal operation arity mismatch" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? f64-operations op)
        (do (when-not (= (get f64-operations op) (count args))
              (reject! "f64 operation arity mismatch" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? f32-operations op)
        (do (when-not (= (get f32-operations op) (count args))
              (reject! "f32 operation arity mismatch" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? typed-map-operations op)
        (do (case op
              map-new (when (odd? (count args))
                        (reject! "map-new requires keyword/value pairs" form))
              map-get (when-not (= 3 (count args))
                        (reject! "map-get requires map, keyword, and default" form))
              map-assoc (when-not (and (>= (count args) 3) (odd? (count args)))
                          (reject! "map-assoc requires map and keyword/value pairs" form)))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? typed-safe-value-operations op)
        (do (when-not (= (get typed-safe-value-operations op) (count args))
              (reject! "typed safe-value operation arity mismatch" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (= op 'typed-list-new)
        (let [[type & items] args]
          (validate-value-type! type)
          (when-not (canonical-list-type? type)
            (reject! "typed list constructor requires [:list item-type]" form))
          (when (> (count items) max-list-items)
            (reject! "typed list constructor exceeds item limit" form))
          (doseq [item items]
            (validate-expr item locals functions (inc depth) budget)))

        (= op 'bytes-empty)
        (when-not (empty? args)
          (reject! "bytes-empty does not accept operands" form))

        (= op 'typed-set-new)
        (let [[type & items] args]
          (validate-value-type! type)
          (when-not (typed-set-type? type)
            (reject! "typed set constructor requires [:set item-type]" form))
          (when (> (count items) max-typed-set-items)
            (reject! "typed set constructor exceeds item limit" form))
          (doseq [item items]
            (validate-expr item locals functions (inc depth) budget)))

        (= op 'typed-set-count)
        (let [[type value] args]
          (when-not (= 2 (count args)) (reject! "typed set count shape is invalid" form))
          (validate-value-type! type)
          (when-not (typed-set-type? type)
            (reject! "typed set count requires [:set item-type]" form))
          (validate-expr value locals functions (inc depth) budget))

        (contains? '#{typed-set-contains typed-set-conj typed-set-disj} op)
        (let [[type value item] args]
          (when-not (= 3 (count args)) (reject! "typed set operation shape is invalid" form))
          (validate-value-type! type)
          (when-not (typed-set-type? type)
            (reject! "typed set operation requires [:set item-type]" form))
          (validate-expr value locals functions (inc depth) budget)
          (validate-expr item locals functions (inc depth) budget))

        (= op 'typed-set-equal)
        (let [[type left right] args]
          (when-not (= 3 (count args)) (reject! "typed set equality shape is invalid" form))
          (validate-value-type! type)
          (when-not (typed-set-type? type)
            (reject! "typed set equality requires [:set item-type]" form))
          (validate-expr left locals functions (inc depth) budget)
          (validate-expr right locals functions (inc depth) budget))

        (= op 'typed-set-nth)
        (let [[type value index] args]
          (when-not (= 3 (count args)) (reject! "typed set nth shape is invalid" form))
          (validate-value-type! type)
          (when-not (typed-set-type? type)
            (reject! "typed set nth requires [:set item-type]" form))
          (validate-expr value locals functions (inc depth) budget)
          (validate-expr index locals functions (inc depth) budget))

        (= op 'typed-map-new)
        (let [[type & entries] args]
          (validate-value-type! type)
          (when-not (and (canonical-typed-map-type? type)
                         (even? (count entries))
                         (<= (/ (count entries) 2) max-typed-map-entries))
            (reject! "typed map constructor shape or entry limit is invalid" form))
          (doseq [entry entries]
            (validate-expr entry locals functions (inc depth) budget)))

        (= op 'typed-map-count)
        (let [[type value] args]
          (when-not (= 2 (count args)) (reject! "typed map count shape is invalid" form))
          (validate-value-type! type)
          (when-not (canonical-typed-map-type? type)
            (reject! "typed map count requires [:map key-type value-type]" form))
          (validate-expr value locals functions (inc depth) budget))

        (contains? '#{typed-map-contains typed-map-get typed-map-dissoc} op)
        (let [[type value key] args]
          (when-not (= 3 (count args)) (reject! "typed map operation shape is invalid" form))
          (validate-value-type! type)
          (when-not (canonical-typed-map-type? type)
            (reject! "typed map operation requires [:map key-type value-type]" form))
          (validate-expr value locals functions (inc depth) budget)
          (validate-expr key locals functions (inc depth) budget))

        (= op 'typed-map-entry-at)
        (let [[type value index] args]
          (when-not (= 3 (count args)) (reject! "typed map entry projection shape is invalid" form))
          (validate-value-type! type)
          (when-not (canonical-typed-map-type? type)
            (reject! "typed map entry projection requires [:map key-type value-type]" form))
          (validate-expr value locals functions (inc depth) budget)
          (validate-expr index locals functions (inc depth) budget))

        (= op 'typed-map-assoc)
        (let [[type map-value key item] args]
          (when-not (= 4 (count args)) (reject! "typed map assoc shape is invalid" form))
          (validate-value-type! type)
          (when-not (canonical-typed-map-type? type)
            (reject! "typed map assoc requires [:map key-type value-type]" form))
          (doseq [item-form [map-value key item]]
            (validate-expr item-form locals functions (inc depth) budget)))

        (= op 'typed-map-equal)
        (let [[type left right] args]
          (when-not (= 3 (count args)) (reject! "typed map equality shape is invalid" form))
          (validate-value-type! type)
          (when-not (canonical-typed-map-type? type)
            (reject! "typed map equality requires [:map key-type value-type]" form))
          (validate-expr left locals functions (inc depth) budget)
          (validate-expr right locals functions (inc depth) budget))

        (= op 'record-new)
        (let [[type & values] args
              fields (when (record-type? type) (nth type 2))]
          (validate-value-type! type)
          (when-not (and (record-type? type) (= (count fields) (count values)))
            (reject! "record constructor must exactly match its descriptor" form))
          (doseq [item values]
            (validate-expr item locals functions (inc depth) budget)))

        (= op 'record-get)
        (let [[type value field] args
              fields (when (record-type? type) (nth type 2))]
          (when-not (= 3 (count args)) (reject! "record projection shape is invalid" form))
          (validate-value-type! type)
          (when-not (and (record-type? type) (keyword? field) (some #{field} (map first fields)))
            (reject! "record field must be a declared keyword literal" form))
          (validate-expr value locals functions (inc depth) budget))

        (= op 'record-assoc)
        (let [[type value field replacement] args
              fields (when (record-type? type) (nth type 2))]
          (when-not (= 4 (count args)) (reject! "record replacement shape is invalid" form))
          (validate-value-type! type)
          (when-not (and (record-type? type) (keyword? field) (some #{field} (map first fields)))
            (reject! "record field must be a declared keyword literal" form))
          (validate-expr value locals functions (inc depth) budget)
          (validate-expr replacement locals functions (inc depth) budget))

        (= op 'record-equal)
        (let [[type left right] args]
          (when-not (= 3 (count args)) (reject! "record equality shape is invalid" form))
          (validate-value-type! type)
          (when-not (record-type? type)
            (reject! "record equality requires a record descriptor" form))
          (validate-expr left locals functions (inc depth) budget)
          (validate-expr right locals functions (inc depth) budget))

        (= op 'hetero-vector-new)
        (let [[type & items] args
              item-types (when (heterogeneous-vector-type? type) (second type))]
          (validate-value-type! type)
          (when-not (and (heterogeneous-vector-type? type)
                         (= (count item-types) (count items)))
            (reject! "heterogeneous vector constructor must exactly match its descriptor" form))
          (doseq [item items]
            (validate-expr item locals functions (inc depth) budget)))

        (= op 'hetero-vector-count)
        (let [[type value] args]
          (when-not (= 2 (count args))
            (reject! "heterogeneous vector count shape is invalid" form))
          (validate-value-type! type)
          (when-not (heterogeneous-vector-type? type)
            (reject! "heterogeneous vector count requires a vector descriptor" form))
          (validate-expr value locals functions (inc depth) budget))

        (contains? '#{hetero-vector-at hetero-vector-assoc} op)
        (let [[type value index item] args
              expected (if (= op 'hetero-vector-at) 3 4)
              item-types (when (heterogeneous-vector-type? type) (second type))]
          (when-not (= expected (count args))
            (reject! "heterogeneous vector indexed operation shape is invalid" form))
          (validate-value-type! type)
          (when-not (heterogeneous-vector-type? type)
            (reject! "heterogeneous vector operation requires a vector descriptor" form))
          (heterogeneous-vector-index! index item-types form)
          (validate-expr value locals functions (inc depth) budget)
          (when (= op 'hetero-vector-assoc)
            (validate-expr item locals functions (inc depth) budget)))

        (= op 'hetero-vector-equal)
        (let [[type left right] args]
          (when-not (= 3 (count args))
            (reject! "heterogeneous vector equality shape is invalid" form))
          (validate-value-type! type)
          (when-not (heterogeneous-vector-type? type)
            (reject! "heterogeneous vector equality requires a vector descriptor" form))
          (validate-expr left locals functions (inc depth) budget)
          (validate-expr right locals functions (inc depth) budget))

        (= op 'option-none-of)
        (do (when-not (= 1 (count args)) (reject! "option-none-of shape is invalid" form))
            (validate-value-type! (first args))
            (when-not (generic-option-type? (first args))
              (reject! "option-none-of requires [:option payload-type]" form)))

        (contains? '#{option-some-of option-some?-of} op)
        (let [[type value] args]
          (when-not (= 2 (count args)) (reject! "generic option operation shape is invalid" form))
          (validate-value-type! type)
          (when-not (generic-option-type? type)
            (reject! "generic option operation requires [:option payload-type]" form))
          (validate-expr value locals functions (inc depth) budget))

        (= op 'option-value-of)
        (let [[type value fallback] args]
          (when-not (= 3 (count args)) (reject! "option-value-of shape is invalid" form))
          (validate-value-type! type)
          (when-not (generic-option-type? type)
            (reject! "option-value-of requires [:option payload-type]" form))
          (validate-expr value locals functions (inc depth) budget)
          (validate-expr fallback locals functions (inc depth) budget))

        (= op 'option-match)
        (let [[type value none-body some-name some-body] args]
          (when-not (= 5 (count args)) (reject! "option-match shape is invalid" form))
          (validate-value-type! type)
          (when-not (and (generic-option-type? type) (symbol? some-name)
                         (nil? (namespace some-name)))
            (reject! "option-match requires option type and unqualified some binder" form))
          (validate-expr value locals functions (inc depth) budget)
          (validate-expr none-body locals functions (inc depth) budget)
          (validate-expr some-body (conj locals some-name) functions (inc depth) budget))

        (= op 'variant-new)
        (let [[type tag payload] args]
          (when-not (= 3 (count args)) (reject! "variant-new shape is invalid" form))
          (validate-value-type! type)
          (when-not (and (variant-type? type) (keyword? tag))
            (reject! "variant-new requires variant descriptor and keyword tag" form))
          (validate-expr payload locals functions (inc depth) budget))

        (= op 'variant-match)
        (let [[type value branches] args
              cases (when (variant-type? type) (nth type 2))]
          (when-not (= 3 (count args)) (reject! "variant-match shape is invalid" form))
          (validate-value-type! type)
          (when-not (and (variant-type? type) (vector? branches)
                         (= (mapv first cases) (mapv first branches))
                         (every? #(and (vector? %) (= 3 (count %))
                                       (symbol? (second %)) (nil? (namespace (second %)))) branches))
            (reject! "variant match must exactly cover declared cases in order" form))
          (validate-expr value locals functions (inc depth) budget)
          (doseq [[_ binder body] branches]
            (validate-expr body (conj locals binder) functions (inc depth) budget)))

        (= op 'result-match-of)
        (let [[type result ok-name ok-body err-name err-body] args]
          (when-not (= 6 (count args))
            (reject! "result-match-of shape is invalid" form))
          (when-not (parametric-result-type? type)
            (reject! "result match requires [:result ok-type err-type]" form))
          (validate-value-type! type)
          (when-not (and (symbol? ok-name) (nil? (namespace ok-name))
                         (symbol? err-name) (nil? (namespace err-name)))
            (reject! "result match binders must be unqualified symbols" form))
          (validate-expr result locals functions (inc depth) budget)
          (validate-expr ok-body (conj locals ok-name) functions (inc depth) budget)
          (validate-expr err-body (conj locals err-name) functions (inc depth) budget))

        (contains? parametric-result-operations op)
        (do (when-not (= (get parametric-result-operations op) (count args))
              (reject! "parametric result operation arity mismatch" form))
            (when-not (parametric-result-type? (first args))
              (reject! "parametric result operation requires [:result ok-type err-type]" form))
            (validate-value-type! (first args))
            (doseq [arg (rest args)]
              (validate-expr arg locals functions (inc depth) budget)))

        (= op 'vector-new)
        (do (when (> (count args) value/vector-literal-item-limit)
              (reject! "vector-new exceeds item limit" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (= op 'vector-f64-new)
        (do (when (> (count args) value/vector-literal-item-limit)
              (reject! "vector-f64-new exceeds item limit" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? typed-vector-operations op)
        (do (when-not (= (get typed-vector-operations op) (count args))
              (reject! "typed vector operation arity mismatch" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? typed-f64-vector-operations op)
        (do (when-not (= (get typed-f64-vector-operations op) (count args))
              (reject! "typed f64 vector operation arity mismatch" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? compact-graph-operations op)
        (do (when-not (= (get compact-graph-operations op) (count args))
              (reject! "compact graph operation arity mismatch" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? document-fixed-operations op)
        (do (when-not (= (get document-fixed-operations op) (count args))
              (reject! "document operation arity mismatch" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? '#{document-vector document-list document-set} op)
        (do (when (> (count args) value/document-container-item-limit)
              (reject! "document sequence exceeds item limit" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (= op 'document-map)
        (do (when (odd? (count args))
              (reject! "document-map requires key/value pairs" form))
            (when (> (quot (count args) 2) value/document-container-item-limit)
              (reject! "document-map exceeds entry limit" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? kernel-memory-operations op)
        (do (when-not (= (get kernel-memory-operations op) (count args))
              (reject! "kernel memory operation arity mismatch" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? kernel-privileged-operations op)
        (do (when-not (= (get kernel-privileged-operations op) (count args))
              (reject! "kernel privileged operation arity mismatch" form))
            (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        (contains? functions op)
        (let [expected (count (get functions op))]
          (when-not (= expected (count args))
            (reject! "function call arity mismatch" form))
          (doseq [arg args] (validate-expr arg locals functions (inc depth) budget)))

        :else (reject! "operation has no admitted lowering" form))
      form)
    :else (reject! "value type is outside the safe profile" form)))

(defn- nominal-type-identity [type]
  (cond
    (schema-ref-type? type) (second type)
    (or (record-type? type) (variant-type? type)) (second type)
    :else nil))

(defn- same-expression-type?
  "Exact structural equality remains the default. A closed-schema reference
  and its fully declared nominal descriptor are interchangeable only by the
  same qualified identity; analyze verifies every inline descriptor carrying
  a declared identity against the namespace's authoritative schema first."
  [actual expected]
  (or (= actual expected)
      (and (or (schema-ref-type? actual) (schema-ref-type? expected))
           (= (nominal-type-identity actual)
              (nominal-type-identity expected))
           (some? (nominal-type-identity actual)))))

(defn- require-expression-type! [actual expected form]
  (when-not (same-expression-type? actual expected)
    (let [type-text #(if (keyword? %) (name %) (pr-str %))]
      (reject! (str "expression type mismatch: expected " (type-text expected)
                    ", got " (type-text actual))
               form))))

(declare infer-expression-type)

(defn- infer-call-type [op args locals signatures]
  (let [types (mapv #(infer-expression-type % locals signatures) args)]
    (cond
      (contains? arithmetic op)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :i64 arg))
          :i64)

      (contains? i64-operations op)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :i64 arg))
          :i64)

      (contains? i32-operations op)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :i64 arg))
          :i64)

      (= op '=)
      (do (when-not (= (first types) (second types))
            (reject! "equality operands must have the same value type" args))
          (when-not (or (contains? #{:i64 :keyword :bool :option-i64 :result-i64 :vector-i64} (first types))
                        (parametric-result-type? (first types)))
            (reject! (str "equality type is outside the safe value profile"
                          (condp = (first types)
                            :string " -- use string=? for string equality"
                            :f64 (str " -- use f64-eq for IEEE equality (returns"
                                      " :bool; NaN is never equal), or compare"
                                      " f64-to-bits values with = for bitwise"
                                      " identity")
                            ""))
                     args))
          :bool)

      (= op 'bool-not)
      (do (require-expression-type! (first types) :bool (first args)) :bool)

      (= op 'option-some)
      (do (require-expression-type! (first types) :i64 (first args)) :option-i64)

      (= op 'option-none) :option-i64

      (= op 'option-some?)
      (do (require-expression-type! (first types) :option-i64 (first args)) :bool)

      (= op 'option-value)
      (do (require-expression-type! (first types) :option-i64 (first args))
          (require-expression-type! (second types) :i64 (second args))
          :i64)

      (contains? '#{result-ok result-err} op)
      (do (require-expression-type! (first types) :i64 (first args)) :result-i64)

      (= op 'result-ok?)
      (do (require-expression-type! (first types) :result-i64 (first args)) :bool)

      (contains? '#{result-value result-error} op)
      (do (require-expression-type! (first types) :result-i64 (first args))
          (require-expression-type! (second types) :i64 (second args))
          :i64)

      (= op 'vector-new)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :i64 arg))
          :vector-i64)

      (= op 'vector-count)
      (do
        (when-not (or (= :vector-i64 (first types))
                      (canonical-list-type? (first types)))
          (require-expression-type! (first types) :vector-i64 (first args)))
        :i64)

      (= op 'vector-get)
      (do (require-expression-type! (nth types 0) :vector-i64 (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1))
          (require-expression-type! (nth types 2) :i64 (nth args 2)) :i64)

      (= op 'vector-at)
      (do (require-expression-type! (nth types 0) :vector-i64 (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1)) :i64)

      (= op 'vector-drop)
      (do (require-expression-type! (nth types 0) :vector-i64 (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1)) :vector-i64)

      (= op 'vector-assoc)
      (do (require-expression-type! (nth types 0) :vector-i64 (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1))
          (require-expression-type! (nth types 2) :i64 (nth args 2)) :vector-i64)

      (= op 'vector-conj)
      (do (require-expression-type! (nth types 0) :vector-i64 (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1)) :vector-i64)

      (= op 'vector-f64-new)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :f64 arg))
          :vector-f64)

      (= op 'vector-f64-count)
      (do (require-expression-type! (first types) :vector-f64 (first args)) :i64)

      (= op 'vector-f64-get)
      (do (require-expression-type! (nth types 0) :vector-f64 (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1))
          (require-expression-type! (nth types 2) :f64 (nth args 2)) :f64)

      (= op 'vector-f64-at)
      (do (require-expression-type! (nth types 0) :vector-f64 (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1)) :f64)

      (= op 'vector-f64-drop)
      (do (require-expression-type! (nth types 0) :vector-f64 (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1)) :vector-f64)

      (= op 'vector-f64-assoc)
      (do (require-expression-type! (nth types 0) :vector-f64 (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1))
          (require-expression-type! (nth types 2) :f64 (nth args 2)) :vector-f64)

      (= op 'vector-f64-conj)
      (do (require-expression-type! (nth types 0) :vector-f64 (nth args 0))
          (require-expression-type! (nth types 1) :f64 (nth args 1)) :vector-f64)

      (= op 'string-index-new) :string-index
      (= op 'string-index-count)
      (do (require-expression-type! (first types) :string-index (first args)) :i64)
      (= op 'string-index-contains)
      (do (require-expression-type! (nth types 0) :string-index (nth args 0))
          (require-expression-type! (nth types 1) :string (nth args 1)) :bool)
      (= op 'string-index-get)
      (do (require-expression-type! (nth types 0) :string-index (nth args 0))
          (require-expression-type! (nth types 1) :string (nth args 1)) [:option :i64])
      (= op 'string-index-assoc)
      (do (require-expression-type! (nth types 0) :string-index (nth args 0))
          (require-expression-type! (nth types 1) :string (nth args 1))
          (require-expression-type! (nth types 2) :i64 (nth args 2)) :string-index)
      (= op 'disjoint-set-i64-new)
      (do (require-expression-type! (first types) :i64 (first args)) :disjoint-set-i64)
      (= op 'disjoint-set-i64-count)
      (do (require-expression-type! (first types) :disjoint-set-i64 (first args)) :i64)
      (= op 'disjoint-set-i64-union)
      (do (require-expression-type! (nth types 0) :disjoint-set-i64 (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1))
          (require-expression-type! (nth types 2) :i64 (nth args 2))
          [:option :disjoint-set-i64])

      (= op 'document-null) :document
      (= op 'document-bool)
      (do (require-expression-type! (first types) :bool (first args)) :document)
      (= op 'document-i64)
      (do (require-expression-type! (first types) :i64 (first args)) :document)
      (= op 'document-f64)
      (do (require-expression-type! (first types) :f64 (first args)) :document)
      (= op 'document-string)
      (do (require-expression-type! (first types) :string (first args)) :document)
      (= op 'document-keyword)
      (do (require-expression-type! (first types) :keyword (first args)) :document)
      (= op 'document-symbol)
      (do (require-expression-type! (first types) :symbol (first args)) :document)
      (= op 'document-vector)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :document arg)) :document)
      (= op 'document-list)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :document arg)) :document)
      (= op 'document-set)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :document arg)) :document)
      (= op 'document-map)
      (do (doseq [[[key-form item-form] [key-type item-type]]
                  (map vector (partition 2 args) (partition 2 types))]
            (when-not (contains? #{:keyword :document} key-type)
              (reject! "document-map key must be keyword or document" key-form))
            (require-expression-type! item-type :document item-form)) :document)
      (= op 'document-count)
      (do (require-expression-type! (first types) :document (first args)) :i64)
      (= op 'document-kind)
      (do (require-expression-type! (first types) :document (first args)) :keyword)
      (= op 'document-sha256)
      (do (require-expression-type! (first types) :document (first args)) :string)
      (= op 'document-print)
      (do (require-expression-type! (first types) :document (first args)) :string)
      (= op 'document-read)
      (do (require-expression-type! (first types) :string (first args)) :document)
      (= op 'document-edn-print)
      (do (require-expression-type! (first types) :document (first args)) :string)
      (= op 'document-edn-read)
      (do (require-expression-type! (first types) :string (first args)) :document)
      (= op 'document-vector-at)
      (do (require-expression-type! (nth types 0) :document (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1)) [:option :document])
      (= op 'document-list-at)
      (do (require-expression-type! (nth types 0) :document (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1)) [:option :document])
      (= op 'document-map-entry-at)
      (do (require-expression-type! (nth types 0) :document (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1)) [:option :document])
      (= op 'document-vector-assoc)
      (do (require-expression-type! (nth types 0) :document (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1))
          (require-expression-type! (nth types 2) :document (nth args 2)) :document)
      (= op 'document-vector-conj)
      (do (require-expression-type! (nth types 0) :document (nth args 0))
          (require-expression-type! (nth types 1) :document (nth args 1)) :document)
      (= op 'document-vector-drop)
      (do (require-expression-type! (nth types 0) :document (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1)) :document)
      (= op 'document-vector-remove)
      (do (require-expression-type! (nth types 0) :document (nth args 0))
          (require-expression-type! (nth types 1) :i64 (nth args 1)) :document)
      (= op 'document-contains)
      (do (require-expression-type! (nth types 0) :document (nth args 0))
          (when-not (contains? #{:keyword :document} (nth types 1))
            (reject! "document map key must be keyword or document" (nth args 1))) :bool)
      (= op 'document-equal?)
      (do (require-expression-type! (nth types 0) :document (nth args 0))
          (require-expression-type! (nth types 1) :document (nth args 1)) :bool)
      (= op 'document-set-contains?)
      (do (require-expression-type! (nth types 0) :document (nth args 0))
          (require-expression-type! (nth types 1) :document (nth args 1)) :bool)
      (= op 'document-get)
      (do (require-expression-type! (nth types 0) :document (nth args 0))
          (when-not (contains? #{:keyword :document} (nth types 1))
            (reject! "document map key must be keyword or document" (nth args 1))) [:option :document])
      (= op 'document-assoc)
      (do (require-expression-type! (nth types 0) :document (nth args 0))
          (when-not (contains? #{:keyword :document} (nth types 1))
            (reject! "document map key must be keyword or document" (nth args 1)))
          (require-expression-type! (nth types 2) :document (nth args 2)) :document)
      (= op 'document-dissoc)
      (do (require-expression-type! (nth types 0) :document (nth args 0))
          (when-not (contains? #{:keyword :document} (nth types 1))
            (reject! "document map key must be keyword or document" (nth args 1))) :document)
      (= op 'document-merge)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :document arg)) :document)
      (= op 'document-string-value)
      (do (require-expression-type! (first types) :document (first args)) [:option :string])
      (= op 'document-keyword-value)
      (do (require-expression-type! (first types) :document (first args)) [:option :keyword])
      (= op 'document-symbol-value)
      (do (require-expression-type! (first types) :document (first args)) [:option :symbol])
      (= op 'document-bool-value)
      (do (require-expression-type! (first types) :document (first args)) [:option :bool])
      (= op 'document-i64-value)
      (do (require-expression-type! (first types) :document (first args)) [:option :i64])
      (= op 'document-f64-value)
      (do (require-expression-type! (first types) :document (first args)) [:option :f64])

      (contains? (disj comparisons '=) op)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :i64 arg))
          :bool)

      (contains? heap-operations op)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :i64 arg))
          :i64)

      (contains? kgraph-operations op)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :i64 arg))
          :i64)

      (or (contains? kernel-memory-operations op)
          (contains? kernel-privileged-operations op))
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :i64 arg))
          :i64)

      (= op 'cap-call)
      (do (require-expression-type! (second types) :i64 (second args)) :i64)

      (= op 'string-byte-length)
      (do (require-expression-type! (first types) :string (first args)) :i64)

      ;; Product Value ABI v1: alias of string-byte-length (UTF-8 byte count;
      ;; same unit as string-substring indices). Prefer this name in pure-product.
      (= op 'string-length)
      (do (require-expression-type! (first types) :string (first args)) :i64)

      (= op 'string-from-i64)
      (do (require-expression-type! (first types) :i64 (first args)) :string)

      ;; T4.2: desugars away; defensive typing if seen pre-desugar.
      (= op 'string-join)
      (do (when (zero? (count args))
            (reject! "string-join requires a separator string" args))
          (when (> (count (rest args)) 8)
            (reject! "string-join exceeds max 8 parts" args))
          (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :string arg))
          :string)

      (= op 'bytes-task-byte-count)
      (do (require-expression-type! (first types) [:task [:stream :bytes]] (first args))
          :i64)

      (= op 'task-ready?)
      (do (require-expression-type! (first types) [:task [:stream :bytes]] (first args))
          :i64)

      (= op 'object-cas-won)
      (let [descriptor (first types)
            fields (when (and (vector? descriptor)
                              (= :record (first descriptor)))
                     (nth descriptor 2 nil))]
        (when-not (and (seq fields)
                       (= :bool (second (first fields))))
          (reject! "object-cas-won requires a record whose first field is bool"
                   (first args)))
        :i64)

      (contains? '#{bytes-response-byte-count log-read-byte-count} op)
      (let [descriptor (first types)
            fields (when (and (vector? descriptor) (= :record (first descriptor)))
                     (nth descriptor 2 nil))
            field (if (= op 'bytes-response-byte-count) (first fields) (second fields))]
        (when-not (= :string (second field))
          (reject! (str op " requires a record bytes field") (first args)))
        :i64)

      (= op 'bool-result)
      (do (require-expression-type! (first types) :bool (first args)) :i64)

      (= op 'http-response-status)
      (let [descriptor (first types)
            fields (when (and (vector? descriptor) (= :record (first descriptor)))
                     (nth descriptor 2 nil))]
        (when-not (= :i64 (second (first fields)))
          (reject! "http-response-status requires a record status field" (first args)))
        :i64)

      (= op 'string=?)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :string arg))
          :i64)

      (= op 'string-concat)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :string arg))
          :string)

      (= op 'string-substring)
      (do (require-expression-type! (first types) :string (first args))
          (doseq [[arg type] (map vector (rest args) (rest types))]
            (require-expression-type! type :i64 arg))
          :string)

      (= op 'string-replace-all)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :string arg))
          :string)

      (= op 'string-contains?)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :string arg))
          :i64)

      (= op 'string-split-count)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :string arg))
          :i64)

      (= op 'string-code-point-at)
      (do (require-expression-type! (first types) :string (first args))
          (require-expression-type! (second types) :i64 (second args))
          :i64)

      (= op 'string-fold-case)
      (do (require-expression-type! (first types) :string (first args)) :string)

      (= op 'keyword-from-string)
      (do (require-expression-type! (first types) :string (first args)) :keyword)

      (= op 'keyword-name)
      (do (require-expression-type! (first types) :keyword (first args)) :string)

      (= op 'symbol)
      (do (require-expression-type! (first types) :string (first args)) :symbol)

      (= op 'xml-path-count)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :string arg))
          :i64)

      (= op 'xml-name-count)
      (do (doseq [[arg type] (map vector args types)]
            (require-expression-type! type :string arg))
          :i64)

      (= op 'xml-name-text)
      (do (require-expression-type! (nth types 0) :string (nth args 0))
          (require-expression-type! (nth types 1) :string (nth args 1))
          (require-expression-type! (nth types 2) :i64 (nth args 2))
          [:option :string])

      (= op 'xml-path-text)
      (do (require-expression-type! (nth types 0) :string (nth args 0))
          (require-expression-type! (nth types 1) :string (nth args 1))
          (require-expression-type! (nth types 2) :i64 (nth args 2))
          [:option :string])

      (= op 'xml-path-attr)
      (do (require-expression-type! (nth types 0) :string (nth args 0))
          (require-expression-type! (nth types 1) :string (nth args 1))
          (require-expression-type! (nth types 2) :i64 (nth args 2))
          (require-expression-type! (nth types 3) :string (nth args 3))
          [:option :string])

      (= op 'decimal-f64-parse)
      (do (require-expression-type! (first types) :string (first args))
          [:option :f64])

      (= op 'decimal-f64x3-parse)
      (do (require-expression-type! (first types) :string (first args))
          [:option [:vector [:f64 :f64 :f64]]])

      (= op 'f64-to-bits)
      (do (require-expression-type! (first types) :f64 (first args)) :i64)

      (= op 'f64-from-bits)
      (do (require-expression-type! (first types) :i64 (first args)) :f64)

      (contains? '#{i64-to-f64-checked i64-to-f64-rounded} op)
      (do (require-expression-type! (first types) :i64 (first args)) :f64)

      (contains? '#{f64-to-i64-checked f64-to-i64-truncating} op)
      (do (require-expression-type! (first types) :f64 (first args)) :i64)

      (contains? '#{f64-add f64-sub f64-mul f64-div f64-min f64-max} op)
      (do (doseq [[type arg] (map vector types args)]
            (require-expression-type! type :f64 arg))
          :f64)

      (contains? '#{f64-neg f64-abs f64-sqrt f64-sin-quarter-turn f64-cos-quarter-turn
                    f64-sin-bounded f64-cos-bounded f64-exp-near-zero f64-log-near-one} op)
      (do (require-expression-type! (first types) :f64 (first args)) :f64)

      (= op 'f64-atan2-bounded)
      (do (doseq [[type arg] (map vector types args)]
            (require-expression-type! type :f64 arg))
          :f64)

      (contains? '#{f64-exp-bounded f64-log-bounded} op)
      (do (require-expression-type! (first types) :f64 (first args)) :f64)

      (contains? '#{f64-eq f64-lt f64-le f64-gt f64-ge f64-unordered} op)
      (do (doseq [[type arg] (map vector types args)]
            (require-expression-type! type :f64 arg))
          :bool)

      (= op 'f32-to-bits)
      (do (require-expression-type! (first types) :f32 (first args)) :i64)

      (= op 'f32-from-bits)
      (do (require-expression-type! (first types) :i64 (first args)) :f32)

      (= op 'f64-to-f32-rounded)
      (do (require-expression-type! (first types) :f64 (first args)) :f32)

      (= op 'f32-to-f64-exact)
      (do (require-expression-type! (first types) :f32 (first args)) :f64)

      (contains? '#{i64-to-f32-checked i64-to-f32-rounded} op)
      (do (require-expression-type! (first types) :i64 (first args)) :f32)

      (contains? '#{f32-to-i64-checked f32-to-i64-truncating} op)
      (do (require-expression-type! (first types) :f32 (first args)) :i64)

      (contains? '#{f32-add f32-sub f32-mul f32-div f32-min f32-max} op)
      (do (doseq [[type arg] (map vector types args)]
            (require-expression-type! type :f32 arg))
          :f32)

      (contains? '#{f32-neg f32-abs f32-sqrt} op)
      (do (require-expression-type! (first types) :f32 (first args)) :f32)

      (contains? '#{f32-eq f32-lt f32-le f32-gt f32-ge f32-unordered} op)
      (do (doseq [[type arg] (map vector types args)]
            (require-expression-type! type :f32 arg))
          :bool)

      (= op 'map-new)
      (do (doseq [[key-form value-form key-type value-type]
                  (map (fn [[key-form value-form] [key-type value-type]]
                         [key-form value-form key-type value-type])
                       (partition 2 args) (partition 2 types))]
            (require-expression-type! key-type :keyword key-form)
            (require-expression-type! value-type :i64 value-form))
          :map)

      (= op 'map-get)
      (do (require-expression-type! (nth types 0) :map (nth args 0))
          (require-expression-type! (nth types 1) :keyword (nth args 1))
          (require-expression-type! (nth types 2) :i64 (nth args 2))
          :i64)

      (= op 'map-assoc)
      (do (require-expression-type! (first types) :map (first args))
          (doseq [[key-form value-form key-type value-type]
                  (map (fn [[key-form value-form] [key-type value-type]]
                         [key-form value-form key-type value-type])
                       (partition 2 (rest args)) (partition 2 (rest types)))]
            (require-expression-type! key-type :keyword key-form)
            (require-expression-type! value-type :i64 value-form))
          :map)

      (contains? signatures op)
      (let [{expected :param-types result :result} (get signatures op)]
        (if (and *loop-helper-recorder* (contains? *loop-helper-names* op))
          ;; Resolution pass: this loop-helper's param-types are not yet known.
          ;; Record the call-site argument types AS its param-types rather than
          ;; checking against the placeholder signature. The (non-recursive)
          ;; enclosing call site is inferred before the helper's own body, so
          ;; the recorded types are the enclosing-scope types of the loop
          ;; bindings' inits and the captured outer variables.
          (vswap! *loop-helper-recorder* assoc op (vec types))
          (doseq [[arg actual wanted] (map vector args types expected)]
            (require-expression-type! actual wanted arg)))
        result)

      :else (reject! "operation has no admitted type signature" op))))

(defn- infer-expression-type [form locals signatures]
  (cond
    (kotoba-integer? form) :i64
    (value/f64-value? form) :f64
    (string? form) :string
    (keyword? form) :keyword
    (boolean? form) :bool
    (symbol? form) (or (get locals form)
                       (reject! "unbound symbol has no value type" form))
    (seq? form)
    (let [[op & args] form]
      (case op
        let (let [[bindings body] args]
              (loop [pairs (partition 2 bindings) current locals]
                (if-let [[name value] (first pairs)]
                  (recur (next pairs)
                         (assoc current name (infer-expression-type value current signatures)))
                  (infer-expression-type body current signatures))))
        if (let [[test then else] args
                 test-type (infer-expression-type test locals signatures)
                 then-type (infer-expression-type then locals signatures)
                 else-type (infer-expression-type else locals signatures)]
             (when-not (contains? #{:i64 :bool} test-type)
               (reject! "if test must be bool or legacy i64" test))
             (when-not (= then-type else-type)
               (reject! "if branches must have the same value type" form))
             then-type)
        do (last (mapv #(infer-expression-type % locals signatures) args))
        typed-cap-call
        (let [[_ request-type result-type request] args]
          (validate-value-type! request-type)
          (validate-value-type! result-type)
          (require-expression-type! (infer-expression-type request locals signatures)
                                    request-type request)
          result-type)
        result-ok-of
        (let [[type payload] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type payload locals signatures)
                                    (second type) payload)
          type)
        result-err-of
        (let [[type payload] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type payload locals signatures)
                                    (nth type 2) payload)
          type)
        result-ok?-of
        (let [[type result] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type result locals signatures) type result)
          :bool)
        result-value-of
        (let [[type result fallback] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type result locals signatures) type result)
          (require-expression-type! (infer-expression-type fallback locals signatures)
                                    (second type) fallback)
          (second type))
        result-error-of
        (let [[type result fallback] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type result locals signatures) type result)
          (require-expression-type! (infer-expression-type fallback locals signatures)
                                    (nth type 2) fallback)
          (nth type 2))
        result-match-of
        (let [[type result ok-name ok-body err-name err-body] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type result locals signatures) type result)
          (let [ok-type (infer-expression-type ok-body (assoc locals ok-name (second type)) signatures)
                err-type (infer-expression-type err-body (assoc locals err-name (nth type 2)) signatures)]
            (when-not (= ok-type err-type)
              (reject! "result match branches must have the same value type" form))
            ok-type))
        variant-new
        (let [[type tag payload] args
              type (canonical-closure-result-type type)
              payload-type (some (fn [[case-tag case-type]]
                                   (when (= case-tag tag) case-type))
                                 (nth type 2))]
          (validate-value-type! type)
          (when-not payload-type (reject! "variant constructor tag is not declared" form))
          (require-expression-type! (infer-expression-type payload locals signatures)
                                    payload-type payload)
          type)
        variant-match
        (let [[type value branches] args
              type (canonical-closure-result-type type)
              cases (nth type 2)]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          (let [branch-types
                (mapv (fn [[[tag payload-type] [_ binder body]]]
                        (infer-expression-type body (assoc locals binder payload-type) signatures))
                      (map vector cases branches))]
            (when-not (apply = branch-types)
              (reject! "variant match branches must have the same value type" form))
            (first branch-types)))
        option-some-of
        (let [[type payload] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type payload locals signatures)
                                    (second type) payload)
          type)
        option-none-of
        (let [[type] args] (validate-value-type! type) type)
        option-some?-of
        (let [[type value] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          :bool)
        option-value-of
        (let [[type value fallback] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          (require-expression-type! (infer-expression-type fallback locals signatures)
                                    (second type) fallback)
          (second type))
        option-match
        (let [[type value none-body some-name some-body] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          (let [none-type (infer-expression-type none-body locals signatures)
                some-type (infer-expression-type some-body
                                                 (assoc locals some-name (second type)) signatures)]
            (when-not (= none-type some-type)
              (reject! "option match branches must have the same value type" form))
            none-type))
        typed-list-new
        (let [[type & items] args]
          (validate-value-type! type)
          (doseq [item items]
            (require-expression-type! (infer-expression-type item locals signatures)
                                      (second type) item))
          type)
        bytes-empty :bytes
        hetero-vector-new
        (let [[type & items] args
              item-types (second type)]
          (validate-value-type! type)
          (doseq [[item item-type] (map vector items item-types)]
            (require-expression-type! (infer-expression-type item locals signatures)
                                      item-type item))
          type)
        hetero-vector-count
        (let [[type value] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          :i64)
        hetero-vector-at
        (let [[type value index] args
              item-types (second type)
              host-index (heterogeneous-vector-index! index item-types form)]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          (nth item-types host-index))
        __kotoba_destructure_get
        (let [[value key default] args
              value-type (infer-expression-type value locals signatures)
              descriptor (resolve-ref-type value-type)]
          (cond
            (canonical-typed-map-type? value-type)
            (do
              (when-not (= 3 (count args))
                (reject! "typed-map destructuring requires an :or default"
                         form :kotoba.error/destructure-default))
              (require-expression-type! (infer-expression-type key locals signatures)
                                        (second value-type) key)
              (require-expression-type! (infer-expression-type default locals signatures)
                                        (nth value-type 2) default)
              (nth value-type 2))

            (record-type? descriptor)
            (or (record-field-type descriptor key)
                (reject! "record field is not declared"
                         form :kotoba.error/record-field))

            :else
            (infer-call-type 'map-get
                             [value key (if (= 3 (count args)) default 0)]
                             locals signatures)))
        get
        (let [[value key default] args
              value-type (infer-expression-type value locals signatures)
              descriptor (resolve-ref-type value-type)]
          (cond
            (canonical-typed-map-type? value-type)
            (do
              (require-expression-type! (infer-expression-type key locals signatures)
                                        (second value-type) key)
              (if (= 3 (count args))
                (do
                  (require-expression-type!
                   (infer-expression-type default locals signatures)
                   (nth value-type 2) default)
                  (nth value-type 2))
                [:option (nth value-type 2)]))

            (record-type? descriptor)
            (do
              (when-not (= 2 (count args))
                (reject! "record get requires a value and one keyword field"
                         form :kotoba.error/record-projection-unresolved))
              (or (record-field-type descriptor key)
                  (reject! "record field is not declared"
                           form :kotoba.error/record-field)))

            :else
            (infer-call-type 'map-get
                             [value key (if (= 3 (count args)) default 0)]
                             locals signatures)))
        nth
        (let [[value index & defaults] args
              value-type (infer-expression-type value locals signatures)]
          (cond
            (heterogeneous-vector-type? value-type)
            (do
              (when-not (<= 2 (count args) 3)
                (reject! "heterogeneous vector nth requires a value, one literal index, and an optional default"
                         form :kotoba.error/hetero-vector-index))
              (let [host-index
                    (heterogeneous-vector-index! index (second value-type) form)
                    item-type (nth (second value-type) host-index)]
                (when (= 3 (count args))
                  (let [default (first defaults)]
                    (require-expression-type!
                     (infer-expression-type default locals signatures)
                     item-type default)))
                item-type))

            (= :vector-i64 value-type)
            (do
              (when-not (<= 2 (count args) 3)
                (reject! "vector nth requires value, index, and optional default" form))
              (infer-call-type (if (= 3 (count args)) 'vector-get 'vector-at)
                               args locals signatures))

            (= :vector-f64 value-type)
            (do
              (when-not (<= 2 (count args) 3)
                (reject! "vector nth requires value, index, and optional default" form))
              (infer-call-type (if (= 3 (count args)) 'vector-f64-get 'vector-f64-at)
                               args locals signatures))

            :else (infer-call-type op args locals signatures)))
        hetero-vector-assoc
        (let [[type value index item] args
              item-types (second type)
              host-index (heterogeneous-vector-index! index item-types form)]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          (require-expression-type! (infer-expression-type item locals signatures)
                                    (nth item-types host-index) item)
          type)
        hetero-vector-equal
        (let [[type left right] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type left locals signatures) type left)
          (require-expression-type! (infer-expression-type right locals signatures) type right)
          :i64)
        typed-set-new
        (let [[type & items] args]
          (validate-value-type! type)
          (doseq [item items]
            (require-expression-type! (infer-expression-type item locals signatures)
                                      (second type) item))
          type)
        typed-set-count
        (let [[type value] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          :i64)
        typed-set-contains
        (let [[type value item] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          (require-expression-type! (infer-expression-type item locals signatures)
                                    (second type) item)
          :bool)
        typed-set-conj
        (let [[type value item] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          (require-expression-type! (infer-expression-type item locals signatures)
                                    (second type) item)
          type)
        typed-set-disj
        (let [[type value item] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          (require-expression-type! (infer-expression-type item locals signatures)
                                    (second type) item)
          type)
        typed-set-equal
        (let [[type left right] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type left locals signatures) type left)
          (require-expression-type! (infer-expression-type right locals signatures) type right)
          :i64)
        typed-set-nth
        (let [[type value index] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          (require-expression-type! (infer-expression-type index locals signatures) :i64 index)
          (second type))
        typed-map-new
        (let [[type & entries] args
              [key-type value-type] (rest type)]
          (validate-value-type! type)
          (doseq [[key item] (partition 2 entries)]
            (require-expression-type! (infer-expression-type key locals signatures)
                                      key-type key)
            (require-expression-type! (infer-expression-type item locals signatures)
                                      value-type item))
          type)
        typed-map-count
        (let [[type value] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          :i64)
        typed-map-contains
        (let [[type value key] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          (require-expression-type! (infer-expression-type key locals signatures)
                                    (second type) key)
          :bool)
        typed-map-get
        (let [[type value key] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          (require-expression-type! (infer-expression-type key locals signatures)
                                    (second type) key)
          [:option (nth type 2)])
        typed-map-entry-at
        (let [[type value index] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          (require-expression-type! (infer-expression-type index locals signatures) :i64 index)
          [:option [:vector [(second type) (nth type 2)]]])
        typed-map-assoc
        (let [[type value key item] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          (require-expression-type! (infer-expression-type key locals signatures)
                                    (second type) key)
          (require-expression-type! (infer-expression-type item locals signatures)
                                    (nth type 2) item)
          type)
        typed-map-dissoc
        (let [[type value key] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          (require-expression-type! (infer-expression-type key locals signatures)
                                    (second type) key)
          type)
        typed-map-equal
        (let [[type left right] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type left locals signatures) type left)
          (require-expression-type! (infer-expression-type right locals signatures) type right)
          :i64)
        record-new
        (let [[type & values] args
              fields (nth type 2)]
          (validate-value-type! type)
          (doseq [[[field field-type] item] (map vector fields values)]
            (require-expression-type! (infer-expression-type item locals signatures)
                                      field-type field))
          type)
        record-get
        (let [[type value field] args
              field-type (some (fn [[declared-field declared-type]]
                                 (when (= declared-field field) declared-type))
                               (nth type 2))]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          field-type)
        record-assoc
        (let [[type value field replacement] args
              field-type (some (fn [[declared-field declared-type]]
                                 (when (= declared-field field) declared-type))
                               (nth type 2))]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type value locals signatures) type value)
          (require-expression-type! (infer-expression-type replacement locals signatures)
                                    field-type replacement)
          type)
        record-equal
        (let [[type left right] args]
          (validate-value-type! type)
          (require-expression-type! (infer-expression-type left locals signatures) type left)
          (require-expression-type! (infer-expression-type right locals signatures) type right)
          :i64)
        (infer-call-type op args locals signatures)))
    :else (reject! "value has no admitted type" form)))

(defn- preserve-form-meta [source result]
  (if-let [m (meta source)]
    (with-meta result m)
    result))

(defn- elaborate-named-ability
  "Lower a friendly qualified operation such as `(http/post request)` after
  parameter and result types are known. Request type comes from the lexical
  expression and result type from the typed context; neither is repeated in
  application source. A call without result context fails closed until the
  semantic catalog owns a context-independent result schema."
  [form expected locals signatures used]
  (if-not (seq? form)
    form
    (let [[op & args] form]
      (cond
        (contains? source-operation-registry op)
        (do
          (when-not (= 1 (count args))
            (reject! "named capability operation requires exactly one request" form))
          (when-not expected
            (reject! "named capability operation requires a typed result context" form))
          (let [request (elaborate-named-ability
                         (first args) nil locals signatures used)
                request-type (infer-expression-type request locals signatures)
                capability (get source-operation-registry op)
                id (capability-wire-id capability form)]
            (vswap! used conj capability)
            (preserve-form-meta
             form
             (list 'typed-cap-call id request-type expected request))))

        (= op 'let)
        (let [[bindings body] args]
          (loop [pairs (partition 2 bindings)
                 current locals
                 out []]
            (if-let [[name value] (first pairs)]
              (let [elaborated
                    (elaborate-named-ability value nil current signatures used)
                    value-type
                    (infer-expression-type elaborated current signatures)]
                (recur (next pairs)
                       (assoc current name value-type)
                       (conj out name elaborated)))
              (preserve-form-meta
               form
               (list 'let (vec out)
                     (elaborate-named-ability
                      body expected current signatures used))))))

        (= op 'if)
        (let [[test then else] args]
          (preserve-form-meta
           form
           (list 'if
                 (elaborate-named-ability test nil locals signatures used)
                 (elaborate-named-ability then expected locals signatures used)
                 (elaborate-named-ability else expected locals signatures used))))

        (= op 'do)
        (let [last-index (dec (count args))]
          (preserve-form-meta
           form
           (list* 'do
                  (map-indexed
                   (fn [index expression]
                     (elaborate-named-ability
                      expression (when (= index last-index) expected)
                      locals signatures used))
                   args))))

        ;; Lowered pattern forms bind payload names in only their branch
        ;; bodies. Preserve those lexical types while elaborating named
        ;; abilities; generic recursion would otherwise treat the binder as
        ;; unbound when a branch contains any expression whose expected type
        ;; must be inferred (including the `option-value-of` produced from
        ;; `option-or`).
        (= op 'option-match)
        (let [[type value none-body some-name some-body] args]
          (preserve-form-meta
           form
           (list 'option-match type
                 (elaborate-named-ability value type locals signatures used)
                 (elaborate-named-ability none-body expected locals signatures used)
                 some-name
                 (elaborate-named-ability some-body expected
                                          (assoc locals some-name (second type))
                                          signatures used))))

        (= op 'result-match-of)
        (let [[type value ok-name ok-body err-name err-body] args]
          (preserve-form-meta
           form
           (list 'result-match-of type
                 (elaborate-named-ability value type locals signatures used)
                 ok-name
                 (elaborate-named-ability ok-body expected
                                          (assoc locals ok-name (second type))
                                          signatures used)
                 err-name
                 (elaborate-named-ability err-body expected
                                          (assoc locals err-name (nth type 2))
                                          signatures used))))

        (= op 'variant-match)
        (let [[type value branches] args
              payloads (into {} (nth type 2))]
          (preserve-form-meta
           form
           (list 'variant-match type
                 (elaborate-named-ability value type locals signatures used)
                 (mapv (fn [[tag binder body]]
                         [tag binder
                          (elaborate-named-ability body expected
                                                   (assoc locals binder (get payloads tag))
                                                   signatures used)])
                       branches))))

        (= op 'typed-cap-call)
        (let [[id request-type result-type request] args]
          (preserve-form-meta
           form
           (list 'typed-cap-call id request-type result-type
                 (elaborate-named-ability
                  request request-type locals signatures used))))

        (contains? signatures op)
        (let [expected-args (:param-types (get signatures op))]
          (preserve-form-meta
           form
           (list* op
                  (map (fn [argument argument-type]
                         (elaborate-named-ability
                          argument argument-type locals signatures used))
                       args expected-args))))

        :else
        (preserve-form-meta
         form
         (list* op
                (map #(elaborate-named-ability
                       % nil locals signatures used)
                     args)))))))

(defn- elaborate-named-abilities [functions]
  (let [signatures
        (into {} (map (fn [{:keys [name params param-types result]}]
                        [name {:params params
                               :param-types param-types
                               :result result}]))
              functions)
        used (volatile! #{})]
    {:functions
     (mapv (fn [{:keys [params param-types result] :as function}]
             (update function :body
                     #(elaborate-named-ability
                       % result (zipmap params param-types) signatures used)))
           functions)
     :used @used}))

(defn- resolve-loop-helper-param-types
  "`loop`/`recur` desugars to a synthesized recursive helper whose parameters
  are the loop bindings followed by the captured outer variables (see the
  `loop` case in desugar-expr). The helper carries no param-type annotations
  because a captured variable's type is knowable only at the helper's call
  site. Recover each loop-helper's param-types from the (unique, non-recursive)
  call site it has in its enclosing function body -- `(helper loop-init...
  captured-sym...)` -- by fixpoint: each round, infer every function whose
  param-types are already known, recording the argument types at every
  still-unresolved loop-helper call. Enclosing callers resolve first (they are
  non-helpers, or an outer loop-helper resolved in an earlier round), so nested
  loops converge. Returns `functions` with every loop-helper's :param-types
  filled in; any helper left unresolved (only possible when the module has an
  independent type error that makes inference throw) keeps an all-:i64
  placeholder so the genuine error still surfaces in check-value-types!."
  [functions]
  (let [helper-names (into #{} (comp (filter :loop-helper?) (map :name)) functions)]
    (if (empty? helper-names)
      functions
      (letfn [(placeholder [{:keys [params]}] (vec (repeat (count params) :i64)))
              (round [resolved]
                (let [recorder (volatile! {})
                      sigs (into {}
                                 (map (fn [{:keys [name params param-types result] :as f}]
                                        [name {:params params
                                               :param-types (cond
                                                              (contains? resolved name) (resolved name)
                                                              (contains? helper-names name) (placeholder f)
                                                              param-types param-types
                                                              :else (placeholder f))
                                               ;; Preserve declared loop-helper result (T4.5 map/filter → :vector-i64).
                                               :result (or result :i64)}]))
                                 functions)]
                  (binding [*loop-helper-names* (into #{} (remove #(contains? resolved %) helper-names))
                            *loop-helper-recorder* recorder]
                    (doseq [{:keys [name params body] :as f} functions
                            :when (or (not (contains? helper-names name))
                                      (contains? resolved name))]
                      (try
                        (infer-expression-type body (zipmap params (get-in sigs [name :param-types])) sigs)
                        (catch #?(:clj Exception :cljs :default) _
                          ;; An independent type error in this body -- ignore
                          ;; here; check-value-types! will report it properly.
                          nil))))
                  (merge resolved @recorder)))]
        (loop [resolved {}]
          (let [next-resolved (round resolved)]
            (if (or (= (count next-resolved) (count helper-names))
                    (= (count next-resolved) (count resolved)))
              (mapv (fn [{:keys [name] :as f}]
                      (if (contains? helper-names name)
                        (assoc f :param-types (get next-resolved name (placeholder f)))
                        f))
                    functions)
              (recur next-resolved))))))))

(def ^:dynamic *record-protocol-dispatch* {})

(defn- rewrite-record-projection
  "Type-directed rewrite: `(record-get value :field)` -> the canonical
  `(record-get SCHEMA value :field)`, recovering SCHEMA from the value's
  inferred type.

  `record-get` needs the descriptor because lowering is static, which forced
  every projection site to repeat the whole `[:record :ns/name [[:f :i64] …]]`
  literal (13 copies in one murakumo module). The type is already known here,
  so the descriptor is derivable rather than something the author must retype.

  Runs after desugar and before validation, so `validate-expr`, inference and
  every backend continue to see only the 3-arity form — no lowering or
  out-of-repo change is involved.

  `let` is the only binding form that survives to this stage (`loop`/`fn` are
  already lowered to helpers), so it is threaded explicitly and everything else
  recurses structurally. Vectors — including type descriptors — are returned
  untouched because they are not seqs."
  [form locals signatures schemas]
  (if-not (seq? form)
    form
    ;; Every branch below rebuilds the form, and a rebuilt list carries no
    ;; metadata. That silently erased the reader span and `:source-operation`
    ;; that `attach-source-operation` puts on an elaborated named operation --
    ;; but only in functions WITH parameters, because `rewrite-record-projections`
    ;; skips a body whose `:param-types` is empty. `(defn main [] (read-clock 42))`
    ;; kept its span while `(defn read-clock [seed] (clock/now seed))` lost it,
    ;; which is why the loss read as unrelated to this pass.
    ;;
    ;; Downstream diagnostics are the casualty: an effect-ceiling or admission
    ;; rejection could no longer name the operation or point at a line
    ;; (ADR-2607279200 promises both). Restore the source form's metadata onto
    ;; whatever this pass produces.
    (preserve-form-meta
     form
     (let [[op & args] form]
      (cond
        (= op 'let)
        (let [[bindings body] args
              [pairs locals']
              (reduce (fn [[acc cur] [nm value]]
                        (let [v (rewrite-record-projection value cur signatures schemas)]
                          [(conj acc nm v)
                           ;; This pass resolves record projections; it is not a
                           ;; type checker, and it must never be the thing that
                           ;; reports a type error. It runs BEFORE
                           ;; `elaborate-named-abilities`, so a binding whose
                           ;; value is a still-named capability operation has no
                           ;; signature yet -- inference threw "operation has no
                           ;; admitted type signature", pre-empting the accurate
                           ;; "named capability operation requires a typed result
                           ;; context" that elaboration would have produced one
                           ;; pass later. Measured on
                           ;;   (let [response (http/post request)] response)
                           ;; An untypeable binding simply has no known type
                           ;; here; a 2-arity `record-get` against it still fails
                           ;; closed with the record-projection message, and any
                           ;; genuine type error surfaces later from
                           ;; check-value-types! with its own diagnostics.
                           (assoc cur nm
                                  (try (infer-expression-type v cur signatures)
                                       (catch #?(:clj Exception :cljs :default) _ nil)))]))
                      [[] locals]
                      (partition 2 bindings))]
          (list 'let (vec pairs) (rewrite-record-projection body locals' signatures schemas)))

        (= op 'option-or)
        (let [[value fallback] args
              value (rewrite-record-projection value locals signatures schemas)
              fallback (rewrite-record-projection fallback locals signatures schemas)
              option-type (infer-expression-type value locals signatures)]
          (when-not (and (vector? option-type)
                         (= 2 (count option-type))
                         (= :option (first option-type)))
            (reject! (str "option-or requires an option value; got "
                          (pr-str option-type))
                     form
                     :kotoba.error/option-type-unresolved))
          (list 'option-value-of option-type value fallback))

        ;; Type-directed sugar may appear inside a lowered pattern branch. The
        ;; branch binder is lexical, but a generic structural recursion would
        ;; visit the body with the enclosing locals only. In practice this made
        ;; `(option-or (typed-map-get ... key) fallback)` fail when `key` was
        ;; derived from a `(some entry ...)` payload, even though `option-match`
        ;; already carries the exact payload descriptor. Thread the same binder
        ;; types used by `infer-expression-type` through this earlier rewrite.
        (= op 'option-match)
        (let [[type value none-body some-name some-body] args]
          (list 'option-match type
                (rewrite-record-projection value locals signatures schemas)
                (rewrite-record-projection none-body locals signatures schemas)
                some-name
                (rewrite-record-projection some-body
                                           (assoc locals some-name (second type))
                                           signatures schemas)))

        (= op 'result-match-of)
        (let [[type value ok-name ok-body err-name err-body] args]
          (list 'result-match-of type
                (rewrite-record-projection value locals signatures schemas)
                ok-name
                (rewrite-record-projection ok-body
                                           (assoc locals ok-name (second type))
                                           signatures schemas)
                err-name
                (rewrite-record-projection err-body
                                           (assoc locals err-name (nth type 2))
                                           signatures schemas)))

        (= op 'variant-match)
        (let [[type value branches] args
              descriptor (if (schema-ref-type? type)
                           (get schemas (second type))
                           type)
              _ (when (and (schema-ref-type? type)
                           (not (variant-type? descriptor)))
                  (reject! (str "no :variant schema declared for " (second type)
                                " in this namespace")
                           form))
              payloads (if (variant-type? descriptor)
                         (into {} (nth descriptor 2))
                         {})]
          (list 'variant-match descriptor
                (rewrite-record-projection value locals signatures schemas)
                (mapv (fn [[tag binder body]]
                        [tag binder
                         (rewrite-record-projection body
                                                    (assoc locals binder (get payloads tag))
                                                    signatures schemas)])
                      branches)))

        (contains? (:methods *record-protocol-dispatch*) op)
        (let [{:keys [arity implementations]}
              (get-in *record-protocol-dispatch* [:methods op])
              rewritten-args
              (mapv #(rewrite-record-projection % locals signatures schemas) args)]
          (when-not (= arity (count rewritten-args))
            (reject! "protocol method call does not match its declared arity"
                     form :kotoba.error/protocol-method))
          (let [receiver-type (infer-expression-type (first rewritten-args)
                                                     locals signatures)
                type-id (nominal-type-identity receiver-type)
                implementation (get implementations type-id)]
            (when-not implementation
              (reject! (str "protocol method requires a statically known implemented record; got "
                            (pr-str receiver-type))
                       form :kotoba.error/protocol-dispatch))
            (list* implementation rewritten-args)))

        (and (= op 'variant-new)
             (schema-ref-type? (first args)))
        (let [descriptor (get schemas (second (first args)))]
          (when-not (variant-type? descriptor)
            (reject! (str "no :variant schema declared for "
                          (second (first args)) " in this namespace")
                     form))
          (cons op (cons descriptor
                         (map #(rewrite-record-projection % locals signatures schemas)
                              (rest args)))))

        ;; A named record schema reference in an operation's *type argument*
        ;; is resolved here too (variant constructor/match references are
        ;; handled immediately above), so validation, inference and lowering
        ;; keep seeing only inline descriptors. Annotations in parameter/return
        ;; position need no rewrite — `same-expression-type?` already treats a
        ;; reference and its descriptor as the same nominal type.
        (and (contains? '#{record-new record-get record-assoc record-equal} op)
             (schema-ref-type? (first args)))
        (let [descriptor (get schemas (second (first args)))]
          (when-not (record-type? descriptor)
            (reject! (str "no :record schema declared for " (second (first args))
                          " in this namespace")
                     form
                     :kotoba.error/record-projection-unresolved))
          (cons op (cons descriptor
                         (map #(rewrite-record-projection % locals signatures schemas)
                              (rest args)))))

        (and (= op 'record-get) (= 2 (count args)))
        (let [value (rewrite-record-projection (first args) locals signatures schemas)
              value-type (infer-expression-type value locals signatures)
              ;; A named schema reference resolves through the namespace's
              ;; closed :schemas map, so a value threaded through many
              ;; signatures can be annotated `[:ref :ns/name]` instead of
              ;; repeating the descriptor at every site.
              descriptor (if (schema-ref-type? value-type)
                           (get schemas (second value-type))
                           value-type)]
          (when-not (record-type? descriptor)
            (reject! (str "record-get without a type descriptor requires a record "
                          "value; got " (pr-str value-type)
                          (when (schema-ref-type? value-type)
                            (str " (no :record schema declared for "
                                 (second value-type) " in this namespace)")))
                     form
                     :kotoba.error/record-projection-unresolved))
          (list 'record-get descriptor value (second args)))

        (= op '__kotoba_destructure_get)
        (let [rewritten-args
              (mapv #(rewrite-record-projection % locals signatures schemas) args)
              [value key default] rewritten-args
              value-type (try (infer-expression-type value locals signatures)
                              (catch #?(:clj Exception :cljs :default) _ nil))
              descriptor (if (schema-ref-type? value-type)
                           (get schemas (second value-type))
                           value-type)]
          (cond
            (canonical-typed-map-type? value-type)
            (do
              (when-not (= 3 (count rewritten-args))
                (reject! "typed-map destructuring requires an :or default"
                         form :kotoba.error/destructure-default))
              (list 'option-value-of [:option (nth value-type 2)]
                    (list 'typed-map-get value-type value key)
                    default))

            (record-type? descriptor)
            (do
              (when-not (keyword? key)
                (reject! "record destructuring requires keyword fields"
                         form :kotoba.error/record-projection-unresolved))
              (list 'record-get descriptor value key))

            :else
            (list 'map-get value key
                  (if (= 3 (count rewritten-args)) default 0))))

        (= op 'get)
        (let [rewritten-args
              (mapv #(rewrite-record-projection % locals signatures schemas) args)
              [value key default] rewritten-args
              ;; This rewrite selects a primitive when the receiver type is
              ;; already known; it is not a type-checking pass. An earlier
              ;; invalid binding may deliberately carry nil here so the final
              ;; checker can report that binding's precise error.
              value-type (try (infer-expression-type value locals signatures)
                              (catch #?(:clj Exception :cljs :default) _ nil))
              descriptor (if (schema-ref-type? value-type)
                           (get schemas (second value-type))
                           value-type)]
          (cond
            (canonical-typed-map-type? value-type)
            (let [lookup (list 'typed-map-get value-type value key)]
              (if (= 3 (count rewritten-args))
                (list 'option-value-of [:option (nth value-type 2)] lookup default)
                lookup))

            (record-type? descriptor)
            (do
              (when-not (and (= 2 (count rewritten-args)) (keyword? key))
                (reject! "record get requires a value and one keyword field"
                         form :kotoba.error/record-projection-unresolved))
              (list 'record-get descriptor value key))

            :else
            (list 'map-get value key
                  (if (= 3 (count rewritten-args)) default 0))))

        (= op 'vector-drop)
        (let [rewritten-args
              (mapv #(rewrite-record-projection % locals signatures schemas) args)
              [value drop-count] rewritten-args
              value-type (try
                           (infer-expression-type value locals signatures)
                           (catch #?(:clj Exception :cljs :default) _ nil))]
          (cond
            (heterogeneous-vector-type? value-type)
            (do
              (when-not (= 2 (count rewritten-args))
                (reject! "heterogeneous vector drop requires a value and one literal count"
                         form :kotoba.error/hetero-vector-slice-index))
              (let [item-types (second value-type)
                    host-index (heterogeneous-vector-slice-index!
                                drop-count item-types form)
                    suffix-types (subvec item-types host-index)
                    suffix-type [:vector suffix-types]
                    value-name (synthetic "hetero-slice")]
                ;; Heterogeneous vectors already expose exact static indexed
                ;; projection and construction. Rebuild the bounded suffix
                ;; from those primitives, binding VALUE once so a general
                ;; source `(vector-drop expression n)` keeps ordinary
                ;; single-evaluation semantics.
                (list 'let [value-name value]
                      (list* 'hetero-vector-new suffix-type
                             (mapv (fn [index]
                                     (list 'hetero-vector-at value-type value-name index))
                                   (range host-index (count item-types)))))))

            (= :vector-f64 value-type)
            (cons 'vector-f64-drop rewritten-args)

            :else
            (cons op rewritten-args)))

        (= op 'nth)
        (let [rewritten-args
              (mapv #(rewrite-record-projection % locals signatures schemas) args)
              value-type (try
                           (infer-expression-type (first rewritten-args)
                                                  locals signatures)
                           (catch #?(:clj Exception :cljs :default) _ nil))]
          (cond
            (heterogeneous-vector-type? value-type)
            (do
              (when-not (<= 2 (count rewritten-args) 3)
                (reject! "heterogeneous vector nth requires a value, one literal index, and an optional default"
                         form :kotoba.error/hetero-vector-index))
              (let [host-index
                    (heterogeneous-vector-index! (second rewritten-args)
                                                 (second value-type) form)
                    item-type (nth (second value-type) host-index)]
                (when (= 3 (count rewritten-args))
                  (let [default (nth rewritten-args 2)]
                    (require-expression-type!
                     (infer-expression-type default locals signatures)
                     item-type default))))
              (list 'hetero-vector-at value-type
                    (first rewritten-args) (second rewritten-args)))

            (= :vector-i64 value-type)
            (do
              (when-not (<= 2 (count rewritten-args) 3)
                (reject! "vector nth requires value, index, and optional default" form))
              (cons (if (= 3 (count rewritten-args)) 'vector-get 'vector-at)
                    rewritten-args))

            (= :vector-f64 value-type)
            (do
              (when-not (<= 2 (count rewritten-args) 3)
                (reject! "vector nth requires value, index, and optional default" form))
              (cons (if (= 3 (count rewritten-args)) 'vector-f64-get 'vector-f64-at)
                    rewritten-args))

            :else (cons op rewritten-args)))

        :else
        ;; Force recursive rewrites while the per-analysis protocol dispatch
        ;; binding is active. A lazy `map` here deferred nested protocol calls
        ;; until validation, after the binding had unwound.
        (cons op (mapv #(rewrite-record-projection % locals signatures schemas) args)))))))

(defn- infer-absent-results
  "Give every unannotated `defn` the result type its body actually has.

  An absent annotation used to mean `:i64`, so an unannotated function could not
  return a predicate once comparisons became `:bool`-typed -- which is most of
  the stdlib, the examples and the test fixtures. Inferring instead is both the
  Clojure reading (no annotation means no constraint) and what keeps a single
  dialect: annotations are for boundaries, not for every function.

  Two passes, because one function's inferred result feeds the next one's
  inference. A body whose type cannot be resolved keeps the `:i64` provisional
  and `check-value-types!` reports the real error."
  [functions]
  (letfn [(sigs [fs]
            (into {} (map (fn [{:keys [name params param-types result]}]
                            [name {:params params :param-types param-types
                                   :result result}]))
                  fs))
          (pass [fs]
            (let [table (sigs fs)]
              (mapv (fn [{:keys [params param-types body result-inferred?] :as f}]
                      (if result-inferred?
                        (if-let [inferred (try (infer-expression-type
                                                body (zipmap params param-types) table)
                                               (catch #?(:clj Exception :cljs :default) _ nil))]
                          (assoc f :result inferred)
                          f)
                        f))
                    fs)))]
    (-> functions pass pass)))

(defn- closure-dispatcher-function?
  "The synthetic entry points whose first physical i64 word is a closure pair."
  [function-name]
  (or (= '__kotoba_closure_apply function-name)
      (boolean
       (re-matches #"__kotoba_invoke(?:_.+)?\$arity[0-4]"
                   (str function-name)))))

(defn- infer-closure-refinements
  "Infer checked closure positions without adding a public closure value type.

  Closure pairs intentionally remain i64 words in Wasm/native signatures.  The
  refinements tell representation-aware runtimes which of those words must be
  validated as the bounded `(lambda-id, capture-chain)` shape.  Facts only grow:
  dispatcher arguments seed the graph, static calls propagate requirements to
  callers, and closure-valued results propagate back through aliases and return
  positions.  The finite function/parameter graph therefore has a deterministic
  fixed point."
  [functions lambda-infos]
  (let [lambda-ids (mapv :id lambda-infos)
        function-names (set (map :name functions))
        seed
        (into {}
              (map (fn [{:keys [name closure-param-indexes closure-result?
                                callable-param-contracts callable-result-contract]}]
                     [name {:params (cond-> (into (set closure-param-indexes)
                                                  (keys callable-param-contracts))
                                      (closure-dispatcher-function? name) (conj 0))
                            :result? (or (true? closure-result?)
                                         (some? callable-result-contract))}]))
              functions)
        refinement-count-limit
        (+ 1 (count functions) (reduce + (map (comp count :params) functions)))]
    (letfn [(binding-value [env name]
              (get env name))
            (lambda-info-for-id [id]
              (some #(when (= id (:id %)) %) lambda-infos))
            (pair-chain-values [form]
              (loop [chain form values []]
                (cond
                  (and (kotoba-integer? chain) (zero? chain)) values
                  (and (seq? chain) (= 'pair (first chain)) (= 3 (count chain)))
                  (recur (nth chain 2) (conj values (second chain)))
                  :else nil)))
            (closure-literal? [form]
              (and (seq? form)
                   (= 'pair (first form))
                   (= 3 (count form))
                   (kotoba-integer? (second form))
                   ;; NBB represents guest i64 literals as JavaScript BigInt,
                   ;; which cannot be hashed by the CLJS persistent-set UID
                   ;; path. Lambda IDs are bounded by max-functions, so a
                   ;; deterministic linear scan avoids hashing arbitrary pair
                   ;; payloads without widening the analysis.
                   (some #(= % (second form)) lambda-ids)))
            (zero-tested-symbol [form]
              (when (and (seq? form) (= '= (first form)) (= 3 (count form)))
                (let [[left right] (rest form)]
                  (cond
                    (and (symbol? left) (kotoba-integer? right) (zero? right)) left
                    (and (symbol? right) (kotoba-integer? left) (zero? left)) right
                    :else nil))))
            (expression-status [function-name form env param-indexes facts seen]
              (cond
                (closure-literal? form) :closure
                (symbol? form)
                (if (contains? seen form)
                  :unknown
                  (if-let [{bound-form :form bound-env :env}
                           (binding-value env form)]
                    (expression-status function-name bound-form bound-env
                                       param-indexes facts (conj seen form))
                    (if (contains? (get-in facts [function-name :params] #{})
                                   (get param-indexes form))
                      :closure
                      :unknown)))
                (seq? form)
                (let [[op & args] form]
                  (cond
                    (= op 'let)
                    (let [[bindings body] args]
                      (loop [pairs (partition 2 bindings) current env]
                        (if-let [[name value] (first pairs)]
                          (let [status (expression-status function-name value current
                                                          param-indexes facts seen)]
                            (if (= :trap status)
                              :trap
                              (recur (next pairs)
                                     (assoc current name {:form value
                                                          :env current}))))
                          (expression-status function-name body current param-indexes
                                             facts seen))))

                    (= op 'if)
                    (let [[test then else] args
                          test-status (expression-status function-name test env
                                                         param-indexes facts seen)]
                      (if (= :trap test-status)
                        :trap
                        (let [then-status (expression-status function-name then env
                                                             param-indexes facts seen)
                              else-status (expression-status function-name else env
                                                             param-indexes facts seen)
                              statuses (set [then-status else-status])]
                          (cond
                            (= statuses #{:trap}) :trap
                            (and (contains? statuses :closure)
                                 (every? #{:closure :trap} statuses)) :closure
                            :else :unknown))))

                    (= op 'do)
                    (loop [remaining args]
                      (if-let [value (first remaining)]
                        (let [status (expression-status function-name value env
                                                        param-indexes facts seen)]
                          (if (or (= :trap status) (nil? (next remaining)))
                            status
                            (recur (next remaining))))
                        :unknown))

                    (and (= op 'quot) (= args '(1 0))) :trap

                    :else
                    (let [arg-statuses (mapv #(expression-status
                                              function-name % env param-indexes facts seen)
                                             args)]
                      (cond
                        (some #{:trap} arg-statuses) :trap
                        (and (contains? function-names op)
                             (get-in facts [op :result?])) :closure
                        :else :unknown))))
                :else :unknown))
            (analyze-pass [facts]
              (let [next-facts (volatile! facts)]
                (letfn [(mark-param! [function-name index]
                          (when (some? index)
                            (vswap! next-facts update-in
                                    [function-name :params] (fnil conj #{}) index)))
                        (mark-result! [function-name]
                          (vswap! next-facts assoc-in [function-name :result?] true))
                        (require-closure! [function-name form env param-indexes
                                           narrowed seen]
                          (when-not (= :trap (expression-status
                                             function-name form env param-indexes
                                             @next-facts seen))
                            (cond
                              (closure-literal? form) nil
                              (symbol? form)
                              (when-not (or (contains? narrowed form)
                                            (contains? seen form))
                                (if-let [{bound-form :form bound-env :env}
                                         (binding-value env form)]
                                  (require-closure! function-name bound-form bound-env
                                                    param-indexes narrowed
                                                    (conj seen form))
                                  (mark-param! function-name
                                               (get param-indexes form))))
                              (seq? form)
                              (let [[op & args] form]
                                (cond
                                  (= op 'let)
                                  (let [[bindings body] args]
                                    (loop [pairs (partition 2 bindings) current env]
                                      (if-let [[name value] (first pairs)]
                                        (recur (next pairs)
                                               (assoc current name {:form value
                                                                    :env current}))
                                        (require-closure! function-name body current
                                                          param-indexes narrowed seen))))
                                  (= op 'if)
                                  (doseq [branch (rest args)]
                                    (require-closure! function-name branch env
                                                      param-indexes narrowed seen))
                                  (= op 'do)
                                  (when-let [tail (last args)]
                                    (require-closure! function-name tail env
                                                      param-indexes narrowed seen))
                                  (and (contains? function-names op)
                                       (not (closure-dispatcher-function? op)))
                                  (mark-result! op)
                                  :else nil))
                              :else nil)))
                        (scan-calls! [function-name form env param-indexes narrowed]
                          (when (seq? form)
                            (if (closure-literal? form)
                              (let [[_ lambda-id capture-chain] form
                                    {:keys [captures helper]}
                                    (lambda-info-for-id lambda-id)
                                    capture-values (pair-chain-values capture-chain)
                                    capture-count (count captures)]
                                (doseq [capture capture-values]
                                  (scan-calls! function-name capture env param-indexes
                                               narrowed))
                                (doseq [index (get-in @next-facts
                                                     [(:name helper) :params] #{})
                                        :when (< index capture-count)]
                                  (when-let [capture (nth capture-values index nil)]
                                    (require-closure! function-name capture env
                                                      param-indexes narrowed #{}))))
                              (let [[op & args] form]
                                (cond
                                (= op 'let)
                                (let [[bindings body] args]
                                  (loop [pairs (partition 2 bindings) current env]
                                    (if-let [[name value] (first pairs)]
                                      (do (scan-calls! function-name value current
                                                       param-indexes narrowed)
                                          (recur (next pairs)
                                                 (assoc current name {:form value
                                                                      :env current})))
                                      (scan-calls! function-name body current
                                                   param-indexes narrowed))))
                                (= op 'if)
                                (let [[test then else] args
                                      nonzero-symbol (zero-tested-symbol test)]
                                  (scan-calls! function-name test env param-indexes narrowed)
                                  (scan-calls! function-name then env param-indexes narrowed)
                                  (scan-calls! function-name else env param-indexes
                                               (cond-> narrowed
                                                 nonzero-symbol (conj nonzero-symbol))))
                                :else
                                (do
                                  (doseq [arg args]
                                    (scan-calls! function-name arg env param-indexes
                                                 narrowed))
                                  ;; A dispatcher multiplexes lambdas whose
                                  ;; argument positions may have different
                                  ;; representation refinements.  Candidate-
                                  ;; specific requirements belong on each
                                  ;; helper entry, not on the shared dispatcher
                                  ;; argument (only its closure handle is a
                                  ;; uniform checked position).
                                  (when (and (contains? function-names op)
                                             (not (closure-dispatcher-function?
                                                   function-name)))
                                    (doseq [index (get-in @next-facts
                                                         [op :params] #{})]
                                      (when-let [arg (nth args index nil)]
                                        (require-closure! function-name arg env
                                                          param-indexes narrowed
                                                          #{}))))))))))]
                  (doseq [{:keys [name params body]} functions]
                    (let [param-indexes (zipmap params (range))]
                      (when (= :closure (expression-status
                                         name body {} param-indexes @next-facts #{}))
                        (mark-result! name))
                      (when (get-in @next-facts [name :result?])
                        (require-closure! name body {} param-indexes #{} #{}))
                      (scan-calls! name body {} param-indexes #{})))
                  @next-facts)))]
      (let [facts
            (loop [facts seed iteration 0]
              (let [next-facts (analyze-pass facts)]
                (cond
                  (= facts next-facts) facts
                  (>= iteration refinement-count-limit)
                  (reject! "closure refinement inference did not converge"
                           {:iterations iteration})
                  :else (recur next-facts (inc iteration)))))]
        (mapv
         (fn [{:keys [name param-types result] :as function}]
           (let [indexes (vec (sort (get-in facts [name :params] #{})))
                 result? (true? (get-in facts [name :result?]))]
             (doseq [index indexes]
               (when-not (= :i64 (nth param-types index nil))
                 (reject! "closure refinement requires an i64 parameter"
                          {:function name :parameter-index index})))
             (when (and result? (not= :i64 result))
               (reject! "closure refinement requires an i64 result"
                        {:function name :result result}))
             (cond-> function
               (seq indexes) (assoc :closure-param-indexes indexes)
               result? (assoc :closure-result? true))))
         functions)))))

(defn- rewrite-record-projections
  "Apply `rewrite-record-projection` to every function body. Only modules that
  declare param types can resolve the sugar; untyped modules are left alone and
  a 2-arity `record-get` there fails closed in validation as before."
  ([functions] (rewrite-record-projections functions {} {}))
  ([functions schemas] (rewrite-record-projections functions schemas {}))
  ([functions schemas protocol-dispatch]
   (let [signatures (into {} (map (fn [{:keys [name params param-types result]}]
                                    [name {:params params :param-types param-types
                                           :result result}])
                                  functions))]
     ;; Every body, including a parameterless one. The guard used to be
     ;; `(seq param-types)`, on the reading that a function with no parameters
     ;; has no local types to resolve against -- true for the 2-arity
     ;; `record-get` sugar, and false for everything else this pass does.
     ;;
     ;; A `[:ref :ns/name]` in `record-new`/`record-assoc`/`record-equal`
     ;; resolves through the namespace's `:schemas` map, not through locals, so
     ;; skipping the body left the reference unresolved and validation rejected
     ;; the program:
     ;;
     ;;   (defn f [] [:ref :p/n] (record-new [:ref :p/n] 1 5))
     ;;   -> record constructor must exactly match its descriptor
     ;;   (defn f [x :i64] [:ref :p/n] (record-new [:ref :p/n] x 5))
     ;;   -> compiles
     ;;
     ;; Adding one unused parameter made the same program legal, which is the
     ;; shape of a bug rather than a rule. `rewrite-record-projection` already
     ;; tolerates an empty locals map -- it only consults locals for inference,
     ;; and an untypeable binding is allowed to have no known type there.
     ;; This rewrite may synthesize exact heterogeneous-vector suffix
     ;; bindings after the parse/desugar binding has unwound. Give that pass
     ;; its own source-order counter instead of falling back to gensym, so KIR
     ;; and conformance digests stay reproducible across compiler processes.
     ;; Prefixes are reserved and distinct from earlier desugar temporaries,
     ;; so restarting the counter here cannot collide with authored or
     ;; previously synthesized bindings.
     (binding [*record-protocol-dispatch* protocol-dispatch
               *synthetic-counter* (volatile! 0)]
       (mapv (fn [{:keys [params param-types] :as f}]
               (update f :body rewrite-record-projection
                       (zipmap params param-types) signatures schemas))
             functions)))))

(defn- check-value-types! [functions]
  (let [signatures (into {} (map (fn [{:keys [name params param-types result]}]
                                   [name {:params params :param-types param-types
                                          :result result}])
                                 functions))]
    (doseq [{:keys [name params param-types result body]} functions]
      (let [actual (infer-expression-type body (zipmap params param-types) signatures)]
        (require-expression-type! actual result name)))
    (let [nodes (mapcat #(tree-seq coll? seq (:body %)) functions)
          literal-bytes
          (reduce + 0
                  (map value/utf8-byte-count!
                       (filter string? nodes)))
          keyword-bytes
          (reduce + 0
                  (map (comp value/utf8-byte-count! str)
                       (filter keyword? nodes)))]
      (when (> literal-bytes value/string-value-byte-limit)
        (reject! "module string literals exceed UTF-8 byte limit" literal-bytes))
      (when (> keyword-bytes value/string-value-byte-limit)
        (reject! "module keyword literals exceed UTF-8 byte limit" keyword-bytes)))))

(defn- linear-typed-cap-call?
  "True when `form` is a 5-element typed-cap-call whose result type is a
  linear task/stream resource."
  [form]
  (and (seq? form)
       (= 'typed-cap-call (first form))
       (= 5 (count form))
       (linear-resource-type? (nth form 3))))

(defn- linear-consume-head?
  [op]
  (contains? '#{bytes-task-byte-count task-ready?} op))

(defn- form-contains-linear-call?
  [form]
  (boolean (some linear-typed-cap-call? (tree-seq coll? seq form))))

(defn- mentions-sym?
  [form sym]
  (boolean (some #(= % sym) (tree-seq coll? seq form))))

(defn- exclusive-use-of-linear
  "If `form` exclusively moves or consumes `sym` (no other linear calls),
  returns `{:kind :move|:consume}`. Returns nil on mismatch.

  ADR 0138: balanced `if` arms (same kind).
  ADR 0139: pure non-linear nested `let` wrappers — needed for `case` /
  `condp` which desugar to `(let [tmp dispatch] (if …))` multi-arm chains."
  [form sym]
  (cond
    (= form sym)
    {:kind :move}

    (and (seq? form)
         (linear-consume-head? (first form))
         (= 2 (count form))
         (= sym (second form)))
    {:kind :consume}

    ;; ADR 0138: balanced if — both arms exclusive-use sym the same way;
    ;; test must not mention sym or produce linear calls.
    (and (seq? form) (= 'if (first form)) (>= (count form) 3))
    (let [test (nth form 1)
          then (nth form 2)
          else (when (>= (count form) 4) (nth form 3))]
      (when (and else
                 (not (mentions-sym? test sym))
                 (not (form-contains-linear-call? test)))
        (let [t (exclusive-use-of-linear then sym)
              e (exclusive-use-of-linear else sym)]
          (when (and t e (= (:kind t) (:kind e)))
            t))))

    ;; ADR 0139: non-linear let wrappers (case/condp dispatch temps).
    (and (seq? form) (= 'let (first form)) (vector? (second form))
         (even? (count (second form))))
    (let [bindings (second form)
          body-forms (nnext form)
          result-expr (when (= 1 (count body-forms)) (first body-forms))
          pairs (when result-expr (partition 2 bindings))]
      (when (and result-expr
                 (seq pairs)
                 (every? (fn [[name value]]
                           (and (simple-symbol? name)
                                (not= name sym)
                                (not (mentions-sym? value sym))
                                (not (form-contains-linear-call? value))))
                         pairs))
        (exclusive-use-of-linear result-expr sym)))

    :else nil))

(defn- linear-let-move
  "ADR 0137–0142: admit forms that bind exactly one linear typed-cap-call
  (possibly among non-linear bindings) and exclusively move or consume it.

  ADR 0138: multi-binding companions, nested non-linear outers, balanced if.
  ADR 0139: exclusive-use walks non-linear lets so multi-arm `case` / `cond` /
  `condp` (desugared to nested if + dispatch lets) are admitted when every
  arm exclusive-uses the binding the same way.
  ADR 0142: one-arm linear `if` — linear produce+consume fully closed inside
  exactly one arm; the other arm has no linear calls (conditional get).

  Returns the underlying typed-cap-call when admitted, else nil."
  [body]
  (letfn [(walk [form]
            (cond
              (linear-typed-cap-call? form)
              form

              (and (seq? form)
                   (linear-consume-head? (first form))
                   (= 2 (count form))
                   (linear-typed-cap-call? (second form)))
              (second form)

              (and (seq? form) (= 'let (first form)) (vector? (second form))
                   (even? (count (second form))))
              (let [bindings (second form)
                    body-forms (nnext form)
                    result-expr (when (= 1 (count body-forms)) (first body-forms))]
                (when result-expr
                  (let [pairs (partition 2 bindings)
                        linear-pairs (filter (fn [[_ v]] (linear-typed-cap-call? v)) pairs)
                        non-linear-pairs (remove (fn [[_ v]] (linear-typed-cap-call? v)) pairs)]
                    (cond
                      ;; Exactly one linear binding (+ optional non-linear companions)
                      (and (= 1 (count linear-pairs))
                           (every? (fn [[name value]]
                                     (and (simple-symbol? name)
                                          (not (form-contains-linear-call? value))))
                                   non-linear-pairs))
                      (let [[sym call] (first linear-pairs)]
                        (when (and (simple-symbol? sym)
                                   (every? (fn [[_ v]] (not (mentions-sym? v sym)))
                                           non-linear-pairs)
                                   (exclusive-use-of-linear result-expr sym))
                          call))

                      ;; Pure non-linear outer wrappers — recurse into body
                      (and (empty? linear-pairs)
                           (seq pairs)
                           (every? (fn [[name value]]
                                     (and (simple-symbol? name)
                                          (not (form-contains-linear-call? value))))
                                   pairs))
                      (walk result-expr)

                      :else nil))))

              ;; ADR 0142: one-arm linear if — produce+consume closed in one arm
              (and (seq? form) (= 'if (first form)) (>= (count form) 3))
              (let [test (nth form 1)
                    then (nth form 2)
                    else (if (>= (count form) 4) (nth form 3) 0)]
                (when-not (form-contains-linear-call? test)
                  (let [then-lin (form-contains-linear-call? then)
                        else-lin (form-contains-linear-call? else)]
                    (cond
                      (and then-lin (not else-lin)) (walk then)
                      (and else-lin (not then-lin)) (walk else)
                      ;; both arms linear: require the same producer call form
                      (and then-lin else-lin)
                      (let [t (walk then) e (walk else)]
                        (when (and t e (= t e)) t))
                      :else nil))))

              :else nil))]
    (walk body)))

(defn- check-linear-resource-ownership! [functions]
  (doseq [{:keys [param-types result body] :as function} functions]
    (when (some linear-resource-type? param-types)
      (reject! "linear resources require move-aware parameters"
               (:name function)))
    (let [linear-calls
          (->> (tree-seq coll? seq body)
               (keep (fn [form]
                       (when (linear-typed-cap-call? form) form)))
               vec)
          direct
          (cond
            (linear-typed-cap-call? body)
            body

            (and (seq? body)
                 (linear-consume-head? (first body))
                 (= 2 (count body))
                 (linear-typed-cap-call? (second body)))
            (second body)

            ;; ADR 0137–0139: let-bound affine move / consume (+ if/case arms)
            :else
            (linear-let-move body))]
      (when (or (and (linear-resource-type? result)
                     (or (nil? direct)
                         (not= result (nth direct 3))))
                (and (seq linear-calls)
                     (not= [direct] linear-calls)))
        (reject! "linear result must be one direct typed capability move"
                 (:name function))))))

;; ---------------------------------------------------------------------------
;; Kernel region provenance.
;;
;; `kernel-load-u8`/`kernel-store-u8`/... take (base, length, index, ...) and
;; the native backends emit a real bounds check before the access: length must
;; not exceed the op's static maximum, base must be non-zero, index must be
;; below length, and any violation reaches `UD2`/`brk` before memory is
;; touched. That check constrains the offset WITHIN a window; it says nothing
;; about whether the window itself is legitimate. Until this pass, `base` was
;; any `:i64` the program could compute, so
;;
;;   (kernel-load-u8 (kernel-load-u8 attacker-buf len i) 4096 0)
;;
;; -- take a byte of attacker-controlled data, use it as a physical address --
;; passed admission. These objects run in ring 0, so that is arbitrary
;; physical memory, and no amount of index checking recovers it.
;;
;; Ring 0 code cannot be forbidden from naming addresses; a kernel's whole job
;; is to address device MMIO and physical frames. What it CAN be held to is
;; that every address is TRACEABLE: each base must flow unmodified from a
;; compile-time literal, from `kernel-boot-info`, or from a parameter — never
;; from arithmetic, a load, or a call result. The set of physical windows an
;; object can reach then becomes statically enumerable and reviewable instead
;; of data-dependent.
;;
;; Parameters make this interprocedural: aiueos threads a base through
;; recursive helpers (`aiueos-fnv1a-step base length index hash`), so a param
;; used as a base taints that position, every internal call into it must pass
;; a traceable argument, and the taint propagates to the caller's own params
;; by fixpoint. A tainted param on a function with no internal caller is the
;; ABI boundary where the C kernel supplies the region: unverifiable from
;; here, so it is admitted and REPORTED (`kernel-region-report`) rather than
;; silently trusted -- the same localize-and-name discipline the raw-memory
;; gate uses, since the alternative is to keep pretending the boundary is not
;; there.
(defn- kernel-memory-op? [op]
  (contains? kernel-memory-operations op))

(defn- let-binding-pairs
  "Seq of [sym init] for a desugared `(let [s0 v0 s1 v1 ...] body)`."
  [bindings]
  (when (vector? bindings)
    (partition 2 bindings)))

(defn- traceable-base?
  "True when EXPR is ROOTED: it resolves to a compile-time literal, to
  `kernel-boot-info`, or to a parameter, possibly plus an offset. Under ENV
  (let-bound symbol -> init expression) and PARAMS (this function's parameter
  symbols).

  Narrowing a validated region to a sub-window is what real kernel code does
  -- aiueos hashes a record inside a block it just range-checked, in six of
  its objects -- so it must be expressible, but `(+ base offset)` produced a
  window nothing had checked. It is now spelled `(kernel-subregion base
  length offset sublen)`, which the native backends emit as a real check:
  offset within length, sublen within the remainder, non-null parent, `UD2`/
  `brk` otherwise. So a derived base is rooted AND bounded, and a correct
  entry window implies every window derived from it is correct.

  Bare `+` in a base position is therefore rejected now (it was admitted, and
  reported as an unchecked narrowing, while no checked form existed). What
  stays rejected for the same reason as before is a base with no traceable
  root at all:

    (kernel-load-u8 (kernel-load-u8 attacker-buf len i) 4096 0)

  Anything not listed here -- a bare load, a call result, a cap-call -- fails
  closed."
  [expr env params]
  (letfn [(clean? [expr seen]
            (cond
              (integer? expr) true
              (and (seq? expr) (= 'kernel-boot-info (first expr))) true
              ;; A checked sub-window. Its own parent base sits in argument
              ;; position 0 and is validated as a base in its own right by
              ;; `kernel-base-uses`, so recursing here would double-report.
              (and (seq? expr) (= 'kernel-subregion (first expr))) true
              ;; one of two rooted origins is still rooted
              (and (seq? expr) (= 'if (first expr)) (= 4 (count expr)))
              (and (clean? (nth expr 2) seen) (clean? (nth expr 3) seen))
              (symbol? expr)
              (cond
                (contains? seen expr) false          ; cyclic shadowing, fail closed
                (contains? env expr) (clean? (get env expr) (conj seen expr))
                (contains? params expr) true         ; ABI boundary, tracked below
                :else false)
              :else false))]
    (clean? expr #{})))

(defn- derived-base?
  "True when EXPR narrows a region to a sub-window. Now always a checked
  narrowing (`kernel-subregion`); `kernel-region-report` still lists these so
  a build can see which windows are derived and from what, but they are no
  longer the unchecked residual they were before the primitive existed."
  [expr]
  (and (seq? expr) (= 'kernel-subregion (first expr))))

(defn- kernel-base-uses
  "Walk BODY collecting, for one function:
    :problems  base expressions that are not traceable
    :params    parameter symbols that reach a base position
    :literals  compile-time-literal bases
    :calls     [callee arg-index arg-expr env] for every internal call, so the
               caller can be checked once callee taint is known
  ENV threading follows `let`; a binding shadows an outer one of the same name."
  [body params function-names]
  (let [problems (volatile! [])
        used-params (volatile! #{})
        literals (volatile! #{})
        derived (volatile! [])
        calls (volatile! [])]
    (letfn [(base! [expr env]
              (cond
                (integer? expr) (vswap! literals conj expr)
                (symbol? expr) (when (contains? params expr)
                                 (vswap! used-params conj expr))
                :else nil)
              (when (derived-base? expr)
                (vswap! derived conj
                        {:base expr
                         :offset-static? (every? integer? (drop 3 expr))}))
              (when-not (traceable-base? expr env params)
                (vswap! problems conj expr))
              ;; a let-bound alias of a param still counts as reaching it
              (when (and (symbol? expr) (contains? env expr))
                (let [root (get env expr)]
                  (when (and (symbol? root) (contains? params root))
                    (vswap! used-params conj root)))))
            (walk [expr env]
              (when (seq? expr)
                (let [[op & args] expr]
                  (cond
                    (= op 'let)
                    (let [[bindings & tail] args
                          env' (reduce (fn [acc [sym init]]
                                         (walk init acc)
                                         (assoc acc sym init))
                                       env
                                       (let-binding-pairs bindings))]
                      (doseq [form tail] (walk form env')))

                    (kernel-memory-op? op)
                    ;; `args` in full, not `(rest args)`: a nested
                    ;; `kernel-subregion` sitting IN a base position has its
                    ;; own parent in its own argument 0, and skipping arg 0
                    ;; here let a narrowing launder an untraceable base --
                    ;; `(kernel-subregion (kernel-load-u8 buf len 0) ...)`
                    ;; passed until a test went looking for it.
                    (do (base! (first args) env)
                        (doseq [arg args] (walk arg env)))

                    :else
                    (do (when (contains? function-names op)
                          (doseq [[i arg] (map-indexed vector args)]
                            (vswap! calls conj [op i arg env])))
                        (doseq [arg args] (walk arg env)))))))]
      (walk body {})
      {:problems @problems :params @used-params
       :literals @literals :derived @derived :calls @calls})))

(defn kernel-region-report
  "Static region provenance for FUNCTIONS: the literal physical bases the
  module can reach, whether it consults `kernel-boot-info`, the ABI
  boundary -- `{function [param ...]}` for base parameters no internal call
  supplies, i.e. the regions the C kernel is trusted to hand in -- and
  `:derived-bases`, every `kernel-subregion` narrowing, flagged
  `:offset-static?` when both the offset and the sub-length are literals.
  Every narrowing is now checked at runtime by the emitted code, so a
  non-static one is no longer an unbounded window -- the flag distinguishes
  what a build can verify statically from what the trap enforces. Public so a
  build can record what a kernel object is allowed to address, and how much
  of that is still trust, instead of rediscovering it by reading the source."
  [functions]
  (let [function-names (into #{} (map :name) functions)
        facts (into {}
                    (map (fn [{:keys [name params body]}]
                           [name (kernel-base-uses body (set params) function-names)]))
                    functions)
        params-by-name (into {} (map (juxt :name :params)) functions)
        ;; fixpoint: a param position is base-tainted when it is used as a base
        ;; directly, or passed into an already-tainted position of a callee.
        tainted
        (loop [tainted (into {}
                             (map (fn [[name {:keys [params]}]]
                                    [name (into #{}
                                                (keep-indexed
                                                 (fn [i p] (when (contains? params p) i)))
                                                (get params-by-name name))]))
                             facts)]
          (let [next-tainted
                (reduce
                 (fn [acc [caller {:keys [calls]}]]
                   (reduce
                    (fn [acc [callee i arg _env]]
                      (if (and (contains? (get acc callee #{}) i) (symbol? arg))
                        (let [caller-params (get params-by-name caller)
                              idx (first (keep-indexed
                                          (fn [j p] (when (= p arg) j)) caller-params))]
                          (if idx (update acc caller (fnil conj #{}) idx) acc))
                        acc))
                    acc calls))
                 tainted facts)]
            (if (= next-tainted tainted) tainted (recur next-tainted))))
        supplied (into #{}
                       (mapcat (fn [[_caller {:keys [calls]}]]
                                 (keep (fn [[callee i _arg _env]]
                                         (when (contains? (get tainted callee #{}) i)
                                           [callee i]))
                                       calls)))
                       facts)]
    {:literal-bases (into (sorted-set) (mapcat (comp :literals val)) facts)
     ;; Both shapes count: a narrowing written directly in a base position,
     ;; and one passed as an argument into a base parameter -- which is how
     ;; aiueos actually writes it, `(fnv (+ base object-offset) len)`, so
     ;; collecting only the direct form would report an empty list on the
     ;; very files that motivated admitting derivation at all.
     :derived-bases
     (into (into [] (mapcat (fn [[name {:keys [derived]}]]
                              (map #(assoc % :function name) derived)))
                 facts)
           (mapcat (fn [[caller {:keys [calls]}]]
                     (keep (fn [[callee i arg _env]]
                             (when (and (contains? (get tainted callee #{}) i)
                                        (derived-base? arg))
                               {:base arg
                                :offset-static? (every? integer? (drop 3 arg))
                                :function caller
                                :into [callee i]}))
                           calls)))
           facts)
     :uses-boot-info?
     (boolean (some (fn [{:keys [body]}]
                      (some #(and (seq? %) (= 'kernel-boot-info (first %)))
                            (tree-seq coll? seq body)))
                    functions))
     :tainted tainted
     :abi-boundary
     (into (sorted-map)
           (keep (fn [[name idxs]]
                   (let [unsupplied (remove #(contains? supplied [name %]) idxs)]
                     (when (seq unsupplied)
                       [name (mapv #(nth (get params-by-name name) %) (sort unsupplied))]))))
           tainted)}))

(defn- check-kernel-region-provenance! [functions]
  (let [function-names (into #{} (map :name) functions)]
    (when (some (fn [{:keys [body]}]
                  (some #(and (seq? %) (kernel-memory-op? (first %)))
                        (tree-seq coll? seq body)))
                functions)
      (let [{:keys [tainted]} (kernel-region-report functions)]
        (doseq [{:keys [name params body]} functions]
          (let [{:keys [problems calls]} (kernel-base-uses body (set params) function-names)]
            (when-let [offender (first problems)]
              (reject! "kernel memory base must name a region, not compute one"
                       offender :kotoba.error/kernel-region-provenance))
            ;; an argument flowing into a base position must be traceable too,
            ;; or the caller becomes the hole the callee's own check closed
            (doseq [[callee i arg env] calls
                    :when (contains? (get tainted callee #{}) i)]
              (when-not (traceable-base? arg env (set params))
                (reject! "kernel memory base must name a region, not compute one"
                         arg :kotoba.error/kernel-region-provenance)))))))))

(defn- direct-facts [form function-names]
  (let [effects (volatile! #{}) calls (volatile! #{})]
    (letfn [(walk [x]
              (cond
                (seq? x)
                (let [[op & args] x]
                  (cond
                    (= op 'cap-call)
                    (do (vswap! effects conj
                                [:cap/call (effect-capability-id (first args))])
                        (walk (second args)))
                    (= op 'typed-cap-call)
                    (do (vswap! effects conj
                                [:cap/call (effect-capability-id (first args))])
                        (walk (nth args 3)))
                    (contains? function-names op)
                    (do (vswap! calls conj op) (doseq [arg args] (walk arg)))
                    :else (doseq [arg args] (walk arg))))
                (coll? x) (doseq [item x] (walk item))))]
      (walk form)
      {:effects @effects :calls @calls})))

(defn- infer-effects [functions]
  (let [names (set (map :name functions))
        direct (into {} (map (fn [{:keys [name body]}]
                               [name (direct-facts body names)])) functions)]
    (loop [inferred (into {} (map (fn [[name facts]] [name (:effects facts)]) direct))]
      (let [next-effects
            (into {} (map (fn [[name {direct-effects :effects calls :calls}]]
                            [name (reduce set/union direct-effects
                                          (map #(get inferred % #{}) calls))])
                          direct))]
        (if (= inferred next-effects) inferred (recur next-effects))))))

(defn- bounded-sum [values]
  (reduce (fn [total value]
            (min (inc max-lowered-nodes) (+ total value)))
          0 values))

(defn- lowered-cost [form env]
  (cond
    (kotoba-integer? form) 1
    (value/f64-value? form) 1
    (string? form) 1
    (keyword? form) 1
    (boolean? form) 1
    (vector? form) (bounded-sum (cons 1 (map #(lowered-cost % env) form)))
    (symbol? form) (get env form 1)
    :else
    (let [[op & args] form]
      (if (= op 'let)
        (let [[bindings body] args
              env' (reduce (fn [current [name value]]
                             (assoc current name (lowered-cost value current)))
                           env (partition 2 bindings))]
          (lowered-cost body env'))
        (bounded-sum (cons 1 (map #(lowered-cost % env) args)))))))

(defn- check-lowering-budget! [functions]
  (let [cost (bounded-sum (map #(lowered-cost (:body %) {}) functions))]
    (when (> cost max-lowered-nodes)
      (reject! "lowered program budget exhausted" cost))))

(defn- check-namespace-capabilities!
  "ADR-2607182410 declare-then-check for an optional `ns` `:capabilities`
  clause: DECLARED (namespace-parts' :capabilities) must equal exactly what
  was actually USED via a named `(cap-call :some/name ...)` anywhere in the
  namespace (collected into *used-capability-keywords* as each is resolved
  during desugaring) -- both directions are rejected, mirroring the
  `:aiueos/imports` declare-then-check convention this org already uses
  elsewhere (orgs/kotoba-lang/aiueos/examples/apps/notes.edn). A no-arg-
  cap-call-by-int module has an empty `used` set regardless -- this check
  only ever fires when the `ns` form actually wrote a `:capabilities`
  clause (`declared` is nil otherwise, see analyze's call site)."
  [declared used]
  (when declared
    (let [undeclared (set/difference used declared)
          unused (set/difference declared used)]
      (when (seq undeclared)
        ;; Keep the historical message token so existing suites match, while
        ;; including the semantic operation names for W1 diagnostics.
        (reject! (str "cap-call uses a capability not declared in namespace :capabilities: "
                      (pr-str undeclared))
                 undeclared))
      (when (seq unused)
        (reject! (str "namespace :capabilities declares a capability never used via cap-call: "
                      (pr-str unused))
                 unused)))))

(defn- param-name+wrap
  "For one `defn` PARAM: a plain symbol is kept as-is (identity wrap). A
  vector/map destructuring pattern (ADR-2607150000) gets a fresh gensym'd
  parameter name, plus a body-wrapping fn that binds the pattern from that
  gensym via a `let` -- reusing desugar-expr's own `let`-destructuring
  (above) rather than duplicating it: `(defn f [{:keys [a]}] body)`
  becomes params `[tmp]`, body `(let [{:keys [a]} tmp] body)`, which then
  goes through desugar-expr exactly like any other `let`. Returns
  `[param-symbol wrap-fn]`."
  [param]
  (if (symbol? param)
    [param identity]
    (let [tmp (synthetic "param-destr")]
      [tmp (fn [body] (list 'let [param tmp] body))])))

(defn- type-alias-form? [value]
  (and (vector? value) (= 2 (count value)) (= :alias (first value))
       (symbol? (second value))))

(defn- resolve-type-alias! [type constants]
  (if (type-alias-form? type)
    (let [name (second type)]
      (when-not (contains? constants name)
        (reject! "type alias must name a declared constant" type))
      (let [resolved (get constants name)]
        (validate-value-type! resolved)
        resolved))
    type))

(defn- normalize-effect-ceiling
  "Translate a public effect ceiling declared as capability keywords into the
  same `[:cap/call id]` row shape `infer-effects` produces."
  [ceiling form]
  (when (some? ceiling)
    (when-not (and (set? ceiling) (seq ceiling) (every? keyword? ceiling))
      (reject! "effect ceiling must be a non-empty set of capability keywords" form))
    (into #{}
          (map (fn [kw]
                 (if-let [id (get capability-registry kw)]
                   [:cap/call id]
                   (reject! (str "effect ceiling names unregistered capability: " kw)
                            form))))
          ceiling)))

(defn- defn-parts
  "Parse Kotoba's bounded function declaration shape. A docstring is inert
  metadata and is deliberately discarded before lowering. An optional result
  keyword follows the parameter vector: `(defn f [s :string] :string s)`.
  An optional public effect ceiling map may follow the result (or params):
  `(defn f [x] {:effects #{:clock/now}} (clock/now x))`. Inferred effects
  outside that ceiling fail closed. Other attributes remain outside the profile."
  [form constants]
  (let [[_ name & declaration] form
        [docstring declaration] (if (string? (first declaration))
                                  [(first declaration) (rest declaration)]
                                  [nil declaration])
        raw-params (first declaration)
        tail (rest declaration)
        [result tail] (if (or (keyword? (first tail))
                              (structured-type? (first tail))
                              (type-alias-form? (first tail)))
                        [(resolve-type-alias! (first tail) constants) (rest tail)]
                        ;; No annotation: `:i64` is provisional. `infer-absent-results`
                        ;; replaces it with the body's inferred type, so an
                        ;; unannotated `defn` can return a predicate.
                        [::absent tail])
        ceiling-form (first tail)
        [effects-ceiling body]
        (if (and (map? ceiling-form)
                 (contains? ceiling-form :effects)
                 (= #{:effects} (set (keys ceiling-form))))
          [(normalize-effect-ceiling (:effects ceiling-form) form) (rest tail)]
          [nil tail])]
    (when (and docstring (> (count docstring) max-function-docstring-chars))
      (reject! "function docstring exceeds admission limit" docstring))
    (when-not (= ::absent result) (validate-value-type! result))
    (cond-> {:name name :raw-params raw-params
             :result (if (or (= ::absent result) (callable-type? result)) :i64 result)
             :body body}
      (= ::absent result) (assoc :result-inferred? true)
      (callable-type? result) (assoc :callable-result-contract result)
      effects-ceiling (assoc :effects-ceiling effects-ceiling))))

(declare typed-param-parts)

(defn- multi-arity-declaration?
  [declaration]
  (and (seq declaration)
       (every? #(and (seq? %) (vector? (first %))) declaration)))

(defn- abi-arity-name [source-name arity]
  (symbol (str (name source-name) "$arity$" arity)))

(defn- expand-defn-parts
  "Return one or more monomorphic clauses for a source defn. Multi-arity is
  syntax-only: every call is resolved before HIR and no backend performs
  argument-count dispatch (ADR 0017)."
  [form constants]
  (let [[op source-name & declaration0] form
        [docstring declaration] (if (string? (first declaration0))
                                  [(first declaration0) (rest declaration0)]
                                  [nil declaration0])]
    (when (and docstring (> (count docstring) max-function-docstring-chars))
      (reject! "function docstring exceeds admission limit" docstring))
    (when (re-find #"\$arity\$" (name source-name))
      (reject! "function name uses reserved multi-arity ABI marker" source-name))
    (if-not (multi-arity-declaration? declaration)
      [(assoc (defn-parts form constants) :source-name source-name :public? (= op 'defn))]
      (do
        (when (> (count declaration) max-arity-clauses)
          (reject! "multi-arity clause count exceeds admission limit" form))
        (let [clauses
              (mapv (fn [clause]
                      (let [raw (defn-parts (list* op source-name clause) constants)
                            param-parts (typed-param-parts (:raw-params raw) constants)
                            arity (count param-parts)]
                        (when (some #{'&} (:raw-params raw))
                          (reject! "variadic parameters are outside the multi-arity profile" (:raw-params raw)))
                        (assoc raw :source-name source-name :logical-arity arity
                               :public? (= op 'defn))))
                    declaration)
              arities (mapv :logical-arity clauses)]
          (when-not (= (count arities) (count (distinct arities)))
            (reject! "duplicate multi-arity clause" form))
          (mapv #(assoc % :name (abi-arity-name source-name (:logical-arity %))) clauses))))))

(defn- resolve-overloaded-calls
  [form overloads overloaded-sources]
  (cond
    (seq? form)
    (let [[op & args] form]
      (if (= 'quote op)
        form
        (let [resolved-op (if (symbol? op)
                            (get overloads [op (count args)] op)
                            op)
              _ (when (and (contains? overloaded-sources op) (= resolved-op op))
                  (reject! "no matching multi-arity clause" form))
              result (list* resolved-op
                            (map #(resolve-overloaded-calls % overloads overloaded-sources) args))]
          (if (seq (meta form)) (with-meta result (meta form)) result))))
    (vector? form) (mapv #(resolve-overloaded-calls % overloads overloaded-sources) form)
    (map? form) (into (empty form)
                      (map (fn [[k v]] [(resolve-overloaded-calls k overloads overloaded-sources)
                                       (resolve-overloaded-calls v overloads overloaded-sources)]))
                      form)
    :else form))

(defn- typed-param-parts
  "Legacy `[x y]` remains two i64 parameters. Once any type keyword appears,
  the whole vector must be alternating `[name :type ...]`; this keeps the
  source grammar deterministic and makes every non-i64 host boundary explicit."
  [raw-params constants]
  (let [raw-params (mapv (fn [index item]
                           (if (and (odd? index) (type-alias-form? item))
                             (resolve-type-alias! item constants)
                             item))
                         (range) raw-params)]
  (if (or (some keyword? raw-params)
          (and (even? (count raw-params))
               (some structured-type? (map second (partition 2 raw-params)))))
    (do
      (when-not (even? (count raw-params))
        (reject! "typed parameters require alternating name/type pairs" raw-params))
      (mapv (fn [[pattern type]]
              (validate-value-type! type)
              (when (and (or (contains? #{:f32 :f64 :string :keyword :map :option-i64 :result-i64 :vector-i64 :vector-f64 :string-index :disjoint-set-i64 :document} type)
                             (structured-type? type))
                         (not (or (symbol? pattern)
                                  (and (= type :map) (map? pattern))
                                  (and (contains? #{:vector-i64 :vector-f64} type)
                                       (vector? pattern))
                                  (and (heterogeneous-vector-type? type)
                                       (vector? pattern))
                                  (and (or (canonical-typed-map-type? type)
                                           (record-type? type)
                                           (schema-ref-type? type))
                                       (map? pattern)))))
                (reject! "typed values require plain-symbol bindings" pattern))
              (cond-> {:pattern pattern
                       :type (if (callable-type? type) :i64 type)}
                (callable-type? type) (assoc :callable-contract type)))
            (partition 2 raw-params)))
    (mapv (fn [pattern] {:pattern pattern :type :i64}) raw-params))))

(defn- binding-symbols [pattern]
  (->> (tree-seq coll? seq pattern)
       (filter symbol?)
       (remove #{'&})
       set))

(defn- constant-literal?
  "Closed compile-time data admitted for top-level `def`. Constants are
  substituted before desugaring, so they cannot allocate ambient mutable
  state or execute code during compilation."
  [value]
  (cond
    (kotoba-integer? value) true
    ;; Function-body f64 literals already lower through canonical IEEE-754
    ;; bits. A top-level constant is only lexically substituted into that same
    ;; path, so admitting a closed Double here adds no evaluation authority.
    (value/f64-value? value) true
    (string? value) (try
                      (value/bounded-string! value value/string-literal-byte-limit)
                      true
                      (catch #?(:clj Exception :cljs :default) _ false))
    (keyword? value) true
    (boolean? value) true
    (nil? value) true
    ;; Symbols are inert references at this stage. Resolution below admits
    ;; only names declared by another top-level constant and rejects unknown
    ;; names and cycles before any function is desugared.
    (symbol? value) true
    (vector? value) (or (type-alias-form? value)
                        (and (<= (count value) max-list-items)
                             (every? constant-literal? value)))
    ;; Keep inferred source sets deliberately narrow. Other item types use
    ;; `typed-set` with an explicit descriptor in function code.
    (set? value) (and (seq value)
                      (<= (count value) max-typed-set-items)
                      (every? keyword? value))
    (map? value) (and (<= (count value) max-list-items)
                      (every? constant-literal? (mapcat identity value)))
    :else false))

(defn- def-parts [form]
  (let [[_ name & declaration] form
        [docstring declaration] (if (and (= 2 (count declaration))
                                         (string? (first declaration)))
                                  [(first declaration) (rest declaration)]
                                  [nil declaration])]
    (when (and docstring (> (count docstring) max-function-docstring-chars))
      (reject! "constant docstring exceeds admission limit" docstring))
    (when-not (= 1 (count declaration))
      (reject! "constant must contain exactly one literal value" form))
    (let [value-form (first declaration)
          value (if (and (seq? value-form)
                         (= 'keyword (first value-form))
                         (= 2 (count value-form))
                         (string? (second value-form)))
                  (keyword (second value-form))
                  value-form)]
      (when-not (constant-literal? value)
        (reject! "constant value must be closed bounded integer/string/keyword/boolean/nil/vector/map or non-empty keyword-set data" value))
      {:name name :value value})))

(defn- resolve-constant-aliases!
  ([value constants] (resolve-constant-aliases! value constants #{}))
  ([value constants resolving]
   (cond
     (type-alias-form? value)
     (let [name (second value)]
       (when-not (contains? constants name)
         (reject! "constant alias must name a declared constant" value))
       (when (contains? resolving name)
         (reject! "constant aliases must be acyclic" value))
       (resolve-constant-aliases! (get constants name) constants (conj resolving name)))
     (symbol? value)
     (do
       (when-not (contains? constants value)
         (reject! "constant alias must name a declared constant" value))
       (when (contains? resolving value)
         (reject! "constant aliases must be acyclic" value))
       (resolve-constant-aliases! (get constants value) constants
                                  (conj resolving value)))
     (vector? value) (mapv #(resolve-constant-aliases! % constants resolving) value)
     (map? value) (into (empty value)
                        (map (fn [[key item]]
                               [(resolve-constant-aliases! key constants resolving)
                                (resolve-constant-aliases! item constants resolving)]))
                        value)
     :else value)))

(declare substitute-constants)

(defn- substitute-bindings
  [op bindings constants bound]
  (when-not (and (vector? bindings) (even? (count bindings)))
    (reject! (case op
               let "let requires an even binding vector"
               loop "loop requires an even binding vector")
             bindings))
  (loop [pairs (partition 2 bindings) bound bound out []]
    (if-let [[pattern value] (first pairs)]
      (recur (next pairs)
             (into bound (binding-symbols pattern))
             (conj out pattern (substitute-constants value constants bound)))
      [out bound])))

(defn- substitute-constants
  "Lexically substitute closed top-level constants without replacing call
  heads or names shadowed by params/let/loop bindings."
  [form constants bound]
  (cond
    (symbol? form) (if (and (not (contains? bound form))
                            (contains? constants form))
                     (get constants form)
                     form)
    (seq? form)
    (let [[op & args] form
          result (case op
                   quote form
                   (let loop) (let [[bindings & body] args
                                    [bindings' bound'] (substitute-bindings op bindings constants bound)]
                                (list* op bindings'
                                       (map #(substitute-constants % constants bound') body)))
                   (list* op (map #(substitute-constants % constants bound) args)))]
      (if (seq (meta form)) (with-meta result (meta form)) result))
    (vector? form) (mapv #(substitute-constants % constants bound) form)
    (set? form) (set (map #(substitute-constants % constants bound) form))
    (map? form) (into (empty form)
                      (map (fn [[k v]] [(substitute-constants k constants bound)
                                       (substitute-constants v constants bound)]))
                      form)
    :else form))

(defn- closed-multimethod-literal? [value]
  (or (kotoba-integer? value) (keyword? value) (boolean? value) (string? value)))

(defn- expand-closed-multimethod-forms [forms]
  (let [declarations (filter #(and (seq? %) (= 'defmulti (first %))) forms)
        methods (filter #(and (seq? %) (= 'defmethod (first %))) forms)
        declaration-names (mapv second declarations)]
    (when-not (= (count declaration-names) (count (distinct declaration-names)))
      (reject! "duplicate defmulti declaration" declarations))
    (let [declarations-by-name
          (into {}
                (map (fn [form]
                       (let [[_ name dispatch & extra] form]
                         (when-not (and (symbol? name) (nil? (namespace name))
                                        (symbol? dispatch) (nil? (namespace dispatch))
                                        (empty? extra))
                           (reject! "defmulti requires an unqualified name and one unqualified dispatch function symbol"
                                    form))
                         [name {:form form :dispatch dispatch}]))
                     declarations))
          methods-by-name
          (group-by second methods)]
      (doseq [form methods]
        (let [[_ name dispatch-value params & body] form]
          (when-not (contains? declarations-by-name name)
            (reject! "defmethod requires a matching defmulti declaration" form))
          (when-not (closed-multimethod-literal? dispatch-value)
            (reject! "defmethod dispatch value must be a bounded literal or :default" form))
          (when-not (and (vector? params) (<= (count params) max-parameters)
                         (every? #(and (symbol? %) (nil? (namespace %))) params)
                         (= (count params) (count (distinct params))))
            (reject! "defmethod parameters must be a unique vector of unqualified symbols within the ABI arity"
                     form))
          (when (empty? body)
            (reject! "defmethod requires at least one body expression" form))))
      (let [expanded
            (into {}
                  (map
                   (fn [[name {:keys [dispatch form]}]]
                     (let [method-forms (get methods-by-name name)]
                       (when (empty? method-forms)
                         (reject! "defmulti requires at least one closed-world defmethod" form))
                       (let [params (nth (first method-forms) 3)
                             _ (doseq [method method-forms]
                                 (when-not (= params (nth method 3))
                                   (reject! "all defmethods must use the same parameter vector"
                                            method)))
                             values (mapv #(nth % 2) method-forms)
                             _ (when-not (= (count values) (count (distinct values)))
                                 (reject! "duplicate defmethod dispatch value" method-forms))
                             default-method (first (filter #(= :default (nth % 2))
                                                           method-forms))
                             ordinary (remove #(= :default (nth % 2)) method-forms)
                             body-form (fn [method]
                                         (let [body (drop 4 method)]
                                           (if (= 1 (count body))
                                             (first body)
                                             (list* 'do body))))
                             clauses (mapcat (fn [method]
                                               [(nth method 2) (body-form method)])
                                             ordinary)
                             clauses (cond-> (vec clauses)
                                       default-method (conj (body-form default-method)))
                             generated (list 'defn name params
                                             (list* 'case
                                                    (list* dispatch params)
                                                    clauses))]
                         [name generated])))
                   declarations-by-name))]
        (into [] (remove nil?)
              (map (fn [form]
                     (cond
                       (and (seq? form) (= 'defmulti (first form)))
                       (get expanded (second form))

                       (and (seq? form) (= 'defmethod (first form)))
                       nil

                       :else form))
                   forms))))))

(defn- protocol-form->info [form]
  (let [[_ protocol-name & methods] form]
    (when-not (and (valid-name? protocol-name)
                   (seq methods)
                   (every? #(and (seq? %)
                                 (= 2 (count %))
                                 (valid-name? (first %))
                                 (vector? (second %))
                                 (seq (second %))
                                 (<= (count (second %)) max-parameters)
                                 (every? valid-name? (second %)))
                           methods)
                   (= (count methods) (count (distinct (map first methods)))))
      (reject! "defprotocol requires unique bounded (method [this ...]) signatures"
               form :kotoba.error/protocol-declaration))
    {:name protocol-name
     :methods (into {} (map (fn [[method-name params]] [method-name params]) methods))}))

(defn- record-descriptor [namespace-symbol record-name field-parts]
  [:record (keyword (str namespace-symbol) (name record-name))
   (mapv (fn [{field-name :name field-type :type}]
           [(keyword (name field-name)) field-type])
         field-parts)])

(defn- record-field-parts [fields form]
  (let [typed? (or (some keyword? fields)
                   (and (even? (count fields))
                        (some structured-type? (map second (partition 2 fields)))))]
    (if typed?
      (do
        (when-not (even? (count fields))
          (reject! "typed defrecord fields require alternating name/type pairs"
                   form :kotoba.error/record-declaration))
        (mapv (fn [[field type]]
                (when-not (valid-name? field)
                  (reject! "defrecord field names must be unique unqualified symbols"
                           field :kotoba.error/record-declaration))
                (validate-value-type! type)
                {:name field :type type})
              (partition 2 fields)))
      (mapv (fn [field]
              (when-not (valid-name? field)
                (reject! "defrecord field names must be unique unqualified symbols"
                         field :kotoba.error/record-declaration))
              {:name field :type :i64})
            fields))))

(defn- extension-implementations
  [protocols records protocol-name record-name method-forms whole-form]
  (let [protocol (get protocols protocol-name)
        record (get records record-name)
        declared-methods (set (keys (:methods protocol)))
        implemented-methods (mapv first method-forms)]
    (when-not (and protocol record (seq method-forms))
      (reject! "protocol extension requires a declared protocol, record, and methods"
               whole-form :kotoba.error/protocol-extension))
    (when-not (and (= (count implemented-methods)
                      (count (distinct implemented-methods)))
                   (= declared-methods (set implemented-methods)))
      (reject! "protocol extension must implement every declared method exactly once"
               whole-form :kotoba.error/protocol-extension))
    (mapv
     (fn [[method-name params & body :as method-form]]
       (let [declared-params (get-in protocol [:methods method-name])]
         (when-not (and declared-params
                        (= 1 (count body))
                        (vector? params)
                        (= (count params) (count declared-params))
                        (every? valid-name? params)
                        (= (count params) (count (distinct params))))
           (reject! "protocol method does not match its declaration"
                    method-form :kotoba.error/protocol-method))
         {:protocol protocol-name
          :method method-name
          :record record-name
          :record-type (:descriptor record)
          :params params
          :body (first body)}))
     method-forms)))

(defn- protocol-extension-groups [extra whole-form]
  (loop [remaining extra out []]
    (if (empty? remaining)
      out
      (let [protocol-name (first remaining)
            [methods tail] (split-with seq? (rest remaining))]
        (when-not (and (symbol? protocol-name) (seq methods))
          (reject! "protocol extension section requires a protocol name and methods"
                   whole-form :kotoba.error/protocol-extension))
        (recur tail (conj out [protocol-name methods]))))))

(defn- extend-protocol-form->info [protocols records form]
  (let [[_ protocol-name & sections] form]
    (when-not (and (get protocols protocol-name) (seq sections))
      (reject! "extend-protocol requires one declared protocol and bounded type sections"
               form :kotoba.error/protocol-extension))
    (loop [remaining sections implementations [] default-methods nil]
      (if (empty? remaining)
        {:protocol protocol-name
         :implementations implementations
         :default-methods default-methods
         :form form}
        (let [record-name (first remaining)
              [methods tail] (split-with seq? (rest remaining))]
          (when-not (and (symbol? record-name) (seq methods))
            (reject! "extend-protocol type section requires a record name and methods"
                     form :kotoba.error/protocol-extension))
          (if (= 'default record-name)
            (do
              (when default-methods
                (reject! "extend-protocol permits at most one default section"
                         form :kotoba.error/protocol-extension))
              (recur tail implementations methods))
            (recur tail
                   (into implementations
                         (extension-implementations protocols records protocol-name
                                                    record-name methods form))
                   default-methods)))))))

(defn- record-form->info [namespace-symbol protocols form]
  (let [[_ record-name fields & extra] form]
    (when-not (and (valid-name? record-name)
                   (vector? fields))
      (reject! "defrecord requires a bounded name and field vector"
               form :kotoba.error/record-declaration))
    (let [field-parts (record-field-parts fields form)
          field-names (mapv :name field-parts)
          typed? (not= fields field-names)
          _ (when-not (and (<= (count field-parts) max-record-fields)
                           (= (count field-names) (count (distinct field-names))))
              (reject! (str "defrecord requires at most " max-record-fields
                            " unique fields")
                       form :kotoba.error/record-declaration))
          descriptor (record-descriptor namespace-symbol record-name field-parts)
          groups (protocol-extension-groups extra form)
          record {:name record-name
                  :fields field-names
                  :field-parts field-parts
                  :typed? typed?
                  :descriptor descriptor}
          implementations
          (mapcat (fn [[protocol-name methods]]
                    (extension-implementations protocols {record-name record}
                                               protocol-name record-name methods form))
                  groups)]
      (assoc record :implementations implementations))))

(declare rewrite-record-constructors)

(defn- rewrite-record-map-expression
  "Lower a computed, but statically closed, map expression to one nominal
  record value.

  Record context propagates only through result positions. Binding values,
  tests, and non-final `do` expressions keep their ordinary meaning. Every
  reachable leaf must still be a literal map with exactly the declared fields;
  this admits heterogeneous records without introducing a dynamically typed
  map representation or runtime field guessing."
  [form {:keys [fields descriptor]}
   records-by-map-constructor records-by-wide-positional-constructor]
  (let [field-keys (mapv (comp keyword name) fields)
        rewrite #(rewrite-record-constructors
                  % records-by-map-constructor
                  records-by-wide-positional-constructor)
        recur-result #(rewrite-record-map-expression
                       % {:fields fields :descriptor descriptor}
                       records-by-map-constructor
                       records-by-wide-positional-constructor)]
    (cond
      (map? form)
      (do
        (when-not (= (set field-keys) (set (keys form)))
          (reject! "map-> record construction requires exactly the declared fields"
                   form :kotoba.error/record-map-constructor))
        (list* 'record-new descriptor
               (map (fn [field-key] (rewrite (get form field-key))) field-keys)))

      (and (seq? form) (contains? '#{if if-not} (first form)))
      (let [[op test then else :as parts] form]
        (when-not (= 4 (count parts))
          (reject! "computed map-> if requires both record-valued branches"
                   form :kotoba.error/record-map-constructor))
        (preserve-form-meta
         form
         (list op (rewrite test) (recur-result then) (recur-result else))))

      (and (seq? form) (contains? '#{if-let if-some} (first form)))
      (let [[op binding then else :as parts] form]
        (when-not (and (= 4 (count parts))
                       (vector? binding) (= 2 (count binding)))
          (reject! "computed map-> binding conditional requires one binding and both record-valued branches"
                   form :kotoba.error/record-map-constructor))
        (preserve-form-meta
         form
         (list op [(first binding) (rewrite (second binding))]
               (recur-result then) (recur-result else))))

      (and (seq? form) (= 'cond (first form)))
      (let [clauses (vec (rest form))]
        (when-not (and (even? (count clauses))
                       (= :else (nth clauses (- (count clauses) 2) nil)))
          (reject! "computed map-> cond requires a final :else record value"
                   form :kotoba.error/record-map-constructor))
        (preserve-form-meta
         form
         (list* 'cond
                (map-indexed (fn [index item]
                               (if (odd? index) (recur-result item) (rewrite item)))
                             clauses))))

      (and (seq? form) (= 'case (first form)))
      (let [[_ dispatch & clauses] form]
        (when-not (odd? (count clauses))
          (reject! "computed map-> case requires a default record value"
                   form :kotoba.error/record-map-constructor))
        (preserve-form-meta
         form
         (list* 'case (rewrite dispatch)
                (concat
                 (mapcat (fn [[test result]] [test (recur-result result)])
                         (partition 2 (butlast clauses)))
                 [(recur-result (last clauses))]))))

      (and (seq? form) (= 'condp (first form)))
      (let [[_ predicate dispatch & clauses] form]
        (when-not (and predicate dispatch (odd? (count clauses)))
          (reject! "computed map-> condp requires a predicate, dispatch, and default record value"
                   form :kotoba.error/record-map-constructor))
        (preserve-form-meta
         form
         (list* 'condp (rewrite predicate) (rewrite dispatch)
                (concat
                 (mapcat (fn [[test result]] [test (recur-result result)])
                         (partition 2 (butlast clauses)))
                 [(recur-result (last clauses))]))))

      (and (seq? form) (= 'let (first form)))
      (let [[_ bindings & body] form]
        (when-not (and (vector? bindings) (even? (count bindings)) (seq body))
          (reject! "computed map-> let requires bindings and a result expression"
                   form :kotoba.error/record-map-constructor))
        (preserve-form-meta
         form
         (list* 'let
                (mapv (fn [index item]
                        (if (odd? index) (rewrite item) item))
                      (range) bindings)
                (concat (map rewrite (butlast body))
                        [(recur-result (last body))]))))

      (and (seq? form) (= 'do (first form)))
      (let [body (rest form)]
        (when-not (seq body)
          (reject! "computed map-> do requires a result expression"
                   form :kotoba.error/record-map-constructor))
        (preserve-form-meta
         form
         (list* 'do (concat (map rewrite (butlast body))
                            [(recur-result (last body))]))))

      :else
      (reject! (str "map-> record construction requires an exact map or a closed "
                    "control expression of exact maps")
               form :kotoba.error/record-map-constructor))))

(defn- rewrite-record-constructors
  [form records-by-map-constructor records-by-wide-positional-constructor]
  (cond
    (seq? form)
    (let [[op & args] form]
      (preserve-form-meta
       form
       (cond
        (= 'quote op) form

        (contains? records-by-map-constructor op)
        (let [record (get records-by-map-constructor op)]
          (when-not (= 1 (count args))
            (reject! "map-> record construction requires one map expression"
                     form :kotoba.error/record-map-constructor))
          (rewrite-record-map-expression
           (first args) record
           records-by-map-constructor records-by-wide-positional-constructor))

        (contains? records-by-wide-positional-constructor op)
        (let [{:keys [fields descriptor]} (get records-by-wide-positional-constructor op)]
          (when-not (= (count fields) (count args))
            (reject! "positional record construction must exactly match the declared fields"
                     form :kotoba.error/record-positional-constructor))
          (list* 'record-new descriptor
                 (mapv #(rewrite-record-constructors
                         % records-by-map-constructor
                         records-by-wide-positional-constructor)
                       args)))

        :else
        (list* op (mapv #(rewrite-record-constructors
                         % records-by-map-constructor
                         records-by-wide-positional-constructor)
                       args)))))
    (vector? form) (mapv #(rewrite-record-constructors
                          % records-by-map-constructor
                          records-by-wide-positional-constructor)
                         form)
    (map? form) (into (empty form)
                      (map (fn [[k v]]
                             [(rewrite-record-constructors
                               k records-by-map-constructor
                               records-by-wide-positional-constructor)
                              (rewrite-record-constructors
                               v records-by-map-constructor
                               records-by-wide-positional-constructor)]))
                      form)
    (set? form) (set (map #(rewrite-record-constructors
                            % records-by-map-constructor
                            records-by-wide-positional-constructor)
                          form))
    :else form))

(declare rewrite-record-member-access*)

(defn- rewrite-record-bindings
  "Rewrite sequential binding values while tracking whether PATTERN shadows the
  record receiver.  A binding is not visible in its own initializer, but is
  visible to every initializer and body expression that follows it."
  [bindings receiver descriptor active?]
  (loop [remaining (partition 2 bindings)
         active? active?
         rewritten []]
    (if-let [[pattern value] (first remaining)]
      (recur (next remaining)
             (and active? (not (contains? (binding-symbols pattern) receiver)))
             (conj rewritten pattern
                   (rewrite-record-member-access* value receiver descriptor active?)))
      [(vec rewritten) active?])))

(defn- rewrite-record-fn-clause
  [clause receiver descriptor active? named-receiver?]
  (let [[params & body] clause
        body-active? (and active?
                          (not named-receiver?)
                          (vector? params)
                          (not (contains? (binding-symbols params) receiver)))]
    (if (vector? params)
      (preserve-form-meta
       clause
       (list* params
              (mapv #(rewrite-record-member-access* % receiver descriptor body-active?)
                    body)))
      clause)))

(defn- rewrite-record-member-access*
  [form receiver descriptor active?]
  (if-not active?
    form
    (cond
      (seq? form)
      (let [[op & args] form]
        (preserve-form-meta
         form
         (cond
           (= 'quote op) form

           (and (= 'get op)
                (<= 2 (count args) 3)
                (= receiver (first args))
                (keyword? (second args)))
           (list 'record-get descriptor receiver (second args))

           (= 'let op)
           (let [[bindings & body] args]
             (if (and (vector? bindings) (even? (count bindings)))
               (let [[bindings' body-active?]
                     (rewrite-record-bindings bindings receiver descriptor active?)]
                 (list* op bindings'
                        (mapv #(rewrite-record-member-access* % receiver descriptor body-active?)
                              body)))
               (list* op (mapv #(rewrite-record-member-access* % receiver descriptor active?)
                               args))))

           (= 'loop op)
           (let [[bindings & body] args]
             (if (and (vector? bindings) (even? (count bindings)))
               (let [pairs (partition 2 bindings)
                     bindings' (vec (mapcat
                                     (fn [[pattern value]]
                                       [pattern
                                        (rewrite-record-member-access*
                                         value receiver descriptor active?)])
                                     pairs))
                     body-active? (and active?
                                       (not-any? #(contains? (binding-symbols %) receiver)
                                                 (map first pairs)))]
                 (list* 'loop bindings'
                        (mapv #(rewrite-record-member-access* % receiver descriptor body-active?)
                              body)))
               (list* 'loop
                      (mapv #(rewrite-record-member-access* % receiver descriptor active?)
                            args))))

           (= 'fn op)
           (let [named? (symbol? (first args))
                 fn-name (when named? (first args))
                 clauses (if named? (rest args) args)
                 named-receiver? (= receiver fn-name)]
             (if (vector? (first clauses))
               (let [[params & body] clauses
                     clause (list* params body)
                     rewritten (rewrite-record-fn-clause clause receiver descriptor
                                                         active? named-receiver?)]
                 (list* 'fn (concat (when named? [fn-name]) rewritten)))
               (list* 'fn
                      (concat (when named? [fn-name])
                              (mapv #(rewrite-record-fn-clause % receiver descriptor
                                                               active? named-receiver?)
                                    clauses)))))

           :else
           (list* op (mapv #(rewrite-record-member-access* % receiver descriptor active?)
                           args)))))
      (vector? form) (mapv #(rewrite-record-member-access* % receiver descriptor active?) form)
      (map? form) (into (empty form)
                        (map (fn [[k v]] [(rewrite-record-member-access* k receiver descriptor active?)
                                         (rewrite-record-member-access* v receiver descriptor active?)]))
                        form)
      (set? form) (set (map #(rewrite-record-member-access* % receiver descriptor active?) form))
      :else form)))

(defn- rewrite-record-member-access [form receiver descriptor]
  (rewrite-record-member-access* form receiver descriptor true))

(defn- expand-record-protocol-forms [forms]
  (let [namespace-symbol (or (some (fn [form]
                                     (when (and (seq? form) (= 'ns (first form)))
                                       (second form)))
                                   forms)
                             (symbol "kotoba.user"))
        protocol-forms (filter #(and (seq? %)
                                     (contains? '#{defprotocol definterface} (first %)))
                               forms)
        protocol-infos (mapv protocol-form->info protocol-forms)
        protocols (into {} (map (juxt :name identity)) protocol-infos)
        _ (when-not (= (count protocols) (count protocol-infos))
            (reject! "duplicate protocol name" protocol-forms
                     :kotoba.error/protocol-declaration))
        method-names (mapcat (comp keys :methods) protocol-infos)
        _ (when-not (= (count method-names) (count (distinct method-names)))
            (reject! "protocol method names must be unique within a namespace"
                     protocol-forms :kotoba.error/protocol-declaration))
        declared-function-names
        (into #{} (keep (fn [form]
                          (when (and (seq? form)
                                     (contains? '#{defn defn-} (first form)))
                            (second form)))) forms)
        _ (when (seq (set/intersection (set method-names) declared-function-names))
            (reject! "protocol method names must not collide with declared functions"
                     protocol-forms :kotoba.error/protocol-declaration))
        record-forms (filter #(and (seq? %) (= 'defrecord (first %))) forms)
        record-infos (mapv #(record-form->info namespace-symbol protocols %) record-forms)
        records (into {} (map (juxt :name identity)) record-infos)
        _ (when-not (= (count records) (count record-infos))
            (reject! "duplicate record name" record-forms :kotoba.error/record-declaration))
        extend-type-forms (filter #(and (seq? %) (= 'extend-type (first %))) forms)
        extend-type-impls
        (mapcat (fn [[_ record-name & extra :as form]]
                  (mapcat (fn [[protocol-name methods]]
                            (extension-implementations protocols records protocol-name
                                                       record-name methods form))
                          (protocol-extension-groups extra form)))
                extend-type-forms)
        extend-protocol-forms
        (filter #(and (seq? %) (= 'extend-protocol (first %))) forms)
        extend-protocol-infos
        (mapv #(extend-protocol-form->info protocols records %) extend-protocol-forms)
        default-infos (filter :default-methods extend-protocol-infos)
        default-protocols (map :protocol default-infos)
        _ (when-not (= (count default-protocols) (count (distinct default-protocols)))
            (reject! "extend-protocol permits one default section per protocol"
                     extend-protocol-forms :kotoba.error/protocol-extension))
        explicit-implementations
        (vec (concat (mapcat :implementations record-infos)
                     extend-type-impls
                     (mapcat :implementations extend-protocol-infos)))
        explicit-identities (map (juxt :protocol :method :record)
                                 explicit-implementations)
        _ (when-not (= (count explicit-identities)
                       (count (distinct explicit-identities)))
            (reject! "duplicate protocol method implementation" explicit-implementations
                     :kotoba.error/protocol-extension))
        default-implementations
        (mapcat
         (fn [{:keys [protocol default-methods form]}]
           (when-not (seq record-infos)
             (reject! "extend-protocol default has no declared record specialization targets"
                      form :kotoba.error/protocol-extension))
           ;; Validate the section even when every record has an explicit
           ;; implementation and the default therefore emits no function.
           (extension-implementations protocols records protocol
                                      (:name (first record-infos))
                                      default-methods form)
           (let [implemented-records
                 (into #{}
                       (keep (fn [{implemented-protocol :protocol record :record}]
                               (when (= protocol implemented-protocol) record)))
                       explicit-implementations)]
             (mapcat (fn [{:keys [name]}]
                       (when-not (contains? implemented-records name)
                         (extension-implementations protocols records protocol name
                                                    default-methods form)))
                     record-infos)))
         default-infos)
        implementations (vec (concat explicit-implementations
                                     default-implementations))
        identities (map (juxt :protocol :method :record) implementations)
        _ (when-not (= (count identities) (count (distinct identities)))
            (reject! "duplicate protocol method implementation" implementations
                     :kotoba.error/protocol-extension))
        named-impls (mapv #(assoc %1 :impl-name
                                  (symbol (str "__kotoba_protocol_impl_" %2)))
                          implementations (range))
        constructors
        (into []
              (keep (fn [{:keys [name fields field-parts typed? descriptor]}]
                      ;; A positional constructor with more than max-parameters
                      ;; is still valid as direct record syntax, but it cannot
                      ;; become a first-class function without lying about the
                      ;; bounded callable ABI. Wide direct calls are rewritten
                      ;; below; map->Type remains available at every width.
                      (when (<= (count fields) max-parameters)
                        (let [params (if typed?
                                       (vec (mapcat (juxt :name :type) field-parts))
                                       fields)]
                          (list 'defn (symbol (str "->" name)) params descriptor
                                (list* 'record-new descriptor fields)))))
                    record-infos))
        impl-defs
        (mapv (fn [{:keys [impl-name params record-type body]}]
                (let [typed-params
                      (vec (mapcat (fn [index param]
                                     [param (if (zero? index) record-type :i64)])
                                   (range) params))]
                  (list 'defn- impl-name typed-params
                        (rewrite-record-member-access body (first params) record-type))))
              named-impls)
        dispatch
        {:methods (into {}
                        (map (fn [[method-name params]]
                               [method-name {:arity (count params)
                                             :implementations
                                             (into {}
                                                   (keep (fn [{:keys [method record-type impl-name]}]
                                                           (when (= method method-name)
                                                             [(second record-type) impl-name])))
                                                   named-impls)}]))
                        (mapcat :methods protocol-infos))}
        map-constructors
        (into {} (map (fn [{:keys [name] :as record}]
                        [(symbol (str "map->" name)) record]))
              record-infos)
        wide-positional-constructors
        (into {} (keep (fn [{:keys [name fields] :as record}]
                         (when (> (count fields) max-parameters)
                           [(symbol (str "->" name)) record])))
              record-infos)
        record-schemas
        ;; A defrecord whose fields already use closed schema edges can expose
        ;; its nominal identity as [:ref :ns/Type]. Keep legacy declarations
        ;; with nested inline nominal descriptors source-compatible: those
        ;; descriptors are valid record values, but are intentionally not
        ;; inserted into the stricter closed schema graph.
        (into {} (keep (fn [{:keys [descriptor]}]
                         (let [field-types (map second (nth descriptor 2))
                               inline-nominal?
                               (some (fn [field-type]
                                       (some #(or (record-type? %)
                                                  (variant-type? %))
                                             (tree-seq coll? seq field-type)))
                                     field-types)]
                           (when-not inline-nominal?
                             [(second descriptor) descriptor]))))
              record-infos)
        declarations '#{defrecord defprotocol definterface extend-type extend-protocol}
        ordinary (remove #(and (seq? %) (contains? declarations (first %))) forms)
        rewritten (mapv #(rewrite-record-constructors
                          % map-constructors wide-positional-constructors)
                        ordinary)]
    {:forms (into rewritten (concat constructors impl-defs))
     :dispatch dispatch
     :record-schemas record-schemas}))

(defn analyze
  "Analyze Kotoba source into HIR.

  opts:
    :language-profile  when `:pure-product`, enforce pure-product-profile.edn
                       admission (T2.1): no capabilities/cap-call/disallowed sugar,
                       empty effects.
    :admit-linked-synthetics?  when true, skip reject-reserved-source-symbols!
                       (T8.3 multi-file project monomorph: project/link-source
                       re-emits HIR bodies that already contain desugared
                       `__kotoba_or_*` / `__kotoba_and_*` bindings from the
                       per-module first pass. User source still cannot invent
                       those names — each module was checked before link.)"
  ([source] (analyze source nil))
  ([source opts]
  (let [language-profile (when (map? opts) (:language-profile opts))
        admit-linked-synthetics? (when (map? opts) (:admit-linked-synthetics? opts))
        lambda-id-base (or (when (map? opts) (:lambda-id-base opts)) 0)
        forms (mapv annotate-doseq-collection-kinds (read-forms source))
        _ (when-not admit-linked-synthetics?
            (reject-reserved-source-symbols! forms))
        _ (when (= :pure-product language-profile)
            (check-pure-product-source-forms! forms))
        record-protocol-expansion (expand-record-protocol-forms forms)
        forms (:forms record-protocol-expansion)
        protocol-dispatch (:dispatch record-protocol-expansion)
        forms (expand-closed-multimethod-forms forms)
        namespaces (filter #(and (seq? %) (= 'ns (first %))) forms)
        defs (filter #(and (seq? %) (contains? '#{defn defn-} (first %))) forms)
        constant-forms (filter #(and (seq? %) (= 'def (first %))) forms)
        other (remove #(or (and (seq? %) (= 'ns (first %)))
                           (and (seq? %) (contains? '#{defn defn-} (first %)))
                           (and (seq? %) (= 'def (first %)))) forms)
        _ (when (> (count namespaces) 1)
            (reject! "at most one namespace form is admitted" namespaces :kotoba.error/namespace-count))
        namespace-info (when-let [namespace-form (first namespaces)]
                         (namespace-parts namespace-form))
        declared-schemas (or (:schemas namespace-info) {})
        record-schemas (:record-schemas record-protocol-expansion)
        schema-collisions (set/intersection (set (keys declared-schemas))
                                            (set (keys record-schemas)))
        schema-conflicts (set (filter #(not= (get declared-schemas %)
                                             (get record-schemas %))
                                      schema-collisions))
        _ (when (seq schema-conflicts)
            (reject! "defrecord namespace :schemas forward declaration must match exactly"
                     schema-conflicts :kotoba.error/record-schema-collision))
        merged-schemas-raw (merge declared-schemas record-schemas)
        merged-schemas (when (seq merged-schemas-raw)
                         (schema/validate-table! merged-schemas-raw))
        namespace-info (assoc (or namespace-info {})
                              :schemas merged-schemas
                              :schema-identities
                              (when merged-schemas (schema/identities merged-schemas)))
        raw-constants (into {}
                        (map (fn [form]
                               (let [{:keys [name value]} (def-parts form)]
                                 (when-not (valid-name? name)
                                   (reject! "invalid constant name" name))
                                 (when (contains? reserved-function-names name)
                                   (reject! "reserved constant name" name))
                                 [name value])))
                        constant-forms)
        _ (when-not (= (count raw-constants) (count constant-forms))
            (reject! "duplicate constant name" constant-forms))
        constants (into {}
                        (map (fn [[name value]]
                               [name (resolve-constant-aliases! value raw-constants #{name})]))
                        raw-constants)
        source-names (mapv second defs)
        _ (when-not (= (count source-names) (count (distinct source-names)))
            (reject! "duplicate function name" defs))
        def-parts (vec (mapcat #(expand-defn-parts % constants) defs))
        function-arities
        (reduce (fn [out {:keys [source-name logical-arity raw-params]}]
                  (if (vector? raw-params)
                    (let [typed? (or (some keyword? raw-params)
                                     (some type-alias-form? raw-params)
                                     (and (even? (count raw-params))
                                          (some structured-type?
                                                (map second (partition 2 raw-params)))))
                          arity (or logical-arity
                                    (if typed? (quot (count raw-params) 2)
                                        (count raw-params)))]
                      (update out source-name (fnil conj #{}) arity))
                    out))
                {} def-parts)
        _ (when (> (count def-parts) max-functions)
            (reject! "function count exceeds admission limit" (count def-parts)))
        overloaded-sources (->> def-parts
                                (group-by :source-name)
                                (keep (fn [[name clauses]]
                                        (when (> (count clauses) 1) name)))
                                set)
        overloads (into {}
                        (keep (fn [{:keys [source-name logical-arity name]}]
                                (when (contains? overloaded-sources source-name)
                                  [[source-name logical-arity] name])))
                        def-parts)
        _ (when (contains? overloaded-sources 'main)
            (reject! "main must have exactly one zero-arity clause" 'main))
        function-callable-result-contracts
        (into {}
              (keep (fn [{:keys [source-name logical-arity raw-params
                                 callable-result-contract]}]
                      (when callable-result-contract
                        (let [typed? (or (some keyword? raw-params)
                                         (some type-alias-form? raw-params)
                                         (and (even? (count raw-params))
                                              (some structured-type?
                                                    (map second (partition 2 raw-params)))))
                              arity (or logical-arity
                                        (if typed? (quot (count raw-params) 2)
                                            (count raw-params)))]
                          [[source-name arity] callable-result-contract]))))
              def-parts)
        ;; ADR-2607150000: mapcat, not mapv -- a defn using `loop` may
        ;; expand into itself PLUS one or more synthesized loop-helper
        ;; functions (collected via *pending-loop-helpers*, bound fresh
        ;; per defn so helpers from one function's loops never leak into
        ;; another's). defn PARAMS may now be destructuring patterns
        ;; (param-name+wrap above), not just plain symbols. *loop-counter*
        ;; is bound ONCE for the whole source (not per-defn) so loop-helper
        ;; names stay unique across every defn, not just within one.
        ;; ADR-2607182410: `used-capabilities` is created OUTSIDE the
        ;; `binding` below (unlike *loop-counter*'s own fresh volatile,
        ;; which only needs to live inside it) so `check-namespace-
        ;; capabilities!` can still deref it once `parsed` is fully built
        ;; and `binding`'s dynamic extent has ended -- the *var* rebinding
        ;; ends with the `let`, but the volatile object itself, referenced
        ;; here from outside, keeps whatever `resolve-capability-keyword!`
        ;; conjoined onto it during desugaring.
        used-capabilities (volatile! #{})
        lambda-infos (atom [])
        uses-apply? (volatile! false)
        uses-lazy? (volatile! false)
        required-dispatchers (volatile! #{})
        parsed (binding [*loop-counter* (volatile! 0)
                          *lambda-counter* (volatile! lambda-id-base)
                          *pending-lambdas* lambda-infos
                          *uses-apply?* uses-apply?
                          *uses-lazy?* uses-lazy?
                          *required-closure-dispatchers* required-dispatchers
                          *function-arities* function-arities
                          *function-callable-result-contracts*
                          function-callable-result-contracts
                          *synthetic-counter* (volatile! 0)
                          *used-capability-keywords* used-capabilities]
               ;; `vec` (forcing) must stay INSIDE `binding`'s dynamic
               ;; extent: `mapcat` is lazy, so `(vec (binding [...]
               ;; (mapcat ...)))` would rebind *loop-counter* only around
               ;; building the (unrealized) lazy seq, then unbind it before
               ;; `vec` actually forces each element -- confirmed live as an
               ;; NPE (`*loop-counter*` back to its nil default) on any
               ;; source using `loop`.
               (vec
                     (mapcat
                     (fn [{:keys [name source-name raw-params result body effects-ceiling
                                  result-inferred? callable-result-contract]}]
                       (let [source-name (or source-name name)]
                         (when-not (valid-name? name) (reject! "invalid function name" name))
                         (when (contains? reserved-function-names name)
                           (reject! "reserved function name" name))
                         (when-not (vector? raw-params)
                           (reject! "function parameters must be a vector" raw-params))
                         (when-not (= 1 (count body))
                           (reject! "function must contain one result expression" body))
                         (let [param-parts (typed-param-parts raw-params constants)
                               _ (when (> (count param-parts) max-parameters)
                                   (reject! "function parameters exceed ABI-supported arity" raw-params
                                            :kotoba.error/max-parameters))
                               name+wraps (mapv #(param-name+wrap (:pattern %)) param-parts)
                               params (mapv first name+wraps)
                               param-types (mapv :type param-parts)
                               callable-param-contracts
                               (into {}
                                     (keep-indexed (fn [index part]
                                                     (when-let [contract (:callable-contract part)]
                                                       [index contract])))
                                     param-parts)
                               wrap-body (apply comp (map second name+wraps))]
                           (when-not (and (every? valid-name? params) (= (count params) (count (distinct params))))
                             (reject! "function parameters must be unique bounded symbols with ABI-supported arity" raw-params))
                           (let [loop-helpers (atom [])
                                 constant-bound (into #{} (mapcat #(binding-symbols (:pattern %)) param-parts))
                                 source-body (substitute-constants
                                              (wrap-body (first body))
                                              constants constant-bound)
                                 ;; Product Value ABI v1: typed option params for if-some/when-some.
                                 option-locals
                                 (into {}
                                       (keep (fn [[p t]]
                                               (when (and (vector? t) (= :option (first t)))
                                                 [p t]))
                                             (map vector params param-types)))
                                 ;; All params + ns schemas so record-get of
                                 ;; [:option T] fields desugars with the real T
                                 ;; (closes option-string-in-record gap).
                                 local-types (zipmap params param-types)
                                 source-callable-contract
                                 (binding [*lexical-callable-contracts*
                                           (into {} (map (fn [[index contract]]
                                                           [(nth params index) contract]))
                                                 callable-param-contracts)]
                                   (expression-callable-contract source-body))
                                 _ (when (and callable-result-contract
                                              source-callable-contract
                                              (not= callable-result-contract
                                                    source-callable-contract))
                                     (reject! "returned callable contract does not match the declared result contract"
                                              {:function source-name
                                               :expected callable-result-contract
                                               :actual source-callable-contract}
                                              :kotoba.error/callable-result-contract))
                                 desugared (binding [*pending-loop-helpers* loop-helpers
                                                     *local-option-types* option-locals
                                                     *local-types* local-types
                                                     *schemas* (:schemas namespace-info)
                                                     *lexical-bindings* (set params)
                                                     *lexical-callable-contracts*
                                                     (into {} (map (fn [[index contract]]
                                                                     [(nth params index) contract]))
                                                           callable-param-contracts)
                                                     *expected-callable-contract*
                                                     callable-result-contract]
                                             (if (closure-result-type? result (:schemas namespace-info))
                                               (desugar-result-expr result source-body)
                                               (desugar-expr source-body)))]
                             (into [(cond-> {:name name :source-name source-name
                                             :params params :param-types param-types
                                             :result result :effects #{}
                                             :result-inferred? result-inferred?
                                             :body desugared}
                                      (seq callable-param-contracts)
                                      (assoc :callable-param-contracts callable-param-contracts)
                                      callable-result-contract
                                      (assoc :callable-result-contract callable-result-contract)
                                      effects-ceiling (assoc :effects-ceiling effects-ceiling))]
                                   @loop-helpers)))))
                     def-parts)))
        ;; Infer lambda helper bodies before constructing dispatchers.  A
        ;; dispatcher has one concrete Wasm result type, so typed closures must
        ;; not share the legacy i64 dispatcher family. Keep every not-yet-
        ;; admitted result on the legacy i64 path, where the ordinary value
        ;; checker retains its previous fail-closed behavior.
        preliminary-lambdas
        (let [helpers (mapv :helper @lambda-infos)
              ;; A lifted lambda may call an earlier lexical closure. Its body
              ;; already contains the requested synthetic dispatcher call, but
              ;; the real dispatcher functions are constructed only after
              ;; lambda result inference. Seed signatures here so an enclosing
              ;; lambda can infer the structured value returned by that nested
              ;; call instead of falling back to its provisional :i64.
              inference-dispatchers
              (mapv (fn [[result-type arity]]
                      {:name (invoke-dispatcher-name result-type arity)
                       :params (vec (cons '__kotoba_inference_closure
                                          (map #(symbol (str "__kotoba_inference_arg_" %))
                                               (range arity))))
                       :param-types (vec (repeat (inc arity) :i64))
                       :result result-type
                       :result-inferred? false
                       ;; This body is never emitted or checked; only the
                       ;; signature participates in infer-absent-results.
                       :body 0})
                    @required-dispatchers)
              inference-functions
              (cond-> (into parsed (concat helpers inference-dispatchers))
                (some #(uses-string-from-i64? (:body %)) helpers)
                (into [string-from-i64-nat-helper string-from-i64-helper]))
              candidates (binding [*schemas* (:schemas namespace-info)]
                           (->> inference-functions
                                (mapv #(update % :body resolve-overloaded-calls
                                               overloads overloaded-sources))
                                (mapv #(if (:param-types %)
                                         %
                                         (assoc % :param-types
                                                (vec (repeat (count (:params %)) :i64)))))
                                infer-absent-results))
              by-name (into {} (map (juxt :name identity)) candidates)]
          (mapv (fn [{:keys [helper contract-result] :as info}]
                  (let [typed (get by-name (:name helper))
                        result (canonical-closure-result-type
                                (:result typed) (:schemas namespace-info))
                        _ (when (and contract-result
                                     (not (same-expression-type? result contract-result)))
                            (reject! "fn result does not match the declared callable contract"
                                     {:function (:name helper)
                                      :expected contract-result :actual result}
                                     :kotoba.error/callable-result-type))
                        typed (assoc typed :result result)]
                    (assoc info :helper
                           (if (closure-result-type? result {})
                             typed
                             (dissoc helper :result-inferred?)))))
                @lambda-infos))
        parsed (into parsed
                     (concat (map :helper preliminary-lambdas)
                             (lambda-dispatchers
                              preliminary-lambdas
                              (cond-> @required-dispatchers
                                @uses-apply? (into (map (fn [arity] [:i64 arity])
                                                       (range 5)))
                                @uses-lazy? (conj [:i64 0])))
                             (when @uses-apply? [closure-apply-helper])
                             (when @uses-lazy? [lazy-take-helper lazy-drop-helper])))
        _ (when (> (count parsed) max-functions)
            (reject! "function count exceeds admission limit after closure lowering"
                     (count parsed)))
        parsed (mapv #(update % :body resolve-overloaded-calls overloads overloaded-sources) parsed)
        ;; ADR-2607150000: inject the synthesized `get`/`assoc` helpers only
        ;; when a desugared body actually calls them -- keeps modules that
        ;; never use `get`/`assoc` byte-identical to before this change. A
        ;; user `defn` that collides with a helper's reserved name is
        ;; caught for free by the existing :duplicate-function-name check
        ;; below (signatures' map semantics silently drop one entry, count
        ;; mismatch trips it).
        parsed (cond-> parsed
                 (some #(uses-map-get? (:body %)) parsed) (conj map-get-helper)
                 (some #(uses-map-without? (:body %)) parsed) (conj map-without-helper)
                 (some #(uses-string-from-i64? (:body %)) parsed)
                 (#(into % [string-from-i64-nat-helper string-from-i64-helper])))
        parsed (mapv #(if (:param-types %)
                        %
                        (assoc % :param-types (vec (repeat (count (:params %)) :i64))))
                     parsed)
        ;; Synthesized loop-helpers were param-type-defaulted to all-:i64 just
        ;; above (they carry no annotations); recover the real types of their
        ;; captured outer variables from each helper's call site so a loop that
        ;; captures a :string/:f64/record variable type-checks and lowers with
        ;; the correct local types instead of a spurious "expected i64" error.
        parsed (resolve-loop-helper-param-types parsed)
        ;; ADR 0189: resolve `(record-get value :field)` to the canonical
        ;; 3-arity form. This must precede every later pass that runs type
        ;; inference — elaborate-named-abilities does, and its record-get case
        ;; destructures [type value field], so a 2-arity form reaching it puts
        ;; the value symbol in the type slot and `(nth type 2)` throws.
        parsed (infer-absent-results parsed)
        parsed (rewrite-record-projections parsed (:schemas namespace-info)
                                           protocol-dispatch)
        ;; `option-or` intentionally survives syntactic desugaring until the
        ;; rewrite above can infer its payload descriptor from locals and
        ;; function signatures. Re-run absent-result inference now that the
        ;; internal `option-value-of` form has an admitted type signature.
        parsed (infer-absent-results parsed)
        named-elaboration (elaborate-named-abilities parsed)
        parsed (:functions named-elaboration)
        parsed (infer-closure-refinements parsed preliminary-lambdas)
        used-capability-names
        (set/union @used-capabilities (:used named-elaboration))
        signatures (into {} (map (juxt :name :params) parsed))
        source-public (->> def-parts (filter :public?) (map :source-name) distinct vec)
        expand-export (fn [source-name]
                        (let [clauses (->> def-parts
                                           (filter #(= source-name (:source-name %)))
                                           (sort-by #(or (:logical-arity %) 0)))]
                          (if (> (count clauses) 1)
                            (mapv :name clauses)
                            [source-name])))
        exports (cond
                  (some? (:exports namespace-info)) (vec (mapcat expand-export (:exports namespace-info)))
                  (some #(= 'defn- (first %)) defs) (vec (mapcat expand-export source-public))
                  :else (mapv :name parsed))
        entry (when (contains? signatures 'main) 'main)]
    (when (seq (set/intersection (set (keys constants)) (set source-names)))
      (reject! "constant and function names must be disjoint" forms))
    (when (seq other) (reject! "only ns, def, defn, and defn- are allowed at top level"
                                 (first other) :kotoba.error/top-level-form))
    (when (empty? parsed) (reject! "at least one defn is required" forms))
    (when-not (= (count parsed) (count signatures)) (reject! "duplicate function name" defs))
    (when (and (some? (:exports namespace-info))
               (not-every? (set source-public) (:exports namespace-info)))
      (reject! "namespace exports must name declared public functions" (:exports namespace-info)))
    (when (and (nil? entry) (nil? (:exports namespace-info)))
      (reject! "entryless library requires an explicit non-empty namespace export list" defs))
    (when (and (nil? entry) (empty? exports))
      (reject! "entryless library requires at least one exported function" exports))
    (when (and entry (not (empty? (get signatures entry))))
      (reject! "main must take zero arguments" 'main))
    (when (and entry (not (some #{entry} exports)))
      (reject! "main entrypoint must be exported" exports))
    (check-namespace-capabilities! (:capabilities namespace-info)
                                   used-capability-names)
    (let [declared (set (keys (:schemas namespace-info)))
          refs (->> parsed
                    (tree-seq coll? seq)
                    (filter schema-ref-type?)
                    (map second)
                    set)
          missing (set/difference refs declared)]
      (when (seq missing)
        (reject! "value type references a schema outside the closed namespace table" missing)))
    ;; Inline nominal descriptors are convenient for field-aware source
    ;; operations while [:ref ...] keeps recursive/cross-root schemas closed.
    ;; When an inline descriptor names a declared schema, it must be byte-for-
    ;; byte the authoritative descriptor before ref/descriptor type
    ;; compatibility is admitted.
    (let [schemas (:schemas namespace-info)
          mismatched
          (->> parsed
               (tree-seq coll? seq)
               (filter #(or (record-type? %) (variant-type? %)))
               (filter (fn [descriptor]
                         (let [identity (second descriptor)]
                           (and (contains? schemas identity)
                                (not= descriptor (get schemas identity))))))
               vec)]
      (when (seq mismatched)
        (reject! "inline nominal descriptor differs from closed namespace schema"
                 (first mismatched))))
    (let [budget (volatile! 0)]
      (doseq [{:keys [params body]} parsed]
        (validate-expr body (set params) signatures 0 budget)))
    (check-value-types! parsed)
    (check-linear-resource-ownership! parsed)
    (check-kernel-region-provenance! parsed)
    (check-lowering-budget! parsed)
    (let [typed-values? (boolean
                         (or (seq (:schemas namespace-info))
                             (some #(or (seq (:closure-param-indexes %))
                                        (seq (:i64-pair-chain-param-indexes %))
                                        (:closure-result? %))
                               parsed)
                         (some (fn [{:keys [param-types result body]}]
                                 (or (some #(or (contains? #{:f32 :f64 :string :keyword :map :bytes :option-i64 :result-i64 :vector-i64 :vector-f64 :string-index :disjoint-set-i64 :document} %)
                                                (structured-type? %)) param-types)
                                     (or (contains? #{:f32 :f64 :string :keyword :map :bytes :option-i64 :result-i64 :vector-i64 :vector-f64 :string-index :disjoint-set-i64 :document} result)
                                         (structured-type? result))
                                     ;; `:bool` literals are plain 0/1 words, not typed values.
                                     (some #(or (string? %) (keyword? %)
                                                (and (seq? %)
                                                     (or (contains? typed-map-operations (first %))
                                                         (contains? typed-safe-value-operations (first %))
                                                         (contains? parametric-result-operations (first %))
                                                         (contains? variant-operations (first %))
                                                         (contains? generic-option-operations (first %))
                                                         (contains? canonical-list-operations (first %))
                                                         (contains? bytes-operations (first %))
                                                         (contains? heterogeneous-vector-operations (first %))
                                                         (contains? typed-set-operations (first %))
                                                         (contains? canonical-typed-map-operations (first %))
                                                         (contains? record-operations (first %))
                                                         (= 'vector-new (first %))
                                                         (= 'vector-f64-new (first %))
                                                         (contains? typed-vector-operations (first %))
                                                         (contains? typed-f64-vector-operations (first %))
                                                         (contains? document-fixed-operations (first %))
                                                         (contains? document-variadic-operations (first %))
                                                         (contains? i32-operations (first %))
                                                         ;; Scalar f64/f32 ops (incl. f64-from-bits and the
                                                         ;; f64-/f32-comparison ops) require the typed (KIR v4)
                                                         ;; emitter: the untyped v3 path has no lowering for
                                                         ;; them and would emit a `call nil`. A body may use
                                                         ;; these while every exported signature stays scalar
                                                         ;; :i64, so scan for them here, not just in signatures.
                                                         (contains? f64-operations (first %))
                                                         (contains? f32-operations (first %))
                                                         (contains? decimal-operations (first %)))))
                                           (tree-seq coll? seq body))))
                               parsed)))
          function-effects (infer-effects parsed)
          _ (doseq [{:keys [name lazy-thunk?]} parsed
                    :when (and lazy-thunk? (seq (get function-effects name)))]
              (reject! "lazy sequence thunks must be effect-free because forcing is non-memoized"
                       name))
          _ (doseq [{:keys [name source-name effects-ceiling body]} parsed]
              (when effects-ceiling
                (let [inferred (get function-effects name #{})
                      excess (set/difference inferred effects-ceiling)]
                  (when (seq excess)
                    (let [ops (into #{}
                                    (keep (fn [[_tag id]]
                                            (get capability-id->name id)))
                                    excess)
                          span (or (get (meta body) :span) (form-span body))]
                      (throw (ex-info
                              (str "inferred effects exceed declared effect ceiling"
                                   (when source-name (str " for " source-name))
                                   (when (seq ops) (str ": " (pr-str ops))))
                              (cond-> {:phase :effect-ceiling
                                       :function (or source-name name)
                                       :inferred inferred
                                       :ceiling effects-ceiling
                                       :excess excess
                                       :operations ops}
                                span (assoc :span span)))))))))
          functions (mapv (fn [function]
                            (cond-> (assoc function :effects
                                           (get function-effects (:name function)))
                              (:effects-ceiling function)
                              (assoc :effects-ceiling (:effects-ceiling function))
                              (not typed-values?) (dissoc :param-types)))
                          parsed)
          main-result (some->> parsed (some #(when (= 'main (:name %)) (:result %))))
          named-operations (into (sorted-set) @used-capabilities)
          effects (reduce set/union #{} (vals function-effects))
          _ (when (and (= :pure-product language-profile) (seq effects))
              (reject! "pure-product profile requires empty effects"
                       {:effects effects}
                       :kotoba.error/pure-product-effects))]
      (hir/validate!
       {:format (if typed-values? :kotoba.hir/v3 :kotoba.hir/v2)
        :namespace (:namespace namespace-info)
        :schemas (:schemas namespace-info)
        :schema-identities (:schema-identities namespace-info)
        :entry entry :exports (vec exports)
        :result (when entry main-result)
        ;; Admission conservatively covers private functions too: changing an
        ;; export boundary must never change the authority the module declares.
        :effects effects
        ;; W1: semantic ability/operation names after elaboration (no numeric IDs).
        :named-operations named-operations
        :language-profile language-profile
        :functions functions})))))
