(ns kotoba.sema
  "Stable public entry points for Kotoba source semantic analysis."
  (:require [kotoba.compiler.frontend :as frontend]
            [kotoba.compiler.schema :as schema]))

(def read-forms
  "Read Kotoba source using the admitted reader profile."
  frontend/read-forms)

(def validate-schema-table!
  "Validate a named schema table and return it."
  schema/validate-table!)

(def schema-identities
  "Return stable nominal content identities for a schema table."
  schema/identities)

(def capability-registry frontend/capability-registry)
(def source-operation-registry frontend/source-operation-registry)
(def capability-id->name frontend/capability-id->name)
(def forbidden-heads frontend/forbidden-heads)
(def max-functions frontend/max-functions)
(def max-expression-nodes frontend/max-expression-nodes)
(def max-lowered-nodes frontend/max-lowered-nodes)
(def max-bindings frontend/max-bindings)
(def max-list-items frontend/max-list-items)
(def max-namespace-capabilities frontend/max-namespace-capabilities)
(def max-namespace-docstring-chars frontend/max-namespace-docstring-chars)
(def max-function-docstring-chars frontend/max-function-docstring-chars)
(def kernel-region-report frontend/kernel-region-report)

(defn- default-controls? []
  (= [max-functions max-expression-nodes max-lowered-nodes max-bindings
      max-list-items max-namespace-capabilities
      max-namespace-docstring-chars max-function-docstring-chars]
     [frontend/max-functions frontend/max-expression-nodes
      frontend/max-lowered-nodes frontend/max-bindings
      frontend/max-list-items frontend/max-namespace-capabilities
      frontend/max-namespace-docstring-chars
      frontend/max-function-docstring-chars]))

(defn- analyze-with-controls [source opts]
  (if (default-controls?)
    (frontend/analyze source opts)
    ;; Rebinding is only entered when a caller explicitly overrides the public
    ;; facade controls (principally bounded tests). Normal concurrent analysis
    ;; stays on the direct, mutation-free path above.
    (with-redefs [frontend/max-functions max-functions
                  frontend/max-expression-nodes max-expression-nodes
                  frontend/max-lowered-nodes max-lowered-nodes
                  frontend/max-bindings max-bindings
                  frontend/max-list-items max-list-items
                  frontend/max-namespace-capabilities max-namespace-capabilities
                  frontend/max-namespace-docstring-chars max-namespace-docstring-chars
                  frontend/max-function-docstring-chars max-function-docstring-chars]
      (frontend/analyze source opts))))

(defn analyze
  "Analyze Kotoba source and return a validated HIR envelope. Public admission
  controls are authoritative when explicitly overridden."
  ([source] (analyze-with-controls source nil))
  ([source opts] (analyze-with-controls source opts)))
