;; Statement-only formalization of thousand-theorems corpus artifact Q1068283,
;; "Löwenheim–Skolem theorem": for an arbitrary first-order language, infinite
;; structure, and sufficiently large infinite cardinal, there is a structure
;; of that cardinality elementarily embedding in one direction. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tags index arbitrary, potentially infinite carriers, languages, structures,
;; assignments, and maps.  The predicates below do not enumerate carriers.
;; Instead, the statement gives the complete first-order syntax and Tarski
;; semantics, and keeps every cardinal, structure, map, and embedding witness
;; under unbounded DEFUN-SK quantification.

(defstub q1068283-function-symbol-p
  (language arity symbol)
  t)

(defstub q1068283-relation-symbol-p
  (language arity symbol)
  t)

(defstub q1068283-carrier-p
  (carrier element)
  t)

(defstub q1068283-function-value
  (language structure arity symbol arguments)
  t)

(defstub q1068283-relation-holds-p
  (language structure arity symbol arguments)
  t)

(defstub q1068283-term-value
  (language structure term assignment bound-values)
  t)

(defstub q1068283-satisfies-p
  (language structure formula assignment bound-values)
  t)

(defstub q1068283-map-value
  (map element)
  t)

(defstub q1068283-base-assignment-value
  (assignment index)
  t)

(defun q1068283-truth (value)
  (if value t nil))

;; Free-variable assignments can be transported through an internally
;; quantified map without introducing an external assignment witness.

(defun q1068283-mapped-assignment-form-p (assignment)
  (and
   (true-listp assignment)
   (equal (len assignment) 3)
   (equal (car assignment) 'q1068283-mapped-assignment)))

(defun q1068283-assignment-value (assignment index)
  (if (q1068283-mapped-assignment-form-p assignment)
      (q1068283-map-value
       (cadr assignment)
       (q1068283-assignment-value (caddr assignment) index))
    (q1068283-base-assignment-value assignment index)))

(defun q1068283-map-assignment (map assignment)
  (list 'q1068283-mapped-assignment map assignment))

;; Finite tuples and lists of bound-variable values.

(defun q1068283-carrier-list-p (carrier values)
  (if (consp values)
      (and
       (q1068283-carrier-p carrier (car values))
       (q1068283-carrier-list-p carrier (cdr values)))
    (equal values nil)))

(defun q1068283-map-list (map values)
  (if (consp values)
      (cons
       (q1068283-map-value map (car values))
       (q1068283-map-list map (cdr values)))
    nil))

;; A term is either (Q1068283-FREE n), (Q1068283-BOUND n), or
;; (Q1068283-FUNCTION arity symbol argument-list).  The work-list recognizer
;; checks all subterms without restricting their number or the carrier.

(defun q1068283-free-term-p (term)
  (and
   (true-listp term)
   (equal (len term) 2)
   (equal (car term) 'q1068283-free)
   (natp (cadr term))))

(defun q1068283-bound-term-p (depth term)
  (and
   (true-listp term)
   (equal (len term) 2)
   (equal (car term) 'q1068283-bound)
   (natp (cadr term))
   (< (cadr term) depth)))

(defun q1068283-function-term-shape-p (term)
  (and
   (true-listp term)
   (equal (len term) 4)
   (equal (car term) 'q1068283-function)
   (natp (cadr term))
   (true-listp (cadddr term))
   (equal (len (cadddr term)) (cadr term))))

(defun q1068283-all-terms-p (language depth pending fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (consp pending)
      (if (zp fuel)
          nil
        (let ((term (car pending)))
          (cond
           ((q1068283-free-term-p term)
            (q1068283-all-terms-p
             language depth (cdr pending) (- fuel 1)))
           ((q1068283-bound-term-p depth term)
            (q1068283-all-terms-p
             language depth (cdr pending) (- fuel 1)))
           ((and
             (q1068283-function-term-shape-p term)
             (q1068283-function-symbol-p
              language (cadr term) (caddr term)))
            (q1068283-all-terms-p
             language
             depth
             (append (cadddr term) (cdr pending))
             (- fuel 1)))
           (t nil))))
    (equal pending nil)))

(defun q1068283-term-p (language depth term)
  (and
   (natp depth)
   (q1068283-all-terms-p
    language depth (list term) (acl2-count term))))

(defun q1068283-term-list-p (language depth arity terms)
  (and
   (natp arity)
   (true-listp terms)
   (equal (len terms) arity)
   (q1068283-all-terms-p
    language depth terms (acl2-count terms))))

;; Mathlib's primitive bounded formulas are falsity, equality, relation
;; application, implication, and universal quantification.  These constructors
;; are represented directly; the natural number DEPTH counts bound variables.

(defun q1068283-formula-p (language depth formula)
  (and
   (natp depth)
   (cond
    ((and
      (true-listp formula)
      (equal (len formula) 1)
      (equal (car formula) 'q1068283-falsum))
     t)
    ((and
      (true-listp formula)
      (equal (len formula) 3)
      (equal (car formula) 'q1068283-equal))
     (and
      (q1068283-term-p language depth (cadr formula))
      (q1068283-term-p language depth (caddr formula))))
    ((and
      (true-listp formula)
      (equal (len formula) 4)
      (equal (car formula) 'q1068283-relation)
      (natp (cadr formula))
      (q1068283-relation-symbol-p
       language (cadr formula) (caddr formula)))
     (q1068283-term-list-p
      language depth (cadr formula) (cadddr formula)))
    ((and
      (true-listp formula)
      (equal (len formula) 3)
      (equal (car formula) 'q1068283-implies))
     (and
      (q1068283-formula-p language depth (cadr formula))
      (q1068283-formula-p language depth (caddr formula))))
    ((and
      (true-listp formula)
      (equal (len formula) 2)
      (equal (car formula) 'q1068283-forall))
     (q1068283-formula-p
      language (+ 1 depth) (cadr formula)))
    (t nil))))

(defun q1068283-term-values
    (language structure terms assignment bound-values)
  (if (consp terms)
      (cons
       (q1068283-term-value
        language structure (car terms) assignment bound-values)
       (q1068283-term-values
        language structure (cdr terms) assignment bound-values))
    nil))

(defun q1068283-holds-p
    (language structure formula assignment bound-values)
  (q1068283-truth
   (q1068283-satisfies-p
    language structure formula assignment bound-values)))

(defun-sk q1068283-assignment-valid-p (carrier assignment)
  (forall (index)
    (implies
     (natp index)
     (q1068283-carrier-p
      carrier
      (q1068283-assignment-value assignment index)))))

(defun-sk q1068283-all-elements-satisfy-p
    (language structure body assignment bound-values)
  (forall (element)
    (implies
     (q1068283-carrier-p structure element)
     (q1068283-holds-p
      language
      structure
      body
      assignment
      (cons element bound-values)))))

;; A language structure has total interpretations of every function symbol.

(defun-sk q1068283-function-closure-p (language structure)
  (forall (arity symbol arguments)
    (implies
     (and
      (natp arity)
      (q1068283-function-symbol-p language arity symbol)
      (true-listp arguments)
      (equal (len arguments) arity)
      (q1068283-carrier-list-p structure arguments))
     (q1068283-carrier-p
      structure
      (q1068283-function-value
       language structure arity symbol arguments)))))

;; The term-value interface is a definitional expansion of recursive term
;; evaluation.  The universally quantified equations characterize variables
;; and function applications exactly.

(defun-sk q1068283-term-semantics-p (language structure)
  (forall
    (depth assignment bound-values term index arity symbol arguments)
    (and
     (implies
      (and
       (natp depth)
       (q1068283-assignment-valid-p structure assignment)
       (q1068283-carrier-list-p structure bound-values)
       (equal (len bound-values) depth)
       (q1068283-term-p language depth term))
      (q1068283-carrier-p
       structure
       (q1068283-term-value
        language structure term assignment bound-values)))
     (implies
      (and
       (q1068283-assignment-valid-p structure assignment)
       (q1068283-carrier-list-p structure bound-values)
       (natp index))
      (equal
       (q1068283-term-value
        language
        structure
        (list 'q1068283-free index)
        assignment
        bound-values)
       (q1068283-assignment-value assignment index)))
     (implies
      (and
       (q1068283-assignment-valid-p structure assignment)
       (q1068283-carrier-list-p structure bound-values)
       (natp index)
       (< index (len bound-values)))
      (equal
       (q1068283-term-value
        language
        structure
        (list 'q1068283-bound index)
        assignment
        bound-values)
       (nth index bound-values)))
     (implies
      (and
       (q1068283-assignment-valid-p structure assignment)
       (q1068283-carrier-list-p structure bound-values)
       (natp arity)
       (q1068283-function-symbol-p language arity symbol)
       (q1068283-term-list-p
        language (len bound-values) arity arguments))
      (equal
       (q1068283-term-value
        language
        structure
        (list 'q1068283-function arity symbol arguments)
        assignment
        bound-values)
       (q1068283-function-value
        language
        structure
        arity
        symbol
        (q1068283-term-values
         language structure arguments assignment bound-values)))))))

;; These are the exact Tarski clauses for the primitive formula constructors.

(defun-sk q1068283-falsum-semantics-p (language structure)
  (forall (assignment bound-values)
    (implies
     (and
      (q1068283-assignment-valid-p structure assignment)
      (q1068283-carrier-list-p structure bound-values))
     (not
      (q1068283-holds-p
       language
       structure
       (list 'q1068283-falsum)
       assignment
       bound-values)))))

(defun-sk q1068283-equality-semantics-p (language structure)
  (forall (assignment bound-values left right)
    (implies
     (and
      (q1068283-assignment-valid-p structure assignment)
      (q1068283-carrier-list-p structure bound-values)
      (q1068283-term-p language (len bound-values) left)
      (q1068283-term-p language (len bound-values) right))
     (equal
      (q1068283-holds-p
       language
       structure
       (list 'q1068283-equal left right)
       assignment
       bound-values)
      (equal
       (q1068283-term-value
        language structure left assignment bound-values)
       (q1068283-term-value
        language structure right assignment bound-values))))))

(defun-sk q1068283-relation-semantics-p (language structure)
  (forall (assignment bound-values arity symbol arguments)
    (implies
     (and
      (q1068283-assignment-valid-p structure assignment)
      (q1068283-carrier-list-p structure bound-values)
      (natp arity)
      (q1068283-relation-symbol-p language arity symbol)
      (q1068283-term-list-p
       language (len bound-values) arity arguments))
     (equal
      (q1068283-holds-p
       language
       structure
       (list 'q1068283-relation arity symbol arguments)
       assignment
       bound-values)
      (q1068283-truth
       (q1068283-relation-holds-p
        language
        structure
        arity
        symbol
        (q1068283-term-values
         language structure arguments assignment bound-values)))))))

(defun-sk q1068283-implication-semantics-p (language structure)
  (forall (assignment bound-values left right)
    (implies
     (and
      (q1068283-assignment-valid-p structure assignment)
      (q1068283-carrier-list-p structure bound-values)
      (q1068283-formula-p
       language (len bound-values) left)
      (q1068283-formula-p
       language (len bound-values) right))
     (equal
      (q1068283-holds-p
       language
       structure
       (list 'q1068283-implies left right)
       assignment
       bound-values)
      (if
       (q1068283-holds-p
        language structure left assignment bound-values)
       (q1068283-holds-p
        language structure right assignment bound-values)
       t)))))

(defun-sk q1068283-universal-semantics-p (language structure)
  (forall (assignment bound-values body)
    (implies
     (and
      (q1068283-assignment-valid-p structure assignment)
      (q1068283-carrier-list-p structure bound-values)
      (q1068283-formula-p
       language (+ 1 (len bound-values)) body))
     (equal
      (q1068283-holds-p
       language
       structure
       (list 'q1068283-forall body)
       assignment
       bound-values)
      (q1068283-truth
       (q1068283-all-elements-satisfy-p
        language structure body assignment bound-values))))))

(defun q1068283-formula-semantics-p (language structure)
  (and
   (q1068283-falsum-semantics-p language structure)
   (q1068283-equality-semantics-p language structure)
   (q1068283-relation-semantics-p language structure)
   (q1068283-implication-semantics-p language structure)
   (q1068283-universal-semantics-p language structure)))

(defun q1068283-structure-p (language structure)
  (and
   (q1068283-function-closure-p language structure)
   (q1068283-term-semantics-p language structure)
   (q1068283-formula-semantics-p language structure)))

;; The cardinal represented by a carrier is infinite exactly when there is an
;; injection from the natural numbers.  This is classically equivalent to
;; Lean's Infinite typeclass and also represents aleph_0 <= kappa.

(defun-sk q1068283-nat-injection-laws-p (carrier map)
  (forall (left right)
    (and
     (implies
      (natp left)
      (q1068283-carrier-p
       carrier (q1068283-map-value map left)))
     (implies
      (and
       (natp left)
       (natp right)
       (equal
        (q1068283-map-value map left)
        (q1068283-map-value map right)))
      (equal left right)))))

(defun-sk q1068283-infinite-carrier-p (carrier)
  (exists (map)
    (q1068283-nat-injection-laws-p carrier map)))

;; A language symbol is the disjointly tagged sigma-type element consisting of
;; its kind, arity, and symbol.  This is exactly mathlib's Language.Symbols.

(defun q1068283-language-symbol-p (language object)
  (and
   (true-listp object)
   (equal (len object) 3)
   (natp (cadr object))
   (if (equal (car object) 'q1068283-function-symbol)
       (q1068283-function-symbol-p
        language (cadr object) (caddr object))
     (and
      (equal (car object) 'q1068283-relation-symbol)
      (q1068283-relation-symbol-p
       language (cadr object) (caddr object))))))

(defun-sk q1068283-language-injection-laws-p
    (language cardinal-carrier map)
  (forall (left right)
    (and
     (implies
      (q1068283-language-symbol-p language left)
      (q1068283-carrier-p
       cardinal-carrier
       (q1068283-map-value map left)))
     (implies
      (and
       (q1068283-language-symbol-p language left)
       (q1068283-language-symbol-p language right)
       (equal
        (q1068283-map-value map left)
        (q1068283-map-value map right)))
      (equal left right)))))

(defun-sk q1068283-language-card-le-p
    (language cardinal-carrier)
  (exists (map)
    (q1068283-language-injection-laws-p
     language cardinal-carrier map)))

;; Cardinal equality is represented by mutually inverse total maps.

(defun-sk q1068283-bijection-laws-p
    (source target forward inverse)
  (forall (source-element target-element)
    (and
     (implies
      (q1068283-carrier-p source source-element)
      (and
       (q1068283-carrier-p
        target
        (q1068283-map-value forward source-element))
       (equal
        (q1068283-map-value
         inverse
         (q1068283-map-value forward source-element))
        source-element)))
     (implies
      (q1068283-carrier-p target target-element)
      (and
       (q1068283-carrier-p
        source
        (q1068283-map-value inverse target-element))
       (equal
        (q1068283-map-value
         forward
         (q1068283-map-value inverse target-element))
        target-element))))))

(defun-sk q1068283-bijection-exists-p (source target)
  (exists (forward inverse)
    (q1068283-bijection-laws-p
     source target forward inverse)))

;; Elementary embeddings are injective structure maps preserving realization
;; of every formula with finitely many free variables.  Free variables are
;; natural-number coded; every individual formula uses only finitely many.

(defun-sk q1068283-embedding-map-laws-p
    (language source target map)
  (forall (left right arity symbol arguments)
    (and
     (implies
      (q1068283-carrier-p source left)
      (q1068283-carrier-p
       target (q1068283-map-value map left)))
     (implies
      (and
       (q1068283-carrier-p source left)
       (q1068283-carrier-p source right)
       (equal
        (q1068283-map-value map left)
        (q1068283-map-value map right)))
      (equal left right))
     (implies
      (and
       (natp arity)
       (q1068283-function-symbol-p language arity symbol)
       (true-listp arguments)
       (equal (len arguments) arity)
       (q1068283-carrier-list-p source arguments))
      (equal
       (q1068283-map-value
        map
        (q1068283-function-value
         language source arity symbol arguments))
       (q1068283-function-value
        language
        target
        arity
        symbol
        (q1068283-map-list map arguments))))
     (implies
      (and
       (natp arity)
       (q1068283-relation-symbol-p language arity symbol)
       (true-listp arguments)
       (equal (len arguments) arity)
       (q1068283-carrier-list-p source arguments))
      (equal
       (q1068283-truth
        (q1068283-relation-holds-p
         language source arity symbol arguments))
       (q1068283-truth
        (q1068283-relation-holds-p
         language
         target
         arity
         symbol
         (q1068283-map-list map arguments))))))))

(defun-sk q1068283-elementary-formula-laws-p
    (language source target map)
  (forall (formula assignment)
    (implies
     (and
      (q1068283-formula-p language 0 formula)
      (q1068283-assignment-valid-p source assignment))
     (equal
      (q1068283-holds-p
       language
       target
       formula
       (q1068283-map-assignment map assignment)
       nil)
      (q1068283-holds-p
       language source formula assignment nil)))))

(defun q1068283-elementary-embedding-p
    (language source target map)
  (and
   (q1068283-embedding-map-laws-p
    language source target map)
   (q1068283-elementary-formula-laws-p
    language source target map)))

(defun-sk q1068283-elementary-embedding-exists-p
    (language source target)
  (exists (map)
    (q1068283-elementary-embedding-p
     language source target map)))

(defun-sk q1068283-lowenheim-skolem-conclusion-p
    (language original cardinal-carrier)
  (exists (new-structure)
    (and
     (q1068283-structure-p language new-structure)
     (q1068283-bijection-exists-p
      new-structure cardinal-carrier)
     (or
      (q1068283-elementary-embedding-exists-p
       language new-structure original)
      (q1068283-elementary-embedding-exists-p
       language original new-structure)))))

(defun-sk
    thousand-theorems-q1068283-lowenheim-skolem-theorem-statement
    ()
  (forall (language original cardinal-carrier)
    (implies
     (and
      (q1068283-structure-p language original)
      (q1068283-infinite-carrier-p original)
      (q1068283-infinite-carrier-p cardinal-carrier)
      (q1068283-language-card-le-p
       language cardinal-carrier))
     (q1068283-lowenheim-skolem-conclusion-p
      language original cardinal-carrier))))

(value-triple :itpeval-statement-checked)
:q
