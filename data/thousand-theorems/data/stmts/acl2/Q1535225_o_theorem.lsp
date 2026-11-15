;; Statement-only formalization of thousand-theorems corpus artifact Q1535225,
;; "Łoś' theorem": a sentence holds in an ultraproduct of nonempty first-order
;; structures exactly when it holds in an ultrafilter-large set of component
;; structures. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Conservative interfaces represent arbitrary, potentially infinite index
;; types, first-order languages, carriers, structures, dependent functions,
;; subsets, and ultrafilters.  Lists below encode only finite syntax and finite
;; argument tuples; no mathematical carrier or function space is enumerated.

(defstub q1535225-index-p
  (index-carrier index)
  t)

(defstub q1535225-function-symbol-p
  (language arity symbol)
  t)

(defstub q1535225-relation-symbol-p
  (language arity symbol)
  t)

(defstub q1535225-structure-at
  (family index)
  t)

(defstub q1535225-carrier-p
  (structure element)
  t)

(defstub q1535225-structure-equal-p
  (structure left right)
  t)

(defstub q1535225-function-value
  (language structure arity symbol arguments)
  t)

(defstub q1535225-relation-holds-p
  (language structure arity symbol arguments)
  t)

(defstub q1535225-term-value
  (language structure term bound-values)
  t)

(defstub q1535225-satisfies-p
  (language structure formula bound-values)
  t)

(defstub q1535225-base-map-value
  (map index)
  t)

(defstub q1535225-base-pointwise-choice-value
  (choice index)
  t)

(defstub q1535225-base-set-member-p
  (index-carrier set index)
  t)

(defstub q1535225-filter-member-p
  (ultrafilter set)
  t)

(defchoose q1535225-carrier-choice
    (element)
    (structure)
  (q1535225-carrier-p structure element))

(defun q1535225-default-product-map (index-carrier family)
  (list 'q1535225-default-product-map index-carrier family))

(defun q1535225-default-product-map-form-p (map)
  (and
   (true-listp map)
   (equal (len map) 3)
   (equal (car map) 'q1535225-default-product-map)))

(defun q1535225-map-value (map index)
  (if (q1535225-default-product-map-form-p map)
      (q1535225-carrier-choice
       (q1535225-structure-at (caddr map) index))
    (q1535225-base-map-value map index)))

(defun q1535225-truth (value)
  (if value t nil))

;; Closed formulas use de Bruijn indices for bound variables and the primitive
;; constructors from the Lean source: falsity, equality, relation application,
;; implication, and universal quantification.

(defun q1535225-bound-term-p (depth term)
  (and
   (true-listp term)
   (equal (len term) 2)
   (equal (car term) 'q1535225-bound)
   (natp (cadr term))
   (< (cadr term) depth)))

(defun q1535225-function-term-shape-p (term)
  (and
   (true-listp term)
   (equal (len term) 4)
   (equal (car term) 'q1535225-function)
   (natp (cadr term))
   (true-listp (cadddr term))
   (equal (len (cadddr term)) (cadr term))))

(defun q1535225-all-terms-p (language depth pending fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (consp pending)
      (if (zp fuel)
          nil
        (let ((term (car pending)))
          (cond
           ((q1535225-bound-term-p depth term)
            (q1535225-all-terms-p
             language depth (cdr pending) (- fuel 1)))
           ((and
             (q1535225-function-term-shape-p term)
             (q1535225-function-symbol-p
              language (cadr term) (caddr term)))
            (q1535225-all-terms-p
             language
             depth
             (append (cadddr term) (cdr pending))
             (- fuel 1)))
           (t nil))))
    (equal pending nil)))

(defun q1535225-term-p (language depth term)
  (and
   (natp depth)
   (q1535225-all-terms-p
    language depth (list term) (acl2-count term))))

(defun q1535225-term-list-p (language depth arity terms)
  (and
   (natp arity)
   (true-listp terms)
   (equal (len terms) arity)
   (q1535225-all-terms-p
    language depth terms (acl2-count terms))))

(defun q1535225-formula-p (language depth formula)
  (and
   (natp depth)
   (cond
    ((and
      (true-listp formula)
      (equal (len formula) 1)
      (equal (car formula) 'q1535225-falsum))
     t)
    ((and
      (true-listp formula)
      (equal (len formula) 3)
      (equal (car formula) 'q1535225-equal))
     (and
      (q1535225-term-p language depth (cadr formula))
      (q1535225-term-p language depth (caddr formula))))
    ((and
      (true-listp formula)
      (equal (len formula) 4)
      (equal (car formula) 'q1535225-relation)
      (natp (cadr formula))
      (q1535225-relation-symbol-p
       language (cadr formula) (caddr formula)))
     (q1535225-term-list-p
      language depth (cadr formula) (cadddr formula)))
    ((and
      (true-listp formula)
      (equal (len formula) 3)
      (equal (car formula) 'q1535225-implies))
     (and
      (q1535225-formula-p language depth (cadr formula))
      (q1535225-formula-p language depth (caddr formula))))
    ((and
      (true-listp formula)
      (equal (len formula) 2)
      (equal (car formula) 'q1535225-forall))
     (q1535225-formula-p
      language (+ 1 depth) (cadr formula)))
    (t nil))))

(defun q1535225-sentence-p (language sentence)
  (q1535225-formula-p language 0 sentence))

(defun q1535225-carrier-list-p (structure values)
  (if (consp values)
      (and
       (q1535225-carrier-p structure (car values))
       (q1535225-carrier-list-p structure (cdr values)))
    (equal values nil)))

(defun q1535225-equivalent-lists-p (structure left right)
  (if (consp left)
      (and
       (consp right)
       (q1535225-truth
        (q1535225-structure-equal-p
         structure (car left) (car right)))
       (q1535225-equivalent-lists-p
        structure (cdr left) (cdr right)))
    (equal right nil)))

(defun q1535225-term-values
    (language structure terms bound-values)
  (if (consp terms)
      (cons
       (q1535225-term-value
        language structure (car terms) bound-values)
       (q1535225-term-values
        language structure (cdr terms) bound-values))
    nil))

(defun q1535225-holds-p
    (language structure formula bound-values)
  (q1535225-truth
   (q1535225-satisfies-p
    language structure formula bound-values)))

(defun q1535225-pointwise-values (arguments index)
  (if (consp arguments)
      (cons
       (q1535225-map-value (car arguments) index)
       (q1535225-pointwise-values (cdr arguments) index))
    nil))

(defun-sk q1535225-counterexample-exists-p
    (language structure body bound-values)
  (exists (element)
    (and
     (q1535225-carrier-p structure element)
     (not
      (q1535225-holds-p
       language structure body (cons element bound-values))))))

(defchoose q1535225-counterexample-choice
    (element)
    (language structure body bound-values)
  (and
   (q1535225-carrier-p structure element)
   (not
    (q1535225-holds-p
     language structure body (cons element bound-values)))))

(defun q1535225-formula-pointwise-choice
    (language family body bound-maps)
  (list
   'q1535225-formula-pointwise-choice
   language
   family
   body
   bound-maps))

(defun q1535225-formula-pointwise-choice-form-p (choice)
  (and
   (true-listp choice)
   (equal (len choice) 5)
   (equal (car choice) 'q1535225-formula-pointwise-choice)))

;; This reserved pointwise choice is the function constructed in the universal
;; case of the Lean proof.  At each component it selects a counterexample to
;; BODY for the pointwise bound assignment when one exists, and otherwise uses
;; component nonemptiness.  Generic choices use the conservative base
;; interface below.

(defun q1535225-pointwise-choice-value (choice index)
  (if (q1535225-formula-pointwise-choice-form-p choice)
      (let* ((language (cadr choice))
             (family (caddr choice))
             (body (cadddr choice))
             (bound-maps (car (cddddr choice)))
             (structure
              (q1535225-structure-at family index))
             (bound-values
              (q1535225-pointwise-values bound-maps index)))
        (if
         (q1535225-counterexample-exists-p
          language structure body bound-values)
         (q1535225-counterexample-choice
          language structure body bound-values)
          (q1535225-carrier-choice structure)))
    (q1535225-base-pointwise-choice-value choice index)))

(defun-sk q1535225-structure-nonempty-p (structure)
  (exists (element)
    (q1535225-carrier-p structure element)))

(defun-sk q1535225-all-elements-satisfy-p
    (language structure body bound-values)
  (forall (element)
    (implies
     (q1535225-carrier-p structure element)
     (q1535225-holds-p
      language structure body (cons element bound-values)))))

;; Structures may be presented as setoids.  These laws say that equality is an
;; equivalence relation on the carrier and that all interpretations respect it.
;; Component structures below use literal ACL2 equality; the ultraproduct uses
;; almost-everywhere equality of representatives.

(defun-sk q1535225-equality-laws-p (structure)
  (forall (left middle right)
    (and
     (implies
      (q1535225-carrier-p structure left)
      (q1535225-truth
       (q1535225-structure-equal-p structure left left)))
     (implies
      (q1535225-truth
       (q1535225-structure-equal-p structure left right))
      (and
       (q1535225-carrier-p structure left)
       (q1535225-carrier-p structure right)
       (q1535225-truth
        (q1535225-structure-equal-p structure right left))))
     (implies
      (and
       (q1535225-truth
        (q1535225-structure-equal-p structure left middle))
       (q1535225-truth
        (q1535225-structure-equal-p structure middle right)))
      (q1535225-truth
       (q1535225-structure-equal-p structure left right))))))

(defun-sk q1535225-function-closure-p (language structure)
  (forall (arity symbol arguments)
    (implies
     (and
      (natp arity)
      (q1535225-function-symbol-p language arity symbol)
      (true-listp arguments)
      (equal (len arguments) arity)
      (q1535225-carrier-list-p structure arguments))
     (q1535225-carrier-p
      structure
      (q1535225-function-value
       language structure arity symbol arguments)))))

(defun-sk q1535225-function-congruence-p (language structure)
  (forall (arity symbol left right)
    (implies
     (and
      (natp arity)
      (q1535225-function-symbol-p language arity symbol)
      (true-listp left)
      (true-listp right)
      (equal (len left) arity)
      (equal (len right) arity)
      (q1535225-carrier-list-p structure left)
      (q1535225-carrier-list-p structure right)
      (q1535225-equivalent-lists-p structure left right))
     (q1535225-truth
      (q1535225-structure-equal-p
       structure
       (q1535225-function-value
        language structure arity symbol left)
       (q1535225-function-value
        language structure arity symbol right))))))

(defun-sk q1535225-relation-congruence-p (language structure)
  (forall (arity symbol left right)
    (implies
     (and
      (natp arity)
      (q1535225-relation-symbol-p language arity symbol)
      (true-listp left)
      (true-listp right)
      (equal (len left) arity)
      (equal (len right) arity)
      (q1535225-carrier-list-p structure left)
      (q1535225-carrier-list-p structure right)
      (q1535225-equivalent-lists-p structure left right))
     (equal
      (q1535225-truth
       (q1535225-relation-holds-p
        language structure arity symbol left))
      (q1535225-truth
       (q1535225-relation-holds-p
        language structure arity symbol right))))))

(defun-sk q1535225-term-semantics-p (language structure)
  (forall (term bound-values index arity symbol arguments)
    (and
     (implies
      (and
       (q1535225-carrier-list-p structure bound-values)
       (q1535225-term-p language (len bound-values) term))
      (q1535225-carrier-p
       structure
       (q1535225-term-value
        language structure term bound-values)))
     (implies
      (and
       (q1535225-carrier-list-p structure bound-values)
       (natp index)
       (< index (len bound-values)))
      (equal
       (q1535225-term-value
        language
        structure
        (list 'q1535225-bound index)
        bound-values)
       (nth index bound-values)))
     (implies
      (and
       (q1535225-carrier-list-p structure bound-values)
       (natp arity)
       (q1535225-function-symbol-p language arity symbol)
       (q1535225-term-list-p
        language (len bound-values) arity arguments))
      (equal
       (q1535225-term-value
        language
        structure
        (list 'q1535225-function arity symbol arguments)
        bound-values)
       (q1535225-function-value
        language
        structure
        arity
        symbol
        (q1535225-term-values
         language structure arguments bound-values)))))))

;; Exact Tarski clauses for the primitive formula constructors.

(defun-sk q1535225-falsum-semantics-p (language structure)
  (forall (bound-values)
    (implies
     (q1535225-carrier-list-p structure bound-values)
     (not
      (q1535225-holds-p
       language
       structure
       (list 'q1535225-falsum)
       bound-values)))))

(defun-sk q1535225-equality-semantics-p (language structure)
  (forall (bound-values left right)
    (implies
     (and
      (q1535225-carrier-list-p structure bound-values)
      (q1535225-term-p language (len bound-values) left)
      (q1535225-term-p language (len bound-values) right))
     (equal
      (q1535225-holds-p
       language
       structure
       (list 'q1535225-equal left right)
       bound-values)
      (q1535225-truth
       (q1535225-structure-equal-p
        structure
        (q1535225-term-value
         language structure left bound-values)
        (q1535225-term-value
         language structure right bound-values)))))))

(defun-sk q1535225-relation-semantics-p (language structure)
  (forall (bound-values arity symbol arguments)
    (implies
     (and
      (q1535225-carrier-list-p structure bound-values)
      (natp arity)
      (q1535225-relation-symbol-p language arity symbol)
      (q1535225-term-list-p
       language (len bound-values) arity arguments))
     (equal
      (q1535225-holds-p
       language
       structure
       (list 'q1535225-relation arity symbol arguments)
       bound-values)
      (q1535225-truth
       (q1535225-relation-holds-p
        language
        structure
        arity
        symbol
        (q1535225-term-values
         language structure arguments bound-values)))))))

(defun-sk q1535225-implication-semantics-p (language structure)
  (forall (bound-values left right)
    (implies
     (and
      (q1535225-carrier-list-p structure bound-values)
      (q1535225-formula-p
       language (len bound-values) left)
      (q1535225-formula-p
       language (len bound-values) right))
     (equal
      (q1535225-holds-p
       language
       structure
       (list 'q1535225-implies left right)
       bound-values)
      (if
       (q1535225-holds-p
        language structure left bound-values)
       (q1535225-holds-p
        language structure right bound-values)
       t)))))

(defun-sk q1535225-universal-semantics-p (language structure)
  (forall (bound-values body)
    (implies
     (and
      (q1535225-carrier-list-p structure bound-values)
      (q1535225-formula-p
       language (+ 1 (len bound-values)) body))
     (equal
      (q1535225-holds-p
       language
       structure
       (list 'q1535225-forall body)
       bound-values)
      (q1535225-truth
       (q1535225-all-elements-satisfy-p
        language structure body bound-values))))))

(defun q1535225-formula-semantics-p (language structure)
  (and
   (q1535225-falsum-semantics-p language structure)
   (q1535225-equality-semantics-p language structure)
   (q1535225-relation-semantics-p language structure)
   (q1535225-implication-semantics-p language structure)
   (q1535225-universal-semantics-p language structure)))

(defun q1535225-structure-p (language structure)
  (and
   (q1535225-equality-laws-p structure)
   (q1535225-function-closure-p language structure)
   (q1535225-function-congruence-p language structure)
   (q1535225-relation-congruence-p language structure)
   (q1535225-term-semantics-p language structure)
   (q1535225-formula-semantics-p language structure)))

;; Each component is a nonempty ordinary first-order structure: its setoid
;; equality is literal equality on its carrier.  Nonemptiness is a separate
;; family assumption, matching the Lean theorem's [Nonempty (M a)] instances.

(defun-sk q1535225-literal-equality-p (structure)
  (forall (left right)
    (implies
     (and
      (q1535225-carrier-p structure left)
      (q1535225-carrier-p structure right))
     (equal
      (q1535225-truth
       (q1535225-structure-equal-p structure left right))
      (equal left right)))))

(defun-sk q1535225-family-p
    (language index-carrier family)
  (forall (index)
    (implies
     (q1535225-index-p index-carrier index)
     (let ((structure
            (q1535225-structure-at family index)))
       (and
        (q1535225-structure-p language structure)
        (q1535225-structure-nonempty-p structure)
        (q1535225-literal-equality-p structure))))))

;; Sets of indices are represented extensionally.  Reserved constructors below
;; denote the universe, empty set, Boolean operations, and the sets arising in
;; the ultraproduct definition.  All other tags use BASE-SET-MEMBER-P.

(defun q1535225-universe-set ()
  (list 'q1535225-universe-set))

(defun q1535225-empty-set ()
  (list 'q1535225-empty-set))

(defun q1535225-intersection-set (left right)
  (list 'q1535225-intersection-set left right))

(defun q1535225-complement-set (set)
  (list 'q1535225-complement-set set))

(defun q1535225-equality-set (family left right)
  (list 'q1535225-equality-set family left right))

(defun q1535225-relation-set
    (language family arity symbol arguments)
  (list
   'q1535225-relation-set
   language
   family
   arity
   symbol
   arguments))

(defun q1535225-sentence-set (language family sentence)
  (list 'q1535225-sentence-set language family sentence))

(defun q1535225-set-member-p (index-carrier set index)
  (declare (xargs :measure (acl2-count set)))
  (if (not (q1535225-index-p index-carrier index))
      nil
    (cond
     ((and
       (true-listp set)
       (equal (len set) 1)
       (equal (car set) 'q1535225-universe-set))
      t)
     ((and
       (true-listp set)
       (equal (len set) 1)
       (equal (car set) 'q1535225-empty-set))
      nil)
     ((and
       (true-listp set)
       (equal (len set) 3)
       (equal (car set) 'q1535225-intersection-set))
      (and
       (q1535225-set-member-p
        index-carrier (cadr set) index)
       (q1535225-set-member-p
        index-carrier (caddr set) index)))
     ((and
       (true-listp set)
       (equal (len set) 2)
       (equal (car set) 'q1535225-complement-set))
      (not
       (q1535225-set-member-p
        index-carrier (cadr set) index)))
     ((and
       (true-listp set)
       (equal (len set) 4)
       (equal (car set) 'q1535225-equality-set))
      (q1535225-truth
       (q1535225-structure-equal-p
        (q1535225-structure-at (cadr set) index)
        (q1535225-map-value (caddr set) index)
        (q1535225-map-value (cadddr set) index))))
     ((and
       (true-listp set)
       (equal (len set) 6)
       (equal (car set) 'q1535225-relation-set))
      (q1535225-truth
       (q1535225-relation-holds-p
        (cadr set)
        (q1535225-structure-at (caddr set) index)
        (cadddr set)
        (car (cddddr set))
        (q1535225-pointwise-values
         (cadr (cddddr set)) index))))
     ((and
       (true-listp set)
       (equal (len set) 4)
       (equal (car set) 'q1535225-sentence-set))
      (q1535225-holds-p
       (cadr set)
       (q1535225-structure-at (caddr set) index)
       (cadddr set)
       nil))
     (t
      (q1535225-truth
       (q1535225-base-set-member-p
        index-carrier set index))))))

(defun-sk q1535225-set-subset-p
    (index-carrier left right)
  (forall (index)
    (implies
     (q1535225-set-member-p index-carrier left index)
     (q1535225-set-member-p index-carrier right index))))

(defun q1535225-eventually-p (ultrafilter set)
  (q1535225-truth
   (q1535225-filter-member-p ultrafilter set)))

;; These are the proper-filter and ultrafilter laws on the full arbitrary set
;; interface.  They are not restricted to the special sets used in the result.

(defun-sk q1535225-ultrafilter-set-laws-p
    (index-carrier ultrafilter)
  (forall (left right)
    (and
     (equal
      (q1535225-eventually-p
       ultrafilter
       (q1535225-intersection-set left right))
      (and
       (q1535225-eventually-p ultrafilter left)
       (q1535225-eventually-p ultrafilter right)))
     (implies
      (and
       (q1535225-eventually-p ultrafilter left)
       (q1535225-set-subset-p index-carrier left right))
      (q1535225-eventually-p ultrafilter right))
     (or
      (q1535225-eventually-p ultrafilter left)
      (q1535225-eventually-p
       ultrafilter
       (q1535225-complement-set left))))))

(defun q1535225-ultrafilter-p
    (index-carrier ultrafilter)
  (and
   (q1535225-eventually-p
    ultrafilter (q1535225-universe-set))
   (not
    (q1535225-eventually-p
     ultrafilter (q1535225-empty-set)))
   (q1535225-ultrafilter-set-laws-p
    index-carrier ultrafilter)))

;; The ultraproduct is presented by representatives rather than quotient
;; objects.  Its carrier consists of dependent functions choosing an element
;; of each component, and its equality is almost-everywhere component
;; equality.  A conservative DEFCHOOSE map supplies the representative whose
;; existence follows from component nonemptiness, while the fullness and
;; formula-witness laws below supply all pointwise choices needed by arbitrary
;; first-order quantifiers.  Thus quantification over these representatives
;; has the same sentence semantics as quantification over Lean's full dependent
;; product, and quotienting by almost-everywhere equality preserves it.

(defun q1535225-ultraproduct-structure
    (language index-carrier family ultrafilter)
  (list
   'q1535225-ultraproduct
   language
   index-carrier
   family
   ultrafilter))

(defun-sk q1535225-product-map-p
    (index-carrier family map)
  (forall (index)
    (implies
     (q1535225-index-p index-carrier index)
     (q1535225-carrier-p
      (q1535225-structure-at family index)
      (q1535225-map-value map index)))))

(defun q1535225-product-map-list-p
    (index-carrier family maps)
  (if (consp maps)
      (and
       (q1535225-product-map-p
        index-carrier family (car maps))
       (q1535225-product-map-list-p
        index-carrier family (cdr maps)))
    (equal maps nil)))

;; Fullness of the representative sort: every pointwise family of component
;; elements has a map code realizing it.  This is the target-native
;; surjectivity condition identifying map codes with the full dependent
;; function type (forall a, M a), rather than with an arbitrary subcollection.

(defun-sk q1535225-pointwise-choice-valid-p
    (index-carrier family choice)
  (forall (index)
    (implies
     (q1535225-index-p index-carrier index)
     (q1535225-carrier-p
      (q1535225-structure-at family index)
      (q1535225-pointwise-choice-value choice index)))))

(defun-sk q1535225-map-realizes-pointwise-choice-p
    (index-carrier choice map)
  (forall (index)
    (implies
     (q1535225-index-p index-carrier index)
     (equal
      (q1535225-map-value map index)
      (q1535225-pointwise-choice-value choice index)))))

(defun-sk q1535225-pointwise-choice-represented-p
    (index-carrier family choice)
  (exists (map)
    (and
     (q1535225-product-map-p index-carrier family map)
     (q1535225-map-realizes-pointwise-choice-p
      index-carrier choice map))))

(defun-sk q1535225-full-dependent-product-p
    (index-carrier family)
  (forall (choice)
    (implies
     (q1535225-pointwise-choice-valid-p
      index-carrier family choice)
     (q1535225-pointwise-choice-represented-p
      index-carrier family choice))))

;; The formula-specific closure makes the quantifier equivalence explicit.
;; Given any bounded formula and finite list of representative parameters, the
;; pointwise counterexample family above is represented by a product map.  By
;; structural induction this is exactly the additional choice needed to pass
;; between quantification over representatives and quantification in every
;; component; atomic formulas and implication use the pointwise and
;; ultrafilter clauses directly.

(defun-sk q1535225-formula-witness-maps-p
    (language index-carrier family)
  (forall (body bound-maps)
    (implies
     (and
      (q1535225-product-map-list-p
       index-carrier family bound-maps)
      (q1535225-formula-p
       language (+ 1 (len bound-maps)) body))
     (q1535225-pointwise-choice-represented-p
      index-carrier
      family
      (q1535225-formula-pointwise-choice
       language family body bound-maps)))))

(defun-sk q1535225-ultraproduct-carrier-laws-p
    (language index-carrier family ultrafilter)
  (forall (map)
    (equal
     (q1535225-truth
      (q1535225-carrier-p
       (q1535225-ultraproduct-structure
        language index-carrier family ultrafilter)
       map))
     (q1535225-truth
      (q1535225-product-map-p
       index-carrier family map)))))

(defun-sk q1535225-ultraproduct-equality-laws-p
    (language index-carrier family ultrafilter)
  (forall (left right)
    (equal
     (q1535225-truth
      (q1535225-structure-equal-p
       (q1535225-ultraproduct-structure
        language index-carrier family ultrafilter)
       left
       right))
     (and
      (q1535225-product-map-p index-carrier family left)
      (q1535225-product-map-p index-carrier family right)
      (q1535225-eventually-p
       ultrafilter
       (q1535225-equality-set family left right))))))

(defun-sk q1535225-ultraproduct-function-laws-p
    (language index-carrier family ultrafilter)
  (forall (arity symbol arguments index)
    (implies
     (and
      (natp arity)
      (q1535225-function-symbol-p language arity symbol)
      (true-listp arguments)
      (equal (len arguments) arity)
      (q1535225-carrier-list-p
       (q1535225-ultraproduct-structure
        language index-carrier family ultrafilter)
       arguments)
      (q1535225-index-p index-carrier index))
     (equal
      (q1535225-map-value
       (q1535225-function-value
        language
        (q1535225-ultraproduct-structure
         language index-carrier family ultrafilter)
        arity
        symbol
        arguments)
       index)
      (q1535225-function-value
       language
       (q1535225-structure-at family index)
       arity
       symbol
       (q1535225-pointwise-values arguments index))))))

(defun-sk q1535225-ultraproduct-relation-laws-p
    (language index-carrier family ultrafilter)
  (forall (arity symbol arguments)
    (implies
     (and
      (natp arity)
      (q1535225-relation-symbol-p language arity symbol)
      (true-listp arguments)
      (equal (len arguments) arity)
      (q1535225-carrier-list-p
       (q1535225-ultraproduct-structure
        language index-carrier family ultrafilter)
       arguments))
     (equal
      (q1535225-truth
       (q1535225-relation-holds-p
        language
        (q1535225-ultraproduct-structure
         language index-carrier family ultrafilter)
        arity
        symbol
        arguments))
      (q1535225-eventually-p
       ultrafilter
       (q1535225-relation-set
        language family arity symbol arguments))))))

(defun q1535225-ultraproduct-p
    (language index-carrier family ultrafilter)
  (let ((structure
         (q1535225-ultraproduct-structure
          language index-carrier family ultrafilter)))
    (and
     (q1535225-full-dependent-product-p
      index-carrier family)
     (q1535225-formula-witness-maps-p
      language index-carrier family)
     (q1535225-ultraproduct-carrier-laws-p
      language index-carrier family ultrafilter)
     (q1535225-ultraproduct-equality-laws-p
      language index-carrier family ultrafilter)
     (q1535225-ultraproduct-function-laws-p
      language index-carrier family ultrafilter)
     (q1535225-ultraproduct-relation-laws-p
      language index-carrier family ultrafilter)
     (q1535225-structure-p language structure))))

(defun q1535225-sentence-realize-equivalence-p
    (language index-carrier family ultrafilter sentence)
  (equal
   (q1535225-holds-p
    language
    (q1535225-ultraproduct-structure
     language index-carrier family ultrafilter)
    sentence
    nil)
   (q1535225-eventually-p
    ultrafilter
    (q1535225-sentence-set language family sentence))))

(defun-sk
    thousand-theorems-q1535225-los-theorem-statement
    ()
  (forall
    (language index-carrier family ultrafilter sentence)
    (implies
     (and
      (q1535225-family-p language index-carrier family)
      (q1535225-ultrafilter-p index-carrier ultrafilter)
      (q1535225-sentence-p language sentence)
      (q1535225-ultraproduct-p
       language index-carrier family ultrafilter))
     (q1535225-sentence-realize-equivalence-p
      language
      index-carrier
      family
      ultrafilter
      sentence))))

(value-triple :itpeval-statement-checked)
:q
