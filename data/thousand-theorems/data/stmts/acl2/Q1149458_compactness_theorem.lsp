;; Statement-only formalization of thousand-theorems corpus artifact Q1149458,
;; "Compactness theorem": an arbitrary first-order theory has a nonempty model
;; if and only if each of its finite subtheories has a nonempty model. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; These conservative interfaces represent arbitrary, potentially infinite
;; languages, theories, carriers, and interpretations.  No carrier, language,
;; theory, function, or relation is replaced by a finite table.

(defstub q1149458-function-symbol-p
  (language arity symbol)
  t)

(defstub q1149458-relation-symbol-p
  (language arity symbol)
  t)

(defstub q1149458-theory-member-p
  (language theory sentence)
  t)

(defstub q1149458-carrier-p
  (structure element)
  t)

(defstub q1149458-function-value
  (language structure arity symbol arguments)
  t)

(defstub q1149458-relation-holds-p
  (language structure arity symbol arguments)
  t)

(defstub q1149458-term-value
  (language structure term bound-values)
  t)

(defstub q1149458-satisfies-p
  (language structure formula bound-values)
  t)

(defun q1149458-truth (value)
  (if value t nil))

;; Terms use de Bruijn indices for bound variables.  A term is either
;; (Q1149458-BOUND n) or
;; (Q1149458-FUNCTION arity symbol argument-list).

(defun q1149458-bound-term-p (depth term)
  (and
   (true-listp term)
   (equal (len term) 2)
   (equal (car term) 'q1149458-bound)
   (natp (cadr term))
   (< (cadr term) depth)))

(defun q1149458-function-term-shape-p (term)
  (and
   (true-listp term)
   (equal (len term) 4)
   (equal (car term) 'q1149458-function)
   (natp (cadr term))
   (true-listp (cadddr term))
   (equal (len (cadddr term)) (cadr term))))

(defun q1149458-all-terms-p (language depth pending fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (consp pending)
      (if (zp fuel)
          nil
        (let ((term (car pending)))
          (cond
           ((q1149458-bound-term-p depth term)
            (q1149458-all-terms-p
             language depth (cdr pending) (- fuel 1)))
           ((and
             (q1149458-function-term-shape-p term)
             (q1149458-function-symbol-p
              language (cadr term) (caddr term)))
            (q1149458-all-terms-p
             language
             depth
             (append (cadddr term) (cdr pending))
             (- fuel 1)))
           (t nil))))
    (equal pending nil)))

(defun q1149458-term-p (language depth term)
  (and
   (natp depth)
   (q1149458-all-terms-p
    language depth (list term) (acl2-count term))))

(defun q1149458-term-list-p (language depth arity terms)
  (and
   (natp arity)
   (true-listp terms)
   (equal (len terms) arity)
   (q1149458-all-terms-p
    language depth terms (acl2-count terms))))

;; Formulas use the same primitive constructors as the Lean source:
;; falsity, equality, relation application, implication, and universal
;; quantification.  Sentences are exactly the formulas at binder depth zero.

(defun q1149458-formula-p (language depth formula)
  (and
   (natp depth)
   (cond
    ((and
      (true-listp formula)
      (equal (len formula) 1)
      (equal (car formula) 'q1149458-falsum))
     t)
    ((and
      (true-listp formula)
      (equal (len formula) 3)
      (equal (car formula) 'q1149458-equal))
     (and
      (q1149458-term-p language depth (cadr formula))
      (q1149458-term-p language depth (caddr formula))))
    ((and
      (true-listp formula)
      (equal (len formula) 4)
      (equal (car formula) 'q1149458-relation)
      (natp (cadr formula))
      (q1149458-relation-symbol-p
       language (cadr formula) (caddr formula)))
     (q1149458-term-list-p
      language depth (cadr formula) (cadddr formula)))
    ((and
      (true-listp formula)
      (equal (len formula) 3)
      (equal (car formula) 'q1149458-implies))
     (and
      (q1149458-formula-p language depth (cadr formula))
      (q1149458-formula-p language depth (caddr formula))))
    ((and
      (true-listp formula)
      (equal (len formula) 2)
      (equal (car formula) 'q1149458-forall))
     (q1149458-formula-p
      language (+ 1 depth) (cadr formula)))
    (t nil))))

(defun q1149458-sentence-p (language sentence)
  (q1149458-formula-p language 0 sentence))

(defun q1149458-carrier-list-p (structure values)
  (if (consp values)
      (and
       (q1149458-carrier-p structure (car values))
       (q1149458-carrier-list-p structure (cdr values)))
    (equal values nil)))

(defun q1149458-term-values
    (language structure terms bound-values)
  (if (consp terms)
      (cons
       (q1149458-term-value
        language structure (car terms) bound-values)
       (q1149458-term-values
        language structure (cdr terms) bound-values))
    nil))

(defun q1149458-holds-p
    (language structure formula bound-values)
  (q1149458-truth
   (q1149458-satisfies-p
    language structure formula bound-values)))

(defun-sk q1149458-structure-nonempty-p (structure)
  (exists (element)
    (q1149458-carrier-p structure element)))

(defun-sk q1149458-all-elements-satisfy-p
    (language structure body bound-values)
  (forall (element)
    (implies
     (q1149458-carrier-p structure element)
     (q1149458-holds-p
      language structure body (cons element bound-values)))))

;; A structure interprets every function symbol as a total operation on its
;; nonempty carrier.

(defun-sk q1149458-function-closure-p (language structure)
  (forall (arity symbol arguments)
    (implies
     (and
      (natp arity)
      (q1149458-function-symbol-p language arity symbol)
      (true-listp arguments)
      (equal (len arguments) arity)
      (q1149458-carrier-list-p structure arguments))
     (q1149458-carrier-p
      structure
      (q1149458-function-value
       language structure arity symbol arguments)))))

;; The following equations characterize recursive term evaluation exactly.

(defun-sk q1149458-term-semantics-p (language structure)
  (forall (term bound-values index arity symbol arguments)
    (and
     (implies
      (and
       (q1149458-carrier-list-p structure bound-values)
       (q1149458-term-p language (len bound-values) term))
      (q1149458-carrier-p
       structure
       (q1149458-term-value
        language structure term bound-values)))
     (implies
      (and
       (q1149458-carrier-list-p structure bound-values)
       (natp index)
       (< index (len bound-values)))
      (equal
       (q1149458-term-value
        language
        structure
        (list 'q1149458-bound index)
        bound-values)
       (nth index bound-values)))
     (implies
      (and
       (q1149458-carrier-list-p structure bound-values)
       (natp arity)
       (q1149458-function-symbol-p language arity symbol)
       (q1149458-term-list-p
        language (len bound-values) arity arguments))
      (equal
       (q1149458-term-value
        language
        structure
        (list 'q1149458-function arity symbol arguments)
        bound-values)
       (q1149458-function-value
        language
        structure
        arity
        symbol
        (q1149458-term-values
         language structure arguments bound-values)))))))

;; These are the exact Tarski clauses for the primitive formula constructors.

(defun-sk q1149458-falsum-semantics-p (language structure)
  (forall (bound-values)
    (implies
     (q1149458-carrier-list-p structure bound-values)
     (not
      (q1149458-holds-p
       language
       structure
       (list 'q1149458-falsum)
       bound-values)))))

(defun-sk q1149458-equality-semantics-p (language structure)
  (forall (bound-values left right)
    (implies
     (and
      (q1149458-carrier-list-p structure bound-values)
      (q1149458-term-p language (len bound-values) left)
      (q1149458-term-p language (len bound-values) right))
     (equal
      (q1149458-holds-p
       language
       structure
       (list 'q1149458-equal left right)
       bound-values)
      (equal
       (q1149458-term-value
        language structure left bound-values)
       (q1149458-term-value
        language structure right bound-values))))))

(defun-sk q1149458-relation-semantics-p (language structure)
  (forall (bound-values arity symbol arguments)
    (implies
     (and
      (q1149458-carrier-list-p structure bound-values)
      (natp arity)
      (q1149458-relation-symbol-p language arity symbol)
      (q1149458-term-list-p
       language (len bound-values) arity arguments))
     (equal
      (q1149458-holds-p
       language
       structure
       (list 'q1149458-relation arity symbol arguments)
       bound-values)
      (q1149458-truth
       (q1149458-relation-holds-p
        language
        structure
        arity
        symbol
        (q1149458-term-values
         language structure arguments bound-values)))))))

(defun-sk q1149458-implication-semantics-p (language structure)
  (forall (bound-values left right)
    (implies
     (and
      (q1149458-carrier-list-p structure bound-values)
      (q1149458-formula-p
       language (len bound-values) left)
      (q1149458-formula-p
       language (len bound-values) right))
     (equal
      (q1149458-holds-p
       language
       structure
       (list 'q1149458-implies left right)
       bound-values)
      (if
       (q1149458-holds-p
        language structure left bound-values)
       (q1149458-holds-p
        language structure right bound-values)
       t)))))

(defun-sk q1149458-universal-semantics-p (language structure)
  (forall (bound-values body)
    (implies
     (and
      (q1149458-carrier-list-p structure bound-values)
      (q1149458-formula-p
       language (+ 1 (len bound-values)) body))
     (equal
      (q1149458-holds-p
       language
       structure
       (list 'q1149458-forall body)
       bound-values)
      (q1149458-truth
       (q1149458-all-elements-satisfy-p
        language structure body bound-values))))))

(defun q1149458-formula-semantics-p (language structure)
  (and
   (q1149458-falsum-semantics-p language structure)
   (q1149458-equality-semantics-p language structure)
   (q1149458-relation-semantics-p language structure)
   (q1149458-implication-semantics-p language structure)
   (q1149458-universal-semantics-p language structure)))

(defun q1149458-structure-p (language structure)
  (and
   (q1149458-structure-nonempty-p structure)
   (q1149458-function-closure-p language structure)
   (q1149458-term-semantics-p language structure)
   (q1149458-formula-semantics-p language structure)))

;; The ACL2 type guard corresponding to Lean's L.Theory requires every member
;; of the arbitrary theory predicate to be a sentence of the given language.

(defun-sk q1149458-theory-p (language theory)
  (forall (sentence)
    (implies
     (q1149458-theory-member-p language theory sentence)
     (q1149458-sentence-p language sentence))))

(defun-sk q1149458-structure-models-theory-p
    (language structure theory)
  (forall (sentence)
    (implies
     (q1149458-theory-member-p language theory sentence)
     (q1149458-holds-p language structure sentence nil))))

(defun-sk q1149458-satisfiable-p (language theory)
  (exists (structure)
    (and
     (q1149458-structure-p language structure)
     (q1149458-structure-models-theory-p
      language structure theory))))

;; A true list denotes the finite set of its entries.  Quantifying over all
;; such lists is equivalent to quantifying over all finite subtheories:
;; repetitions do not affect whether a single structure models every entry.

(defun q1149458-sentence-list-p (language sentences)
  (if (consp sentences)
      (and
       (q1149458-sentence-p language (car sentences))
       (q1149458-sentence-list-p language (cdr sentences)))
    (equal sentences nil)))

(defun q1149458-list-subset-theory-p
    (language theory sentences)
  (if (consp sentences)
      (and
       (q1149458-theory-member-p
        language theory (car sentences))
       (q1149458-list-subset-theory-p
        language theory (cdr sentences)))
    (equal sentences nil)))

(defun q1149458-structure-models-list-p
    (language structure sentences)
  (if (consp sentences)
      (and
       (q1149458-holds-p
        language structure (car sentences) nil)
       (q1149458-structure-models-list-p
        language structure (cdr sentences)))
    (equal sentences nil)))

(defun-sk q1149458-finite-subtheory-satisfiable-p
    (language sentences)
  (exists (structure)
    (and
     (q1149458-sentence-list-p language sentences)
     (q1149458-structure-p language structure)
     (q1149458-structure-models-list-p
      language structure sentences))))

(defun-sk q1149458-finitely-satisfiable-p
    (language theory)
  (forall (sentences)
    (implies
     (and
      (q1149458-sentence-list-p language sentences)
      (q1149458-list-subset-theory-p
       language theory sentences))
     (q1149458-finite-subtheory-satisfiable-p
      language sentences))))

(defun-sk
    thousand-theorems-q1149458-compactness-theorem-statement
    ()
  (forall (language theory)
    (implies
     (q1149458-theory-p language theory)
     (iff
      (q1149458-satisfiable-p language theory)
      (q1149458-finitely-satisfiable-p
       language theory)))))

(value-triple :itpeval-statement-checked)
:q
