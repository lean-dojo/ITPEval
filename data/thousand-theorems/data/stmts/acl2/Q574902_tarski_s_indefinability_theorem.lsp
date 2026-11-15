;; Statement-only formalization of thousand-theorems corpus artifact Q574902,
;; "Tarski's indefinability theorem": no unary formula of first-order
;; arithmetic defines standard-model truth for every arithmetic sentence when
;; applied to that sentence's Gödel numeral. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Terms and formulas give a concrete presentation of the ordered-semiring
;; language used by the source. Variables are natural numbers. The only data
;; represented by finite lists are finite syntax trees and environments;
;; quantifiers below range over all ACL2 natural numbers.

(mutual-recursion
 (defun q574902-term-p (term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((atom term)
     (or (equal term :zero)
         (equal term :one)))
    ((equal (car term) :var)
     (and
      (true-listp term)
      (equal (len term) 2)
      (natp (cadr term))))
    ((or (equal (car term) :add)
         (equal (car term) :multiply))
     (and
      (true-listp term)
      (equal (len term) 3)
      (q574902-term-p (cadr term))
      (q574902-term-p (caddr term))))
    (t nil)))

 (defun q574902-formula-p (formula)
   (declare (xargs :measure (acl2-count formula)))
   (cond
    ((atom formula) nil)
    ((equal (car formula) :falsum)
     (and
      (true-listp formula)
      (equal (len formula) 1)))
    ((or (equal (car formula) :equal)
         (equal (car formula) :less))
     (and
      (true-listp formula)
      (equal (len formula) 3)
      (q574902-term-p (cadr formula))
      (q574902-term-p (caddr formula))))
    ((equal (car formula) :implies)
     (and
      (true-listp formula)
      (equal (len formula) 3)
      (q574902-formula-p (cadr formula))
      (q574902-formula-p (caddr formula))))
    ((equal (car formula) :forall)
     (and
      (true-listp formula)
      (equal (len formula) 3)
      (natp (cadr formula))
      (q574902-formula-p (caddr formula))))
    (t nil))))

;; A variable occurrence is admissible when it is bound or belongs to the
;; displayed finite list of permitted free-variable positions. Thus NIL gives
;; sentences and (LIST 0) gives exactly the source type Semisentence L 1:
;; formulas may use the single free position 0, but need not actually use it.

(mutual-recursion
 (defun q574902-term-variables-among-p
     (term permitted-free bound)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((atom term)
     (or (equal term :zero)
         (equal term :one)))
    ((equal (car term) :var)
     (or
      (member-equal (cadr term) permitted-free)
      (member-equal (cadr term) bound)))
    ((or (equal (car term) :add)
         (equal (car term) :multiply))
     (and
      (q574902-term-variables-among-p
       (cadr term) permitted-free bound)
      (q574902-term-variables-among-p
       (caddr term) permitted-free bound)))
    (t nil)))

 (defun q574902-formula-variables-among-p
     (formula permitted-free bound)
   (declare (xargs :measure (acl2-count formula)))
   (cond
    ((atom formula) nil)
    ((equal (car formula) :falsum) t)
    ((or (equal (car formula) :equal)
         (equal (car formula) :less))
     (and
      (q574902-term-variables-among-p
       (cadr formula) permitted-free bound)
      (q574902-term-variables-among-p
       (caddr formula) permitted-free bound)))
    ((equal (car formula) :implies)
     (and
      (q574902-formula-variables-among-p
       (cadr formula) permitted-free bound)
      (q574902-formula-variables-among-p
       (caddr formula) permitted-free bound)))
    ((equal (car formula) :forall)
     (q574902-formula-variables-among-p
      (caddr formula)
      permitted-free
      (cons (cadr formula) bound)))
    (t nil))))

(defun q574902-sentence-p (formula)
  (and
   (q574902-formula-p formula)
   (q574902-formula-variables-among-p
    formula nil nil)))

(defun q574902-unary-semisentence-p (formula)
  (and
   (q574902-formula-p formula)
   (q574902-formula-variables-among-p
    formula (list 0) nil)))

;; Closed-term substitution is capture-free: a quantifier binding the
;; substituted variable blocks replacement, while other binders cannot
;; capture any variable of the closed Gödel numeral.

(mutual-recursion
 (defun q574902-substitute-term
     (term variable replacement)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((atom term) term)
    ((equal (car term) :var)
     (if (equal (cadr term) variable)
         replacement
       term))
    ((equal (car term) :add)
     (list
      :add
      (q574902-substitute-term
       (cadr term) variable replacement)
      (q574902-substitute-term
       (caddr term) variable replacement)))
    ((equal (car term) :multiply)
     (list
      :multiply
      (q574902-substitute-term
       (cadr term) variable replacement)
      (q574902-substitute-term
       (caddr term) variable replacement)))
    (t term)))

 (defun q574902-substitute-formula
     (formula variable replacement)
   (declare (xargs :measure (acl2-count formula)))
   (cond
    ((atom formula) formula)
    ((equal (car formula) :equal)
     (list
      :equal
      (q574902-substitute-term
       (cadr formula) variable replacement)
      (q574902-substitute-term
       (caddr formula) variable replacement)))
    ((equal (car formula) :less)
     (list
      :less
      (q574902-substitute-term
       (cadr formula) variable replacement)
      (q574902-substitute-term
       (caddr formula) variable replacement)))
    ((equal (car formula) :falsum)
     formula)
    ((equal (car formula) :implies)
     (list
      :implies
      (q574902-substitute-formula
       (cadr formula) variable replacement)
      (q574902-substitute-formula
       (caddr formula) variable replacement)))
    ((equal (car formula) :forall)
     (if (equal (cadr formula) variable)
         formula
       (list
        :forall
        (cadr formula)
        (q574902-substitute-formula
         (caddr formula) variable replacement))))
    (t formula))))

(defun q574902-numeral (number)
  (declare (xargs :measure (nfix number)))
  (if (zp number)
      :zero
    (list
     :add
     :one
     (q574902-numeral (- number 1)))))

;; Cantor pairing gives an injective, unbounded Gödel numbering of all terms
;; and formulas in this concrete syntax. Distinct constructor tags remain
;; distinct because the pairing function is injective in both coordinates.

(defun q574902-pair (left right)
  (let* ((left (nfix left))
         (right (nfix right))
         (sum (+ left right)))
    (+ right (floor (* sum (+ sum 1)) 2))))

(mutual-recursion
 (defun q574902-term-code (term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((equal term :zero)
     (q574902-pair 0 0))
    ((equal term :one)
     (q574902-pair 1 0))
    ((and (consp term)
          (equal (car term) :var))
     (q574902-pair 2 (nfix (cadr term))))
    ((and (consp term)
          (equal (car term) :add))
     (q574902-pair
      3
      (q574902-pair
       (q574902-term-code (cadr term))
       (q574902-term-code (caddr term)))))
    ((and (consp term)
          (equal (car term) :multiply))
     (q574902-pair
      4
      (q574902-pair
       (q574902-term-code (cadr term))
       (q574902-term-code (caddr term)))))
    (t (q574902-pair 5 0))))

 (defun q574902-formula-code (formula)
   (declare (xargs :measure (acl2-count formula)))
   (cond
    ((and (consp formula)
          (equal (car formula) :falsum))
     (q574902-pair 10 0))
    ((equal (car formula) :equal)
     (q574902-pair
      11
      (q574902-pair
       (q574902-term-code (cadr formula))
       (q574902-term-code (caddr formula)))))
    ((equal (car formula) :less)
     (q574902-pair
      12
      (q574902-pair
       (q574902-term-code (cadr formula))
       (q574902-term-code (caddr formula)))))
    ((equal (car formula) :implies)
     (q574902-pair
      13
      (q574902-pair
       (q574902-formula-code (cadr formula))
       (q574902-formula-code (caddr formula)))))
    ((equal (car formula) :forall)
     (q574902-pair
      14
      (q574902-pair
       (nfix (cadr formula))
       (q574902-formula-code (caddr formula)))))
    (t (q574902-pair 15 0)))))

;; Standard-natural-number term evaluation is executable. Environments are
;; association lists; closed formulas are independent of any default values.

(defun q574902-environment-lookup (variable environment)
  (nfix (cdr (assoc-equal variable environment))))

(defun q574902-environment-update
    (variable value environment)
  (acons variable (nfix value) environment))

(defun q574902-term-value (term environment)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ((equal term :zero) 0)
   ((equal term :one) 1)
   ((and (consp term)
         (equal (car term) :var))
    (q574902-environment-lookup
     (cadr term) environment))
   ((and (consp term)
         (equal (car term) :add))
    (+ (q574902-term-value (cadr term) environment)
       (q574902-term-value (caddr term) environment)))
   ((and (consp term)
         (equal (car term) :multiply))
    (* (q574902-term-value (cadr term) environment)
       (q574902-term-value (caddr term) environment)))
   (t 0)))

;; This conservative interface is constrained below by every Tarskian
;; recursion clause for the fixed standard model of arithmetic. Those clauses
;; uniquely determine satisfaction on well-formed formulas.

(defstub q574902-satisfies
  (environment formula)
  t)

(defun q574902-satisfies-p (environment formula)
  (if (q574902-satisfies environment formula)
      t
    nil))

(defun-sk q574902-all-naturals-satisfy-p
    (environment variable body)
  (forall (value)
    (implies
     (natp value)
     (q574902-satisfies-p
      (q574902-environment-update
       variable value environment)
      body))))

(defun-sk q574902-equality-semantics-p ()
  (forall (environment left right)
    (implies
     (and
      (q574902-term-p left)
      (q574902-term-p right))
     (equal
      (q574902-satisfies-p
       environment (list :equal left right))
      (equal
       (q574902-term-value left environment)
       (q574902-term-value right environment))))))

(defun-sk q574902-order-semantics-p ()
  (forall (environment left right)
    (implies
     (and
      (q574902-term-p left)
      (q574902-term-p right))
     (equal
      (q574902-satisfies-p
       environment (list :less left right))
      (if
       (< (q574902-term-value left environment)
          (q574902-term-value right environment))
       t
       nil)))))

(defun-sk q574902-falsum-semantics-p ()
  (forall (environment)
    (not
     (q574902-satisfies-p
      environment (list :falsum)))))

(defun-sk q574902-implication-semantics-p ()
  (forall (environment left right)
    (implies
     (and
      (q574902-formula-p left)
      (q574902-formula-p right))
     (equal
      (q574902-satisfies-p
       environment (list :implies left right))
      (if
       (q574902-satisfies-p environment left)
       (q574902-satisfies-p environment right)
       t)))))

(defun-sk q574902-universal-semantics-p ()
  (forall (environment variable body)
    (implies
     (and
      (natp variable)
      (q574902-formula-p body))
     (equal
      (q574902-satisfies-p
       environment (list :forall variable body))
      (if
       (q574902-all-naturals-satisfy-p
        environment variable body)
       t
       nil)))))

(defun q574902-standard-natural-semantics-p ()
  (and
   (q574902-equality-semantics-p)
   (q574902-order-semantics-p)
   (q574902-falsum-semantics-p)
   (q574902-implication-semantics-p)
   (q574902-universal-semantics-p)))

;; Agreement has the source quantifier order: one internally existential
;; unary formula must work uniformly for every closed arithmetic sentence.

(defun-sk q574902-truth-agreement-p (truth-formula)
  (forall (sentence)
    (implies
     (q574902-sentence-p sentence)
     (iff
      (q574902-satisfies-p nil sentence)
      (q574902-satisfies-p
       nil
       (q574902-substitute-formula
        truth-formula
        0
        (q574902-numeral
         (q574902-formula-code sentence))))))))

(defun-sk q574902-tarski-predicate-exists-p ()
  (exists (truth-formula)
    (and
     (q574902-unary-semisentence-p truth-formula)
     (q574902-truth-agreement-p truth-formula))))

(defun thousand-theorems-q574902-tarski-s-indefinability-statement ()
  (implies
   (q574902-standard-natural-semantics-p)
   (not
    (q574902-tarski-predicate-exists-p))))

(value-triple :itpeval-statement-checked)
:q
