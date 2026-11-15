;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/defunctionalization_ReductionSemantics_reduceqtvc: preservation of
;; direct integer evaluation when a redex is replaced by an expression with
;; the same value inside a reduction context. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Expressions are represented bijectively by the finite constructor records
;; (:RSR-CTE integer) and (:RSR-SUB expression expression).

(defun rsr-cte-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 2)
   (equal (car expression) :rsr-cte)))

(defun rsr-sub-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 3)
   (equal (car expression) :rsr-sub)))

(defun rsr-expression-p (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rsr-cte-shape-p expression)
    (integerp (cadr expression)))
   ((rsr-sub-shape-p expression)
    (and
     (rsr-expression-p (cadr expression))
     (rsr-expression-p (caddr expression))))
   (t nil)))

(defun rsr-cte (integer)
  (list :rsr-cte integer))

(defun rsr-sub (left right)
  (list :rsr-sub left right))

(defun rsr-cte-number (expression)
  (cadr expression))

(defun rsr-sub-left (expression)
  (cadr expression))

(defun rsr-sub-right (expression)
  (caddr expression))

;; This is the source DirectSem.eval_0 definition on valid expressions.

(defun rsr-eval-0 (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rsr-cte-shape-p expression)
    (rsr-cte-number expression))
   ((rsr-sub-shape-p expression)
    (-
     (rsr-eval-0 (rsr-sub-left expression))
     (rsr-eval-0 (rsr-sub-right expression))))
   (t 0)))

;; Reduction contexts are represented bijectively by the finite constructor
;; records (:RSR-EMPTY), (:RSR-LEFT context expression), and
;; (:RSR-RIGHT integer context).

(defun rsr-empty-shape-p (context)
  (equal context (list :rsr-empty)))

(defun rsr-left-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rsr-left)))

(defun rsr-right-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rsr-right)))

(defun rsr-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rsr-empty-shape-p context)
    t)
   ((rsr-left-shape-p context)
    (and
     (rsr-context-p (cadr context))
     (rsr-expression-p (caddr context))))
   ((rsr-right-shape-p context)
    (and
     (integerp (cadr context))
     (rsr-context-p (caddr context))))
   (t nil)))

(defun rsr-empty ()
  (list :rsr-empty))

(defun rsr-left (context expression)
  (list :rsr-left context expression))

(defun rsr-right (integer context)
  (list :rsr-right integer context))

(defun rsr-left-context (context)
  (cadr context))

(defun rsr-left-expression (context)
  (caddr context))

(defun rsr-right-number (context)
  (cadr context))

(defun rsr-right-context (context)
  (caddr context))

;; This is the source reduction-context recomposition definition on valid
;; contexts and expressions.

(defun rsr-recompose (context expression)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rsr-empty-shape-p context)
    expression)
   ((rsr-left-shape-p context)
    (rsr-recompose
     (rsr-left-context context)
     (rsr-sub
      expression
      (rsr-left-expression context))))
   ((rsr-right-shape-p context)
    (rsr-recompose
     (rsr-right-context context)
     (rsr-sub
      (rsr-cte (rsr-right-number context))
      expression)))
   (t expression)))

;; This is exactly the source redex predicate: a subtraction whose two
;; immediate operands are integer constants.

(defun rsr-redex-p (expression)
  (and
   (rsr-sub-shape-p expression)
   (rsr-cte-shape-p (rsr-sub-left expression))
   (rsr-cte-shape-p (rsr-sub-right expression))))

;; Preserve the source's existentially quantified replacement expression
;; inside the antecedent of the result implication.

(defun-sk rsr-replacement-exists-p
    (context redex result)
  (exists (replacement)
    (and
     (rsr-expression-p replacement)
     (equal
      (rsr-eval-0 replacement)
      (rsr-eval-0 redex))
     (equal
      result
      (rsr-recompose context replacement)))))

;; Preserve the source's universal quantifier over every expression result.

(defun-sk rsr-all-results-p
    (context redex whole-expression)
  (forall (result)
    (implies
     (rsr-expression-p result)
     (implies
      (rsr-replacement-exists-p
       context redex result)
      (equal
       (rsr-eval-0 result)
       (rsr-eval-0 whole-expression))))))

(defun
  ntp4vc-pearl-defunctionalization-reductionsemantics-reduceqtvc-statement
  (context redex whole-expression)
  (implies
   (and
    (rsr-context-p context)
    (rsr-expression-p redex)
    (rsr-expression-p whole-expression)
    (equal
     (rsr-recompose context redex)
     whole-expression)
    (rsr-redex-p redex))
   (and
    (rsr-redex-p redex)
    (rsr-all-results-p
     context redex whole-expression))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
