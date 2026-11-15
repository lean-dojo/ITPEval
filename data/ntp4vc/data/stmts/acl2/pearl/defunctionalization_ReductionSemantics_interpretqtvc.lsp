;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/defunctionalization_ReductionSemantics_interpretqtvc: direct
;; evaluation of an integer-subtraction expression is unchanged when the
;; expression is recomposed in the empty reduction context. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Expressions are represented bijectively by the finite constructor records
;; (:RSI-CTE integer) and (:RSI-SUB expression expression).

(defun rsi-cte-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 2)
   (equal (car expression) :rsi-cte)))

(defun rsi-sub-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 3)
   (equal (car expression) :rsi-sub)))

(defun rsi-expression-p (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rsi-cte-shape-p expression)
    (integerp (cadr expression)))
   ((rsi-sub-shape-p expression)
    (and
     (rsi-expression-p (cadr expression))
     (rsi-expression-p (caddr expression))))
   (t nil)))

(defun rsi-cte (integer)
  (list :rsi-cte integer))

(defun rsi-sub (left right)
  (list :rsi-sub left right))

(defun rsi-cte-number (expression)
  (cadr expression))

(defun rsi-sub-left (expression)
  (cadr expression))

(defun rsi-sub-right (expression)
  (caddr expression))

;; This is the source DirectSem.eval_0 definition on valid expressions.

(defun rsi-eval-0 (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rsi-cte-shape-p expression)
    (rsi-cte-number expression))
   ((rsi-sub-shape-p expression)
    (-
     (rsi-eval-0 (rsi-sub-left expression))
     (rsi-eval-0 (rsi-sub-right expression))))
   (t 0)))

;; Reduction contexts are represented bijectively by the finite constructor
;; records (:RSI-EMPTY), (:RSI-LEFT context expression), and
;; (:RSI-RIGHT integer context).

(defun rsi-empty-shape-p (context)
  (equal context (list :rsi-empty)))

(defun rsi-left-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rsi-left)))

(defun rsi-right-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rsi-right)))

(defun rsi-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rsi-empty-shape-p context)
    t)
   ((rsi-left-shape-p context)
    (and
     (rsi-context-p (cadr context))
     (rsi-expression-p (caddr context))))
   ((rsi-right-shape-p context)
    (and
     (integerp (cadr context))
     (rsi-context-p (caddr context))))
   (t nil)))

(defun rsi-empty ()
  (list :rsi-empty))

(defun rsi-left (context expression)
  (list :rsi-left context expression))

(defun rsi-right (integer context)
  (list :rsi-right integer context))

(defun rsi-left-context (context)
  (cadr context))

(defun rsi-left-expression (context)
  (caddr context))

(defun rsi-right-number (context)
  (cadr context))

(defun rsi-right-context (context)
  (caddr context))

;; This is the source reduction-context recomposition definition on valid
;; contexts and expressions.

(defun rsi-recompose (context expression)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rsi-empty-shape-p context)
    expression)
   ((rsi-left-shape-p context)
    (rsi-recompose
     (rsi-left-context context)
     (rsi-sub
      expression
      (rsi-left-expression context))))
   ((rsi-right-shape-p context)
    (rsi-recompose
     (rsi-right-context context)
     (rsi-sub
      (rsi-cte (rsi-right-number context))
      expression)))
   (t expression)))

(defun
  ntp4vc-pearl-defunctionalization-reductionsemantics-interpretqtvc-statement
  (p)
  (implies
   (rsi-expression-p p)
   (equal
    (rsi-eval-0 (rsi-recompose (rsi-empty) p))
    (rsi-eval-0 p))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
