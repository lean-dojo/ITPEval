;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/defunctionalization_ReductionSemantics_eval_1qtvc: structural measure
;; decrease and direct-evaluation preservation for integer subtraction
;; expressions under reduction-context recomposition. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Expressions are exact finite constructor records:
;; (:RSE1-CTE integer) and (:RSE1-SUB expression expression).

(defun rse1-cte-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 2)
   (equal (car expression) :rse1-cte)))

(defun rse1-sub-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 3)
   (equal (car expression) :rse1-sub)))

(defun rse1-expression-p (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rse1-cte-shape-p expression)
    (integerp (cadr expression)))
   ((rse1-sub-shape-p expression)
    (and
     (rse1-expression-p (cadr expression))
     (rse1-expression-p (caddr expression))))
   (t nil)))

(defun rse1-cte (integer)
  (list :rse1-cte integer))

(defun rse1-sub (left right)
  (list :rse1-sub left right))

(defun rse1-cte-number (expression)
  (cadr expression))

(defun rse1-sub-left (expression)
  (cadr expression))

(defun rse1-sub-right (expression)
  (caddr expression))

;; These are the source DirectSem.eval_0 and Defunctionalization.size_e
;; definitions on valid expressions.

(defun rse1-eval-0 (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rse1-cte-shape-p expression)
    (rse1-cte-number expression))
   ((rse1-sub-shape-p expression)
    (-
     (rse1-eval-0 (rse1-sub-left expression))
     (rse1-eval-0 (rse1-sub-right expression))))
   (t 0)))

(defun rse1-size-e (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rse1-cte-shape-p expression)
    1)
   ((rse1-sub-shape-p expression)
    (+
     3
     (rse1-size-e (rse1-sub-left expression))
     (rse1-size-e (rse1-sub-right expression))))
   (t 0)))

;; Reduction contexts are exact finite constructor records:
;; (:RSE1-EMPTY), (:RSE1-LEFT context expression), and
;; (:RSE1-RIGHT integer context).

(defun rse1-empty-shape-p (context)
  (equal context (list :rse1-empty)))

(defun rse1-left-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rse1-left)))

(defun rse1-right-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rse1-right)))

(defun rse1-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rse1-empty-shape-p context)
    t)
   ((rse1-left-shape-p context)
    (and
     (rse1-context-p (cadr context))
     (rse1-expression-p (caddr context))))
   ((rse1-right-shape-p context)
    (and
     (integerp (cadr context))
     (rse1-context-p (caddr context))))
   (t nil)))

(defun rse1-empty ()
  (list :rse1-empty))

(defun rse1-left (context expression)
  (list :rse1-left context expression))

(defun rse1-right (integer context)
  (list :rse1-right integer context))

(defun rse1-left-context (context)
  (cadr context))

(defun rse1-left-expression (context)
  (caddr context))

(defun rse1-right-number (context)
  (cadr context))

(defun rse1-right-context (context)
  (caddr context))

;; These are the source reduction-semantics definitions.

(defun rse1-recompose (context expression)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rse1-empty-shape-p context)
    expression)
   ((rse1-left-shape-p context)
    (rse1-recompose
     (rse1-left-context context)
     (rse1-sub
      expression
      (rse1-left-expression context))))
   ((rse1-right-shape-p context)
    (rse1-recompose
     (rse1-right-context context)
     (rse1-sub
      (rse1-cte (rse1-right-number context))
      expression)))
   (t expression)))

(defun rse1-redex-p (expression)
  (and
   (rse1-sub-shape-p expression)
   (rse1-cte-shape-p (rse1-sub-left expression))
   (rse1-cte-shape-p (rse1-sub-right expression))))

(defun rse1-value-p (expression)
  (rse1-cte-shape-p expression))

(defun rse1-empty-context-p (context)
  (rse1-empty-shape-p context))

(defun rse1-size-c (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rse1-empty-shape-p context)
    0)
   ((rse1-left-shape-p context)
    (+
     2
     (rse1-size-c (rse1-left-context context))
     (rse1-size-e (rse1-left-expression context))))
   ((rse1-right-shape-p context)
    (+
     1
     (rse1-size-c (rse1-right-context context))))
   (t 0)))

;; Exact constructor split of the source's structural-decrease conjunct.

(defun rse1-size-obligation-p (expression context)
  (let ((whole-measure
         (*
          2
          (+
           (rse1-size-c context)
           (rse1-size-e expression)))))
    (cond
     ((rse1-cte-shape-p expression)
      (and
       (<= 0 whole-measure)
       (<
        (+
         1
         (* 2 (rse1-size-c context)))
        whole-measure)))
     ((rse1-sub-shape-p expression)
      (and
       (<= 0 whole-measure)
       (<
        (*
         2
         (+
          (rse1-size-c
           (rse1-left
            context
            (rse1-sub-right expression)))
          (rse1-size-e
           (rse1-sub-left expression))))
        whole-measure)))
     (t nil))))

;; Preserve the source's universal quantifier over every integer result.

(defun rse1-result-premise-p
    (expression context result)
  (cond
   ((rse1-cte-shape-p expression)
    (equal
     result
     (rse1-eval-0
      (rse1-recompose context expression))))
   ((rse1-sub-shape-p expression)
    (equal
     result
     (rse1-eval-0
      (rse1-recompose
       (rse1-left
        context
        (rse1-sub-right expression))
       (rse1-sub-left expression)))))
   (t nil)))

(defun-sk rse1-all-results-p (expression context)
  (forall (result)
    (implies
     (integerp result)
     (implies
      (rse1-result-premise-p
       expression context result)
      (equal
       result
       (rse1-eval-0
        (rse1-recompose context expression)))))))

(defun
  ntp4vc-pearl-defunctionalization-reductionsemantics-eval-1qtvc-statement
  (expression context)
  (implies
   (and
    (rse1-expression-p expression)
    (rse1-context-p context))
   (and
    (rse1-size-obligation-p expression context)
    (rse1-all-results-p expression context))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
