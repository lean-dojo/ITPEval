;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/defunctionalization_ReductionSemantics_eval_2qtvc: structural measure
;; decrease and direct-evaluation preservation after processing an integer
;; value in a subtraction reduction context. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Expressions are exact finite constructor records:
;; (:RSE2-CTE integer) and (:RSE2-SUB expression expression).

(defun rse2-cte-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 2)
   (equal (car expression) :rse2-cte)))

(defun rse2-sub-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 3)
   (equal (car expression) :rse2-sub)))

(defun rse2-expression-p (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rse2-cte-shape-p expression)
    (integerp (cadr expression)))
   ((rse2-sub-shape-p expression)
    (and
     (rse2-expression-p (cadr expression))
     (rse2-expression-p (caddr expression))))
   (t nil)))

(defun rse2-cte (integer)
  (list :rse2-cte integer))

(defun rse2-sub (left right)
  (list :rse2-sub left right))

(defun rse2-cte-number (expression)
  (cadr expression))

(defun rse2-sub-left (expression)
  (cadr expression))

(defun rse2-sub-right (expression)
  (caddr expression))

;; These are the source DirectSem.eval_0 and Defunctionalization.size_e
;; definitions on valid expressions.

(defun rse2-eval-0 (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rse2-cte-shape-p expression)
    (rse2-cte-number expression))
   ((rse2-sub-shape-p expression)
    (-
     (rse2-eval-0 (rse2-sub-left expression))
     (rse2-eval-0 (rse2-sub-right expression))))
   (t 0)))

(defun rse2-size-e (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rse2-cte-shape-p expression)
    1)
   ((rse2-sub-shape-p expression)
    (+
     3
     (rse2-size-e (rse2-sub-left expression))
     (rse2-size-e (rse2-sub-right expression))))
   (t 0)))

;; Reduction contexts are exact finite constructor records:
;; (:RSE2-EMPTY), (:RSE2-LEFT context expression), and
;; (:RSE2-RIGHT integer context).

(defun rse2-empty-shape-p (context)
  (equal context (list :rse2-empty)))

(defun rse2-left-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rse2-left)))

(defun rse2-right-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rse2-right)))

(defun rse2-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rse2-empty-shape-p context)
    t)
   ((rse2-left-shape-p context)
    (and
     (rse2-context-p (cadr context))
     (rse2-expression-p (caddr context))))
   ((rse2-right-shape-p context)
    (and
     (integerp (cadr context))
     (rse2-context-p (caddr context))))
   (t nil)))

(defun rse2-empty ()
  (list :rse2-empty))

(defun rse2-left (context expression)
  (list :rse2-left context expression))

(defun rse2-right (integer context)
  (list :rse2-right integer context))

(defun rse2-left-context (context)
  (cadr context))

(defun rse2-left-expression (context)
  (caddr context))

(defun rse2-right-number (context)
  (cadr context))

(defun rse2-right-context (context)
  (caddr context))

;; These are the source reduction-semantics definitions.

(defun rse2-recompose (context expression)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rse2-empty-shape-p context)
    expression)
   ((rse2-left-shape-p context)
    (rse2-recompose
     (rse2-left-context context)
     (rse2-sub
      expression
      (rse2-left-expression context))))
   ((rse2-right-shape-p context)
    (rse2-recompose
     (rse2-right-context context)
     (rse2-sub
      (rse2-cte (rse2-right-number context))
      expression)))
   (t expression)))

(defun rse2-redex-p (expression)
  (and
   (rse2-sub-shape-p expression)
   (rse2-cte-shape-p (rse2-sub-left expression))
   (rse2-cte-shape-p (rse2-sub-right expression))))

(defun rse2-value-p (expression)
  (rse2-cte-shape-p expression))

(defun rse2-empty-context-p (context)
  (rse2-empty-shape-p context))

(defun rse2-size-c (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rse2-empty-shape-p context)
    0)
   ((rse2-left-shape-p context)
    (+
     2
     (rse2-size-c (rse2-left-context context))
     (rse2-size-e (rse2-left-expression context))))
   ((rse2-right-shape-p context)
    (+
     1
     (rse2-size-c (rse2-right-context context))))
   (t 0)))

;; Exact constructor split of the source's structural-decrease conjunct.

(defun rse2-size-obligation-p (context number)
  (let ((whole-bound
         (+
          1
          (* 2 (rse2-size-c context)))))
    (cond
     ((rse2-empty-shape-p context)
      t)
     ((rse2-left-shape-p context)
      (and
       (<= 0 whole-bound)
       (<
        (*
         2
         (+
          (rse2-size-c
           (rse2-right
            number
            (rse2-left-context context)))
          (rse2-size-e
           (rse2-left-expression context))))
        whole-bound)))
     ((rse2-right-shape-p context)
      (and
       (<= 0 whole-bound)
       (<
        (*
         2
         (+
          (rse2-size-c
           (rse2-right-context context))
          (rse2-size-e
           (rse2-cte
            (-
             (rse2-right-number context)
             number)))))
        whole-bound)))
     (t nil))))

;; Preserve the source's branch-specific premise for every integer result.

(defun rse2-result-premise-p
    (context number result)
  (cond
   ((rse2-empty-shape-p context)
    (equal result number))
   ((rse2-left-shape-p context)
    (equal
     result
     (rse2-eval-0
      (rse2-recompose
       (rse2-right
        number
        (rse2-left-context context))
       (rse2-left-expression context)))))
   ((rse2-right-shape-p context)
    (equal
     result
     (rse2-eval-0
      (rse2-recompose
       (rse2-right-context context)
       (rse2-cte
        (-
         (rse2-right-number context)
         number))))))
   (t nil)))

(defun-sk rse2-all-results-p (context number)
  (forall (result)
    (implies
     (integerp result)
     (implies
      (rse2-result-premise-p
       context number result)
      (equal
       result
       (rse2-eval-0
        (rse2-recompose
         context
         (rse2-cte number))))))))

(defun
  ntp4vc-pearl-defunctionalization-reductionsemantics-eval-2qtvc-statement
  (context number)
  (implies
   (and
    (rse2-context-p context)
    (integerp number))
   (and
    (rse2-size-obligation-p context number)
    (rse2-all-results-p context number))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
