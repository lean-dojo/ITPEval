;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/defunctionalization_RWithError_eval_1qtvc: structural measure
;; decrease and semantic preservation for an error-aware subtraction
;; evaluator under expression-context recomposition. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Expressions are exact finite constructor records:
;; (:RWE1-CTE integer) and (:RWE1-SUB expression expression).

(defun rwe1-cte-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 2)
   (equal (car expression) :rwe1-cte)))

(defun rwe1-sub-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 3)
   (equal (car expression) :rwe1-sub)))

(defun rwe1-expression-p (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rwe1-cte-shape-p expression)
    (integerp (cadr expression)))
   ((rwe1-sub-shape-p expression)
    (and
     (rwe1-expression-p (cadr expression))
     (rwe1-expression-p (caddr expression))))
   (t nil)))

(defun rwe1-cte (integer)
  (list :rwe1-cte integer))

(defun rwe1-sub (left right)
  (list :rwe1-sub left right))

(defun rwe1-cte-number (expression)
  (cadr expression))

(defun rwe1-sub-left (expression)
  (cadr expression))

(defun rwe1-sub-right (expression)
  (caddr expression))

(defun rwe1-size-e (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rwe1-cte-shape-p expression)
    1)
   ((rwe1-sub-shape-p expression)
    (+
     3
     (rwe1-size-e (rwe1-sub-left expression))
     (rwe1-size-e (rwe1-sub-right expression))))
   (t 0)))

;; Contexts are exact finite constructor records:
;; (:RWE1-EMPTY), (:RWE1-LEFT context expression), and
;; (:RWE1-RIGHT integer context).

(defun rwe1-empty-shape-p (context)
  (equal context (list :rwe1-empty)))

(defun rwe1-left-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rwe1-left)))

(defun rwe1-right-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rwe1-right)))

(defun rwe1-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rwe1-empty-shape-p context)
    t)
   ((rwe1-left-shape-p context)
    (and
     (rwe1-context-p (cadr context))
     (rwe1-expression-p (caddr context))))
   ((rwe1-right-shape-p context)
    (and
     (integerp (cadr context))
     (rwe1-context-p (caddr context))))
   (t nil)))

(defun rwe1-empty ()
  (list :rwe1-empty))

(defun rwe1-left (context expression)
  (list :rwe1-left context expression))

(defun rwe1-right (integer context)
  (list :rwe1-right integer context))

(defun rwe1-left-context (context)
  (cadr context))

(defun rwe1-left-expression (context)
  (caddr context))

(defun rwe1-right-number (context)
  (cadr context))

(defun rwe1-right-context (context)
  (caddr context))

(defun rwe1-size-c (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rwe1-empty-shape-p context)
    0)
   ((rwe1-left-shape-p context)
    (+
     2
     (rwe1-size-c (rwe1-left-context context))
     (rwe1-size-e (rwe1-left-expression context))))
   ((rwe1-right-shape-p context)
    (+
     1
     (rwe1-size-c (rwe1-right-context context))))
   (t 0)))

(defun rwe1-recompose (context expression)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rwe1-empty-shape-p context)
    expression)
   ((rwe1-left-shape-p context)
    (rwe1-recompose
     (rwe1-left-context context)
     (rwe1-sub
      expression
      (rwe1-left-expression context))))
   ((rwe1-right-shape-p context)
    (rwe1-recompose
     (rwe1-right-context context)
     (rwe1-sub
      (rwe1-cte (rwe1-right-number context))
      expression)))
   (t expression)))

;; Error-aware values are exact records (:RWE1-VNUM integer) and
;; (:RWE1-UNDERFLOW).

(defun rwe1-vnum-shape-p (value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (equal (car value) :rwe1-vnum)))

(defun rwe1-underflow-p (value)
  (equal value (list :rwe1-underflow)))

(defun rwe1-value-p (value)
  (or
   (and
    (rwe1-vnum-shape-p value)
    (integerp (cadr value)))
   (rwe1-underflow-p value)))

(defun rwe1-vnum (integer)
  (list :rwe1-vnum integer))

(defun rwe1-underflow ()
  (list :rwe1-underflow))

(defun rwe1-vnum-number (value)
  (cadr value))

;; This is the source SemWithError.eval_0 definition.

(defun rwe1-eval-0 (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rwe1-cte-shape-p expression)
    (if (<= 0 (rwe1-cte-number expression))
        (rwe1-vnum (rwe1-cte-number expression))
      (rwe1-underflow)))
   ((rwe1-sub-shape-p expression)
    (let ((left-value
           (rwe1-eval-0
            (rwe1-sub-left expression))))
      (if (rwe1-underflow-p left-value)
          (rwe1-underflow)
        (let ((right-value
               (rwe1-eval-0
                (rwe1-sub-right expression))))
          (if (rwe1-underflow-p right-value)
              (rwe1-underflow)
            (if
             (<=
              (rwe1-vnum-number right-value)
              (rwe1-vnum-number left-value))
             (rwe1-vnum
              (-
               (rwe1-vnum-number left-value)
               (rwe1-vnum-number right-value)))
             (rwe1-underflow)))))))
   (t (rwe1-underflow))))

;; Exact constructor split for the source's structural-decrease conjunct.

(defun rwe1-size-obligation-p (expression context)
  (let ((whole-measure
         (*
          2
          (+
           (rwe1-size-c context)
           (rwe1-size-e expression)))))
    (cond
     ((rwe1-cte-shape-p expression)
      (implies
       (<= 0 (rwe1-cte-number expression))
       (and
        (<= 0 whole-measure)
        (<
         (+
          1
          (* 2 (rwe1-size-c context)))
         whole-measure)
        (<= 0 (rwe1-cte-number expression)))))
     ((rwe1-sub-shape-p expression)
      (and
       (<= 0 whole-measure)
       (<
        (*
         2
         (+
          (rwe1-size-c
           (rwe1-left
            context
            (rwe1-sub-right expression)))
          (rwe1-size-e
           (rwe1-sub-left expression))))
        whole-measure)))
     (t nil))))

;; Preserve the source's universal quantifier over every error-aware result.

(defun rwe1-result-premise-p
    (expression context result)
  (cond
   ((rwe1-cte-shape-p expression)
    (if (<= 0 (rwe1-cte-number expression))
        (equal
         result
         (rwe1-eval-0
          (rwe1-recompose context expression)))
      (equal result (rwe1-underflow))))
   ((rwe1-sub-shape-p expression)
    (equal
     result
     (rwe1-eval-0
      (rwe1-recompose
       (rwe1-left
        context
        (rwe1-sub-right expression))
       (rwe1-sub-left expression)))))
   (t nil)))

(defun-sk rwe1-all-results-p (expression context)
  (forall (result)
    (implies
     (rwe1-value-p result)
     (implies
      (rwe1-result-premise-p
       expression context result)
      (equal
       result
       (rwe1-eval-0
        (rwe1-recompose context expression)))))))

(defun
  ntp4vc-pearl-defunctionalization-rwitherror-eval-1qtvc-statement
  (expression context)
  (implies
   (and
    (rwe1-expression-p expression)
    (rwe1-context-p context))
   (and
    (rwe1-size-obligation-p expression context)
    (rwe1-all-results-p expression context))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
