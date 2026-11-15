;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/defunctionalization_RWithError_eval_2qtvc: structural measure
;; decrease and semantic consistency for an underflow-aware subtraction
;; evaluator under expression-context recomposition. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Expressions are exact finite constructor records:
;; (:RWE2-CTE integer) and (:RWE2-SUB expression expression).

(defun rwe2-cte-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 2)
   (equal (car expression) :rwe2-cte)))

(defun rwe2-sub-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 3)
   (equal (car expression) :rwe2-sub)))

(defun rwe2-expression-p (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rwe2-cte-shape-p expression)
    (integerp (cadr expression)))
   ((rwe2-sub-shape-p expression)
    (and
     (rwe2-expression-p (cadr expression))
     (rwe2-expression-p (caddr expression))))
   (t nil)))

(defun rwe2-cte (integer)
  (list :rwe2-cte integer))

(defun rwe2-sub (left right)
  (list :rwe2-sub left right))

(defun rwe2-cte-number (expression)
  (cadr expression))

(defun rwe2-sub-left (expression)
  (cadr expression))

(defun rwe2-sub-right (expression)
  (caddr expression))

(defun rwe2-size-e (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rwe2-cte-shape-p expression)
    1)
   ((rwe2-sub-shape-p expression)
    (+
     3
     (rwe2-size-e (rwe2-sub-left expression))
     (rwe2-size-e (rwe2-sub-right expression))))
   (t 0)))

;; Contexts are exact finite constructor records:
;; (:RWE2-EMPTY), (:RWE2-LEFT context expression), and
;; (:RWE2-RIGHT integer context).

(defun rwe2-empty-shape-p (context)
  (equal context (list :rwe2-empty)))

(defun rwe2-left-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rwe2-left)))

(defun rwe2-right-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rwe2-right)))

(defun rwe2-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rwe2-empty-shape-p context)
    t)
   ((rwe2-left-shape-p context)
    (and
     (rwe2-context-p (cadr context))
     (rwe2-expression-p (caddr context))))
   ((rwe2-right-shape-p context)
    (and
     (integerp (cadr context))
     (rwe2-context-p (caddr context))))
   (t nil)))

(defun rwe2-empty ()
  (list :rwe2-empty))

(defun rwe2-left (context expression)
  (list :rwe2-left context expression))

(defun rwe2-right (integer context)
  (list :rwe2-right integer context))

(defun rwe2-left-context (context)
  (cadr context))

(defun rwe2-left-expression (context)
  (caddr context))

(defun rwe2-right-number (context)
  (cadr context))

(defun rwe2-right-context (context)
  (caddr context))

(defun rwe2-size-c (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rwe2-empty-shape-p context)
    0)
   ((rwe2-left-shape-p context)
    (+
     2
     (rwe2-size-c (rwe2-left-context context))
     (rwe2-size-e (rwe2-left-expression context))))
   ((rwe2-right-shape-p context)
    (+
     1
     (rwe2-size-c (rwe2-right-context context))))
   (t 0)))

(defun rwe2-recompose (context expression)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rwe2-empty-shape-p context)
    expression)
   ((rwe2-left-shape-p context)
    (rwe2-recompose
     (rwe2-left-context context)
     (rwe2-sub
      expression
      (rwe2-left-expression context))))
   ((rwe2-right-shape-p context)
    (rwe2-recompose
     (rwe2-right-context context)
     (rwe2-sub
      (rwe2-cte (rwe2-right-number context))
      expression)))
   (t expression)))

;; Error-aware values are exact records (:RWE2-VNUM integer) and
;; (:RWE2-UNDERFLOW).

(defun rwe2-vnum-shape-p (value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (equal (car value) :rwe2-vnum)))

(defun rwe2-underflow-p (value)
  (equal value (list :rwe2-underflow)))

(defun rwe2-value-p (value)
  (or
   (and
    (rwe2-vnum-shape-p value)
    (integerp (cadr value)))
   (rwe2-underflow-p value)))

(defun rwe2-vnum (integer)
  (list :rwe2-vnum integer))

(defun rwe2-underflow ()
  (list :rwe2-underflow))

(defun rwe2-vnum-number (value)
  (cadr value))

;; Exact recursive definition of the source SemWithError.eval_0.

(defun rwe2-eval-0 (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rwe2-cte-shape-p expression)
    (if (<= 0 (rwe2-cte-number expression))
        (rwe2-vnum (rwe2-cte-number expression))
      (rwe2-underflow)))
   ((rwe2-sub-shape-p expression)
    (let ((left-value
           (rwe2-eval-0
            (rwe2-sub-left expression))))
      (if (rwe2-underflow-p left-value)
          (rwe2-underflow)
        (let ((right-value
               (rwe2-eval-0
                (rwe2-sub-right expression))))
          (if (rwe2-underflow-p right-value)
              (rwe2-underflow)
            (if
             (<=
              (rwe2-vnum-number right-value)
              (rwe2-vnum-number left-value))
             (rwe2-vnum
              (-
               (rwe2-vnum-number left-value)
               (rwe2-vnum-number right-value)))
             (rwe2-underflow)))))))
   (t (rwe2-underflow))))

;; Exact constructor split for the source's first conjunct.

(defun rwe2-size-obligation-p (number context)
  (let ((whole-bound
         (+
          1
          (* 2 (rwe2-size-c context)))))
    (cond
     ((rwe2-empty-shape-p context)
      t)
     ((rwe2-left-shape-p context)
      (and
       (<= 0 whole-bound)
       (<
        (*
         2
         (+
          (rwe2-size-c
           (rwe2-right
            number
            (rwe2-left-context context)))
          (rwe2-size-e
           (rwe2-left-expression context))))
        whole-bound)))
     ((rwe2-right-shape-p context)
      (implies
       (<= number (rwe2-right-number context))
       (and
        (<= 0 whole-bound)
        (<
         (*
          2
          (+
           (rwe2-size-c
            (rwe2-right-context context))
           (rwe2-size-e
            (rwe2-cte
             (-
              (rwe2-right-number context)
              number)))))
         whole-bound))))
     (t nil))))

;; Exact matched antecedent of the universally quantified result implication.

(defun rwe2-result-premise-p
    (number context result)
  (cond
   ((rwe2-empty-shape-p context)
    (equal result (rwe2-vnum number)))
   ((rwe2-left-shape-p context)
    (equal
     result
     (rwe2-eval-0
      (rwe2-recompose
       (rwe2-right
        number
        (rwe2-left-context context))
       (rwe2-left-expression context)))))
   ((rwe2-right-shape-p context)
    (if
        (<= number (rwe2-right-number context))
        (equal
         result
         (rwe2-eval-0
          (rwe2-recompose
           (rwe2-right-context context)
           (rwe2-cte
            (-
             (rwe2-right-number context)
             number)))))
      (equal result (rwe2-underflow))))
   (t nil)))

(defun-sk rwe2-all-results-p (number context)
  (forall (result)
    (implies
     (rwe2-value-p result)
     (implies
      (rwe2-result-premise-p
       number context result)
      (equal
       result
       (rwe2-eval-0
        (rwe2-recompose
         context
         (rwe2-cte number))))))))

(defun
  ntp4vc-pearl-defunctionalization-rwitherror-eval-2qtvc-statement
  (number context)
  (implies
   (and
    (integerp number)
    (rwe2-context-p context)
    (<= 0 number))
   (and
    (rwe2-size-obligation-p number context)
    (rwe2-all-results-p number context))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
