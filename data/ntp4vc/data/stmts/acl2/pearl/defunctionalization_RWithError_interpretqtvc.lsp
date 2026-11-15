;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/defunctionalization_RWithError_interpretqtvc: the error-aware
;; evaluator is unchanged when an integer-subtraction expression is
;; recomposed in the empty context. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Expressions are represented bijectively by the finite constructor records
;; (:RWI-CTE integer) and (:RWI-SUB expression expression).

(defun rwi-cte-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 2)
   (equal (car expression) :rwi-cte)))

(defun rwi-sub-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 3)
   (equal (car expression) :rwi-sub)))

(defun rwi-expression-p (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rwi-cte-shape-p expression)
    (integerp (cadr expression)))
   ((rwi-sub-shape-p expression)
    (and
     (rwi-expression-p (cadr expression))
     (rwi-expression-p (caddr expression))))
   (t nil)))

(defun rwi-cte (integer)
  (list :rwi-cte integer))

(defun rwi-sub (left right)
  (list :rwi-sub left right))

(defun rwi-cte-number (expression)
  (cadr expression))

(defun rwi-sub-left (expression)
  (cadr expression))

(defun rwi-sub-right (expression)
  (caddr expression))

;; Error-aware values are represented bijectively by
;; (:RWI-VNUM integer) and (:RWI-UNDERFLOW).

(defun rwi-vnum (integer)
  (list :rwi-vnum integer))

(defun rwi-underflow ()
  (list :rwi-underflow))

(defun rwi-underflow-p (value)
  (equal value (rwi-underflow)))

(defun rwi-vnum-number (value)
  (cadr value))

;; This is exactly the source SemWithError.eval_0 on valid expressions.

(defun rwi-eval-0 (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rwi-cte-shape-p expression)
    (if (<= 0 (rwi-cte-number expression))
        (rwi-vnum (rwi-cte-number expression))
      (rwi-underflow)))
   ((rwi-sub-shape-p expression)
    (let ((left-value
           (rwi-eval-0 (rwi-sub-left expression))))
      (if (rwi-underflow-p left-value)
          (rwi-underflow)
        (let ((right-value
               (rwi-eval-0 (rwi-sub-right expression))))
          (if (rwi-underflow-p right-value)
              (rwi-underflow)
            (if (<= (rwi-vnum-number right-value)
                    (rwi-vnum-number left-value))
                (rwi-vnum
                 (- (rwi-vnum-number left-value)
                    (rwi-vnum-number right-value)))
              (rwi-underflow)))))))
   (t (rwi-underflow))))

;; Contexts are represented bijectively by the finite constructor records
;; (:RWI-EMPTY), (:RWI-LEFT context expression), and
;; (:RWI-RIGHT integer context).

(defun rwi-empty-shape-p (context)
  (equal context (list :rwi-empty)))

(defun rwi-left-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rwi-left)))

(defun rwi-right-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rwi-right)))

(defun rwi-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rwi-empty-shape-p context)
    t)
   ((rwi-left-shape-p context)
    (and
     (rwi-context-p (cadr context))
     (rwi-expression-p (caddr context))))
   ((rwi-right-shape-p context)
    (and
     (integerp (cadr context))
     (rwi-context-p (caddr context))))
   (t nil)))

(defun rwi-empty ()
  (list :rwi-empty))

(defun rwi-left (context expression)
  (list :rwi-left context expression))

(defun rwi-right (integer context)
  (list :rwi-right integer context))

(defun rwi-left-context (context)
  (cadr context))

(defun rwi-left-expression (context)
  (caddr context))

(defun rwi-right-number (context)
  (cadr context))

(defun rwi-right-context (context)
  (caddr context))

;; This is exactly the source recompose definition on valid contexts and
;; expressions.

(defun rwi-recompose (context expression)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rwi-empty-shape-p context)
    expression)
   ((rwi-left-shape-p context)
    (rwi-recompose
     (rwi-left-context context)
     (rwi-sub expression
              (rwi-left-expression context))))
   ((rwi-right-shape-p context)
    (rwi-recompose
     (rwi-right-context context)
     (rwi-sub
      (rwi-cte (rwi-right-number context))
      expression)))
   (t expression)))

(defun
  ntp4vc-pearl-defunctionalization-rwitherror-interpretqtvc-statement
  (p)
  (implies
   (rwi-expression-p p)
   (equal
    (rwi-eval-0 (rwi-recompose (rwi-empty) p))
    (rwi-eval-0 p))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
