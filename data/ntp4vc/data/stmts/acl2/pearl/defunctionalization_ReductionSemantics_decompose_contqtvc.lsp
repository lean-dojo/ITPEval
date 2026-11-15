;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/defunctionalization_ReductionSemantics_decompose_contqtvc:
;; structural decrease, recomposition preservation, and redex production when
;; decomposing a subtraction reduction context after obtaining an integer
;; value. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Expressions are exact finite constructor records:
;; (:DCD-CTE integer) and (:DCD-SUB expression expression).

(defun dcd-cte-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 2)
   (equal (car expression) :dcd-cte)))

(defun dcd-sub-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 3)
   (equal (car expression) :dcd-sub)))

(defun dcd-expression-p (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((dcd-cte-shape-p expression)
    (integerp (cadr expression)))
   ((dcd-sub-shape-p expression)
    (and
     (dcd-expression-p (cadr expression))
     (dcd-expression-p (caddr expression))))
   (t nil)))

(defun dcd-cte (integer)
  (list :dcd-cte integer))

(defun dcd-sub (left right)
  (list :dcd-sub left right))

(defun dcd-cte-number (expression)
  (cadr expression))

(defun dcd-sub-left (expression)
  (cadr expression))

(defun dcd-sub-right (expression)
  (caddr expression))

;; This is the source Defunctionalization.size_e definition.

(defun dcd-size-e (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((dcd-cte-shape-p expression)
    1)
   ((dcd-sub-shape-p expression)
    (+
     3
     (dcd-size-e (dcd-sub-left expression))
     (dcd-size-e (dcd-sub-right expression))))
   (t 0)))

;; Reduction contexts are exact finite constructor records:
;; (:DCD-EMPTY), (:DCD-LEFT context expression), and
;; (:DCD-RIGHT integer context).

(defun dcd-empty-shape-p (context)
  (equal context (list :dcd-empty)))

(defun dcd-left-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :dcd-left)))

(defun dcd-right-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :dcd-right)))

(defun dcd-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((dcd-empty-shape-p context)
    t)
   ((dcd-left-shape-p context)
    (and
     (dcd-context-p (cadr context))
     (dcd-expression-p (caddr context))))
   ((dcd-right-shape-p context)
    (and
     (integerp (cadr context))
     (dcd-context-p (caddr context))))
   (t nil)))

(defun dcd-empty ()
  (list :dcd-empty))

(defun dcd-left (context expression)
  (list :dcd-left context expression))

(defun dcd-right (integer context)
  (list :dcd-right integer context))

(defun dcd-left-context (context)
  (cadr context))

(defun dcd-left-expression (context)
  (caddr context))

(defun dcd-right-number (context)
  (cadr context))

(defun dcd-right-context (context)
  (caddr context))

;; These are the source reduction-semantics definitions.

(defun dcd-recompose (context expression)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((dcd-empty-shape-p context)
    expression)
   ((dcd-left-shape-p context)
    (dcd-recompose
     (dcd-left-context context)
     (dcd-sub
      expression
      (dcd-left-expression context))))
   ((dcd-right-shape-p context)
    (dcd-recompose
     (dcd-right-context context)
     (dcd-sub
      (dcd-cte (dcd-right-number context))
      expression)))
   (t expression)))

(defun dcd-redex-p (expression)
  (and
   (dcd-sub-shape-p expression)
   (dcd-cte-shape-p (dcd-sub-left expression))
   (dcd-cte-shape-p (dcd-sub-right expression))))

(defun dcd-value-p (expression)
  (dcd-cte-shape-p expression))

(defun dcd-empty-context-p (context)
  (dcd-empty-shape-p context))

(defun dcd-size-c (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((dcd-empty-shape-p context)
    0)
   ((dcd-left-shape-p context)
    (+
     2
     (dcd-size-c (dcd-left-context context))
     (dcd-size-e (dcd-left-expression context))))
   ((dcd-right-shape-p context)
    (+
     1
     (dcd-size-c (dcd-right-context context))))
   (t 0)))

;; This preserves the source's nested universal quantifier over every
;; reduction context c11 and expression e1 in the Left constructor case.

(defun-sk dcd-left-recomposition-p (context number)
  (forall (c11 e1)
    (implies
     (and
      (dcd-context-p c11)
      (dcd-expression-p e1))
     (implies
      (and
       (equal
        (dcd-recompose c11 e1)
        (dcd-recompose
         (dcd-right
          number
          (dcd-left-context context))
         (dcd-left-expression context)))
       (dcd-redex-p e1))
      (and
       (equal
        (dcd-recompose c11 e1)
        (dcd-recompose
         context
         (dcd-cte number)))
       (dcd-redex-p e1))))))

;; Exact constructor split of the source verification condition.

(defun dcd-decompose-cont-obligation-p (context number)
  (cond
   ((dcd-empty-shape-p context)
    (dcd-empty-context-p context))
   ((dcd-left-shape-p context)
    (let ((o1
           (dcd-right
            number
            (dcd-left-context context)))
          (expression
           (dcd-left-expression context)))
      (and
       (and
        (<= 0 (dcd-size-c context))
        (<
         (+
          (dcd-size-e expression)
          (dcd-size-c o1))
         (dcd-size-c context)))
       (dcd-left-recomposition-p context number)
       (implies
        (and
         (dcd-empty-context-p o1)
         (dcd-value-p expression))
        (dcd-empty-context-p context)))))
   ((dcd-right-shape-p context)
    (let* ((context1
            (dcd-right-context context))
           (o1
            (dcd-sub
             (dcd-cte
              (dcd-right-number context))
             (dcd-cte number))))
      (and
       (equal
        (dcd-recompose context1 o1)
        (dcd-recompose
         context
         (dcd-cte number)))
       (dcd-redex-p o1))))
   (t nil)))

(defun
  ntp4vc-pearl-defunctionalization-reductionsemantics-decompose-contqtvc-statement
  (context number)
  (implies
   (and
    (dcd-context-p context)
    (integerp number))
   (dcd-decompose-cont-obligation-p
    context number)))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
