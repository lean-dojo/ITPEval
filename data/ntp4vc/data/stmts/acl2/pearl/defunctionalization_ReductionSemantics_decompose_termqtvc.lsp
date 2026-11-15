;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/defunctionalization_ReductionSemantics_decompose_termqtvc:
;; structural decrease, recomposition preservation, and value production when
;; decomposing an integer subtraction expression in a reduction context. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Expressions are exact finite constructor records:
;; (:DTD-CTE integer) and (:DTD-SUB expression expression).

(defun dtd-cte-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 2)
   (equal (car expression) :dtd-cte)))

(defun dtd-sub-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 3)
   (equal (car expression) :dtd-sub)))

(defun dtd-expression-p (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((dtd-cte-shape-p expression)
    (integerp (cadr expression)))
   ((dtd-sub-shape-p expression)
    (and
     (dtd-expression-p (cadr expression))
     (dtd-expression-p (caddr expression))))
   (t nil)))

(defun dtd-cte (integer)
  (list :dtd-cte integer))

(defun dtd-sub (left right)
  (list :dtd-sub left right))

(defun dtd-cte-number (expression)
  (cadr expression))

(defun dtd-sub-left (expression)
  (cadr expression))

(defun dtd-sub-right (expression)
  (caddr expression))

;; This is the source Defunctionalization.size_e definition.

(defun dtd-size-e (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((dtd-cte-shape-p expression)
    1)
   ((dtd-sub-shape-p expression)
    (+
     3
     (dtd-size-e (dtd-sub-left expression))
     (dtd-size-e (dtd-sub-right expression))))
   (t 0)))

;; Reduction contexts are exact finite constructor records:
;; (:DTD-EMPTY), (:DTD-LEFT context expression), and
;; (:DTD-RIGHT integer context).

(defun dtd-empty-shape-p (context)
  (equal context (list :dtd-empty)))

(defun dtd-left-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :dtd-left)))

(defun dtd-right-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :dtd-right)))

(defun dtd-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((dtd-empty-shape-p context)
    t)
   ((dtd-left-shape-p context)
    (and
     (dtd-context-p (cadr context))
     (dtd-expression-p (caddr context))))
   ((dtd-right-shape-p context)
    (and
     (integerp (cadr context))
     (dtd-context-p (caddr context))))
   (t nil)))

(defun dtd-empty ()
  (list :dtd-empty))

(defun dtd-left (context expression)
  (list :dtd-left context expression))

(defun dtd-right (integer context)
  (list :dtd-right integer context))

(defun dtd-left-context (context)
  (cadr context))

(defun dtd-left-expression (context)
  (caddr context))

(defun dtd-right-number (context)
  (cadr context))

(defun dtd-right-context (context)
  (caddr context))

;; These are the source reduction-semantics definitions.

(defun dtd-recompose (context expression)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((dtd-empty-shape-p context)
    expression)
   ((dtd-left-shape-p context)
    (dtd-recompose
     (dtd-left-context context)
     (dtd-sub
      expression
      (dtd-left-expression context))))
   ((dtd-right-shape-p context)
    (dtd-recompose
     (dtd-right-context context)
     (dtd-sub
      (dtd-cte (dtd-right-number context))
      expression)))
   (t expression)))

(defun dtd-redex-p (expression)
  (and
   (dtd-sub-shape-p expression)
   (dtd-cte-shape-p (dtd-sub-left expression))
   (dtd-cte-shape-p (dtd-sub-right expression))))

(defun dtd-value-p (expression)
  (dtd-cte-shape-p expression))

(defun dtd-empty-context-p (context)
  (dtd-empty-shape-p context))

(defun dtd-size-c (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((dtd-empty-shape-p context)
    0)
   ((dtd-left-shape-p context)
    (+
     2
     (dtd-size-c (dtd-left-context context))
     (dtd-size-e (dtd-left-expression context))))
   ((dtd-right-shape-p context)
    (+
     1
     (dtd-size-c (dtd-right-context context))))
   (t 0)))

;; These predicates preserve the source's branch-local universal quantifiers
;; over every well-typed reduction context and expression.

(defun-sk dtd-cte-recomposition-p (context number)
  (forall (context1 expression1)
    (implies
     (and
      (dtd-context-p context1)
      (dtd-expression-p expression1))
     (implies
      (and
       (equal
        (dtd-recompose context1 expression1)
        (dtd-recompose context (dtd-cte number)))
       (dtd-redex-p expression1))
      (and
       (equal
        (dtd-recompose context1 expression1)
        (dtd-recompose context (dtd-cte number)))
       (dtd-redex-p expression1))))))

(defun-sk dtd-sub-recomposition-p
  (context left-expression right-expression)
  (forall (context1 expression11)
    (implies
     (and
      (dtd-context-p context1)
      (dtd-expression-p expression11))
     (implies
      (and
       (equal
        (dtd-recompose context1 expression11)
        (dtd-recompose
         (dtd-left context right-expression)
         left-expression))
       (dtd-redex-p expression11))
      (and
       (equal
        (dtd-recompose context1 expression11)
        (dtd-recompose
         context
         (dtd-sub left-expression right-expression)))
       (dtd-redex-p expression11))))))

;; Exact constructor split of the source verification condition.

(defun dtd-decompose-term-obligation-p (expression context)
  (cond
   ((dtd-cte-shape-p expression)
    (and
     (and
      (<=
       0
       (+
        (dtd-size-e expression)
        (dtd-size-c context)))
      (<
       (dtd-size-c context)
       (+
        (dtd-size-e expression)
        (dtd-size-c context))))
     (dtd-cte-recomposition-p
      context
      (dtd-cte-number expression))
     (implies
      (dtd-empty-context-p context)
      (and
       (dtd-empty-context-p context)
       (dtd-value-p expression)))))
   ((dtd-sub-shape-p expression)
    (let* ((left-expression
            (dtd-sub-left expression))
           (right-expression
            (dtd-sub-right expression))
           (o1
            (dtd-left context right-expression)))
      (and
       (and
        (<=
         0
         (+
          (dtd-size-e expression)
          (dtd-size-c context)))
        (<
         (+
          (dtd-size-e left-expression)
          (dtd-size-c o1))
         (+
          (dtd-size-e expression)
          (dtd-size-c context))))
       (dtd-sub-recomposition-p
        context
        left-expression
        right-expression)
       (implies
        (and
         (dtd-empty-context-p o1)
         (dtd-value-p left-expression))
        (and
         (dtd-empty-context-p context)
         (dtd-value-p expression))))))
   (t nil)))

(defun
  ntp4vc-pearl-defunctionalization-reductionsemantics-decompose-termqtvc-statement
  (expression context)
  (implies
   (and
    (dtd-expression-p expression)
    (dtd-context-p context))
   (dtd-decompose-term-obligation-p
    expression context)))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
