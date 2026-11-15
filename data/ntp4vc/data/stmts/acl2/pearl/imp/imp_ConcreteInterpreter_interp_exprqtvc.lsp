;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/imp/imp_ConcreteInterpreter_interp_exprqtvc: the verification
;; condition for interpreting integer literals, variables, and subtraction
;; expressions with possible unbound-variable behavior. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Options, expressions, and expression behaviors are exact finite
;; constructor records for the source datatypes.

(defun ici-option-none ()
  (list :ici-none))

(defun ici-option-some (value)
  (list :ici-some value))

(defun ici-option-none-p (option)
  (equal option (ici-option-none)))

(defun ici-option-some-shape-p (option)
  (and
   (true-listp option)
   (equal (len option) 2)
   (equal (car option) :ici-some)))

(defun ici-option-some-value (option)
  (cadr option))

(defun ici-option-integer-p (option)
  (or
   (ici-option-none-p option)
   (and
    (ici-option-some-shape-p option)
    (integerp (ici-option-some-value option)))))

(defun ici-elit-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 2)
   (equal (car expression) :ici-elit)))

(defun ici-evar-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 2)
   (equal (car expression) :ici-evar)))

(defun ici-esub-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 3)
   (equal (car expression) :ici-esub)))

(defun ici-expression-p (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((ici-elit-shape-p expression)
    (integerp (cadr expression)))
   ((ici-evar-shape-p expression)
    t)
   ((ici-esub-shape-p expression)
    (and
     (ici-expression-p (cadr expression))
     (ici-expression-p (caddr expression))))
   (t nil)))

(defun ici-elit-value (expression)
  (cadr expression))

(defun ici-evar-variable (expression)
  (cadr expression))

(defun ici-esub-left (expression)
  (cadr expression))

(defun ici-esub-right (expression)
  (caddr expression))

(defun ici-enormal (value)
  (list :ici-enormal value))

(defun ici-eunbound-var ()
  (list :ici-eunbound-var))

(defun ici-enormal-shape-p (behavior)
  (and
   (true-listp behavior)
   (equal (len behavior) 2)
   (equal (car behavior) :ici-enormal)))

(defun ici-enormal-value (behavior)
  (cadr behavior))

(defun ici-eunbound-var-p (behavior)
  (equal behavior (ici-eunbound-var)))

;; The source environment type is abstract and is observed only through
;; model1/get.  The conservative raw interface ranges over arbitrary
;; environments and program variables.  Normalization changes only ill-typed
;; raw outputs, so every arbitrary source function into Option integer is
;; represented without restricting it to a finite table.

(defstub ici-raw-model1 (environment variable) t)

(defun ici-model1 (environment variable)
  (let ((option (ici-raw-model1 environment variable)))
    (if (ici-option-integer-p option)
        option
      (ici-option-none))))

;; On valid expressions, this deterministic evaluator is bidirectionally
;; equivalent to the source inductive eval_expr relation: its branches are
;; exactly eval_lit, the two variable rules, and the three subtraction
;; success/error cases.

(defun ici-eval-expr-value (environment expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((ici-elit-shape-p expression)
    (ici-enormal (ici-elit-value expression)))
   ((ici-evar-shape-p expression)
    (let ((option
           (ici-model1
            environment
            (ici-evar-variable expression))))
      (if (ici-option-none-p option)
          (ici-eunbound-var)
        (ici-enormal
         (ici-option-some-value option)))))
   ((ici-esub-shape-p expression)
    (let ((left-behavior
           (ici-eval-expr-value
            environment
            (ici-esub-left expression))))
      (if (ici-eunbound-var-p left-behavior)
          (ici-eunbound-var)
        (let ((right-behavior
               (ici-eval-expr-value
                environment
                (ici-esub-right expression))))
          (if (ici-eunbound-var-p right-behavior)
              (ici-eunbound-var)
            (ici-enormal
             (-
              (ici-enormal-value left-behavior)
              (ici-enormal-value right-behavior))))))))
   (t (ici-eunbound-var))))

(defun ici-eval-expr-p (environment expression behavior)
  (equal
   behavior
   (ici-eval-expr-value environment expression)))

;; This preserves the source match expression that tests whether either
;; immediate child of a subtraction expression equals the selected child.

(defun ici-immediate-component-p (expression component)
  (cond
   ((ici-elit-shape-p expression)
    nil)
   ((ici-evar-shape-p expression)
    nil)
   ((ici-esub-shape-p expression)
    (or
     (equal (ici-esub-left expression) component)
     (equal (ici-esub-right expression) component)))
   (t nil)))

(defun ici-lookup-matches-result-p
    (environment variable result)
  (let ((option (ici-model1 environment variable)))
    (if (ici-option-none-p option)
        nil
      (equal
       result
       (ici-option-some-value option)))))

;; Preserve the universal quantifier over every integer result in the Evar
;; branch.

(defun-sk ici-all-variable-results-p
    (environment expression variable)
  (forall (result)
    (implies
     (integerp result)
     (implies
      (ici-lookup-matches-result-p
       environment variable result)
      (ici-eval-expr-p
       environment expression (ici-enormal result))))))

(defun ici-variable-branch-p
    (environment expression variable)
  (and
   (ici-all-variable-results-p
    environment expression variable)
   (implies
    (equal
     (ici-model1 environment variable)
     (ici-option-none))
    (ici-eval-expr-p
     environment expression (ici-eunbound-var)))))

;; O2 remains universally quantified inside the implication for each O1,
;; exactly as in the source subtraction branch.

(defun-sk ici-all-left-results-p
    (environment expression left-expression o1)
  (forall (o2)
    (implies
     (integerp o2)
     (implies
      (ici-eval-expr-p
       environment left-expression (ici-enormal o2))
      (ici-eval-expr-p
       environment expression (ici-enormal (- o2 o1)))))))

(defun ici-right-result-conclusion-p
    (environment expression left-expression o1)
  (and
   (ici-immediate-component-p expression left-expression)
   (ici-all-left-results-p
    environment expression left-expression o1)
   (implies
    (ici-eval-expr-p
     environment left-expression (ici-eunbound-var))
    (ici-eval-expr-p
     environment expression (ici-eunbound-var)))))

;; Preserve the universal quantifier over every integer O1 whose normal
;; behavior is assumed for the right operand.

(defun-sk ici-all-right-results-p
    (environment expression left-expression right-expression)
  (forall (o1)
    (implies
     (integerp o1)
     (implies
      (ici-eval-expr-p
       environment right-expression (ici-enormal o1))
      (ici-right-result-conclusion-p
       environment expression left-expression o1)))))

(defun ici-subtraction-branch-p
    (environment expression left-expression right-expression)
  (and
   (ici-immediate-component-p expression right-expression)
   (ici-all-right-results-p
    environment expression left-expression right-expression)
   (implies
    (ici-eval-expr-p
     environment right-expression (ici-eunbound-var))
    (ici-eval-expr-p
     environment expression (ici-eunbound-var)))))

(defun
  ntp4vc-pearl-imp-concreteinterpreter-interp-exprqtvc-statement
  (expression environment)
  (implies
   (ici-expression-p expression)
   (cond
    ((ici-elit-shape-p expression)
     (ici-eval-expr-p
      environment
      expression
      (ici-enormal (ici-elit-value expression))))
    ((ici-evar-shape-p expression)
     (ici-variable-branch-p
      environment
      expression
      (ici-evar-variable expression)))
    ((ici-esub-shape-p expression)
     (ici-subtraction-branch-p
      environment
      expression
      (ici-esub-left expression)
      (ici-esub-right expression)))
    (t nil))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
