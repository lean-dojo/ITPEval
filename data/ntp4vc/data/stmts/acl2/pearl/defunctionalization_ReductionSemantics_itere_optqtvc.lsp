;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/defunctionalization_ReductionSemantics_itere_optqtvc: preservation of
;; direct evaluation across redex replacement in integer-subtraction reduction
;; contexts, together with the empty-context value result. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Expressions are represented bijectively by the finite constructor records
;; (:RSIO-CTE integer) and (:RSIO-SUB expression expression).

(defun rsio-cte-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 2)
   (equal (car expression) :rsio-cte)))

(defun rsio-sub-shape-p (expression)
  (and
   (true-listp expression)
   (equal (len expression) 3)
   (equal (car expression) :rsio-sub)))

(defun rsio-expression-p (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rsio-cte-shape-p expression)
    (integerp (cadr expression)))
   ((rsio-sub-shape-p expression)
    (and
     (rsio-expression-p (cadr expression))
     (rsio-expression-p (caddr expression))))
   (t nil)))

(defun rsio-cte (integer)
  (list :rsio-cte integer))

(defun rsio-sub (left right)
  (list :rsio-sub left right))

(defun rsio-cte-number (expression)
  (cadr expression))

(defun rsio-sub-left (expression)
  (cadr expression))

(defun rsio-sub-right (expression)
  (caddr expression))

;; This is the source DirectSem.eval_0 definition on valid expressions.

(defun rsio-eval-0 (expression)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((rsio-cte-shape-p expression)
    (rsio-cte-number expression))
   ((rsio-sub-shape-p expression)
    (-
     (rsio-eval-0 (rsio-sub-left expression))
     (rsio-eval-0 (rsio-sub-right expression))))
   (t 0)))

;; Reduction contexts are represented bijectively by the finite constructor
;; records (:RSIO-EMPTY), (:RSIO-LEFT context expression), and
;; (:RSIO-RIGHT integer context).

(defun rsio-empty-shape-p (context)
  (equal context (list :rsio-empty)))

(defun rsio-left-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rsio-left)))

(defun rsio-right-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :rsio-right)))

(defun rsio-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rsio-empty-shape-p context)
    t)
   ((rsio-left-shape-p context)
    (and
     (rsio-context-p (cadr context))
     (rsio-expression-p (caddr context))))
   ((rsio-right-shape-p context)
    (and
     (integerp (cadr context))
     (rsio-context-p (caddr context))))
   (t nil)))

(defun rsio-empty ()
  (list :rsio-empty))

(defun rsio-left (context expression)
  (list :rsio-left context expression))

(defun rsio-right (integer context)
  (list :rsio-right integer context))

(defun rsio-left-context (context)
  (cadr context))

(defun rsio-left-expression (context)
  (caddr context))

(defun rsio-right-number (context)
  (cadr context))

(defun rsio-right-context (context)
  (caddr context))

;; These are the source reduction-semantics definitions on valid inputs.

(defun rsio-recompose (context expression)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((rsio-empty-shape-p context)
    expression)
   ((rsio-left-shape-p context)
    (rsio-recompose
     (rsio-left-context context)
     (rsio-sub
      expression
      (rsio-left-expression context))))
   ((rsio-right-shape-p context)
    (rsio-recompose
     (rsio-right-context context)
     (rsio-sub
      (rsio-cte (rsio-right-number context))
      expression)))
   (t expression)))

(defun rsio-redex-p (expression)
  (and
   (rsio-sub-shape-p expression)
   (rsio-cte-shape-p (rsio-sub-left expression))
   (rsio-cte-shape-p (rsio-sub-right expression))))

(defun rsio-value-p (expression)
  (rsio-cte-shape-p expression))

(defun rsio-empty-context-p (context)
  (rsio-empty-shape-p context))

;; Preserve the source's universal quantifier over every expression replacing
;; a selected redex.

(defun-sk rsio-all-replacements-p
  (context redex initial-context initial-expression)
  (forall (replacement)
    (implies
     (rsio-expression-p replacement)
     (implies
      (equal
       (rsio-eval-0 replacement)
       (rsio-eval-0 redex))
      (equal
       (rsio-eval-0
        (rsio-recompose context replacement))
       (rsio-eval-0
        (rsio-recompose
         initial-context
         initial-expression)))))))

;; Preserve the source's universal quantifiers over every typed context/redex
;; decomposition of the original recomposed expression.

(defun-sk rsio-all-redex-decompositions-p
  (initial-context initial-expression)
  (forall (context redex)
    (implies
     (and
      (rsio-context-p context)
      (rsio-expression-p redex))
     (implies
      (and
       (equal
        (rsio-recompose context redex)
        (rsio-recompose
         initial-context
         initial-expression))
       (rsio-redex-p redex))
      (and
       (rsio-redex-p redex)
       (rsio-all-replacements-p
        context
        redex
        initial-context
        initial-expression))))))

;; These two predicates are the source match expressions in the value clause.

(defun rsio-value-constructor-case-p (expression)
  (if (rsio-cte-shape-p expression)
      t
    nil))

(defun rsio-result-premise-p (expression result)
  (if (rsio-cte-shape-p expression)
      (equal result (rsio-cte-number expression))
    nil))

;; Preserve the source's universal quantifier over every integer result.

(defun-sk rsio-all-results-p (initial-context initial-expression)
  (forall (result)
    (implies
     (integerp result)
     (implies
      (rsio-result-premise-p
       initial-expression
       result)
      (equal
       result
       (rsio-eval-0
        (rsio-recompose
         initial-context
         initial-expression)))))))

(defun rsio-empty-context-value-obligation-p
  (initial-context initial-expression)
  (implies
   (and
    (rsio-empty-context-p initial-context)
    (rsio-value-p initial-expression))
   (and
    (rsio-value-constructor-case-p initial-expression)
    (rsio-all-results-p
     initial-context
     initial-expression))))

(defun
  ntp4vc-pearl-defunctionalization-reductionsemantics-itere-optqtvc-statement
  (initial-context initial-expression)
  (implies
   (and
    (rsio-context-p initial-context)
    (rsio-expression-p initial-expression))
   (and
    (rsio-all-redex-decompositions-p
     initial-context
     initial-expression)
    (rsio-empty-context-value-obligation-p
     initial-context
     initial-expression))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
