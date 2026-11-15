;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/imp/imp_SymbolicInterpreter_symbolic_interp_exprqtvc: soundness of
;; symbolic interpretation for integer literals, variables, and subtraction,
;; including symbolic-variable provenance and unbound-variable propagation.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Program variables and symbolic variables are disjoint inhabited copies of
;; ACL2's unbounded universe, matching the two abstract source carrier types.

(defun siex-program-var-p (x)
  (and
   (true-listp x)
   (equal (len x) 2)
   (equal (car x) :siex-program-var)))

(defun siex-svar-p (x)
  (and
   (true-listp x)
   (equal (len x) 2)
   (equal (car x) :siex-svar)))

;; Options are represented bijectively by NIL and (:SIEX-SOME value).

(defun siex-some (value)
  (list :siex-some value))

(defun siex-some-p (value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (equal (car value) :siex-some)))

(defun siex-option-svar-p (value)
  (or
   (equal value nil)
   (and
    (siex-some-p value)
    (siex-svar-p (cadr value)))))

;; Concrete and symbolic expressions use the source inductive constructors
;; exactly, with ACL2 integers representing the source's mathematical integers.

(defun siex-expr-p (expr)
  (and
   (consp expr)
   (cond
    ((equal (car expr) :siex-elit)
     (and
      (true-listp expr)
      (equal (len expr) 2)
      (integerp (cadr expr))))
    ((equal (car expr) :siex-evar)
     (and
      (true-listp expr)
      (equal (len expr) 2)
      (siex-program-var-p (cadr expr))))
    ((equal (car expr) :siex-esub)
     (and
      (true-listp expr)
      (equal (len expr) 3)
      (siex-expr-p (cadr expr))
      (siex-expr-p (caddr expr))))
    (t nil))))

(defun siex-symbolic-expr-p (expr)
  (and
   (consp expr)
   (cond
    ((equal (car expr) :siex-slit)
     (and
      (true-listp expr)
      (equal (len expr) 2)
      (integerp (cadr expr))))
    ((equal (car expr) :siex-svar-expr)
     (and
      (true-listp expr)
      (equal (len expr) 2)
      (siex-svar-p (cadr expr))))
    ((equal (car expr) :siex-ssub)
     (and
      (true-listp expr)
      (equal (len expr) 3)
      (siex-symbolic-expr-p (cadr expr))
      (siex-symbolic-expr-p (caddr expr))))
    (t nil))))

;; Constraints are retained because symbolic states in the source carry a
;; constraint and satisfy an invariant relating its variables to state vars.

(defun siex-constraint-p (constraint)
  (and
   (consp constraint)
   (cond
    ((or
      (equal (car constraint) :siex-ctrue)
      (equal (car constraint) :siex-cfalse))
     (and
      (true-listp constraint)
      (equal (len constraint) 1)))
    ((or
      (equal (car constraint) :siex-ceq)
      (equal (car constraint) :siex-cneq))
     (and
      (true-listp constraint)
      (equal (len constraint) 3)
      (siex-symbolic-expr-p (cadr constraint))
      (siex-symbolic-expr-p (caddr constraint))))
    ((equal (car constraint) :siex-cconj)
     (and
      (true-listp constraint)
      (equal (len constraint) 3)
      (siex-constraint-p (cadr constraint))
      (siex-constraint-p (caddr constraint))))
    ((equal (car constraint) :siex-cexists)
     (and
      (true-listp constraint)
      (equal (len constraint) 3)
      (siex-svar-p (cadr constraint))
      (siex-constraint-p (caddr constraint))))
    (t nil))))

;; Finite sets are duplicate-free proper lists, an extensional representation
;; of the finite sets used for symbolic-expression and constraint variables.

(defun siex-no-duplicates-p (xs)
  (if (consp xs)
      (and
       (not (member-equal (car xs) (cdr xs)))
       (siex-no-duplicates-p (cdr xs)))
    (equal xs nil)))

(defun siex-svar-list-p (xs)
  (if (consp xs)
      (and
       (siex-svar-p (car xs))
       (siex-svar-list-p (cdr xs)))
    (equal xs nil)))

(defun siex-svar-set-p (xs)
  (and
   (siex-svar-list-p xs)
   (siex-no-duplicates-p xs)))

(defun siex-set-subset-p (left right)
  (if (consp left)
      (and
       (member-equal (car left) right)
       (siex-set-subset-p (cdr left) right))
    (equal left nil)))

(defun siex-svar-set-insert (element set)
  (if (member-equal element set)
      set
    (cons element set)))

(defun siex-svar-set-union (left right)
  (if (consp left)
      (siex-svar-set-insert
       (car left)
       (siex-svar-set-union (cdr left) right))
    right))

(defun siex-symbolic-expr-vars (expr)
  (cond
   ((equal (car expr) :siex-slit)
    nil)
   ((equal (car expr) :siex-svar-expr)
    (list (cadr expr)))
   ((equal (car expr) :siex-ssub)
    (siex-svar-set-union
     (siex-symbolic-expr-vars (cadr expr))
     (siex-symbolic-expr-vars (caddr expr))))
   (t nil)))

(defun siex-constraint-vars (constraint)
  (cond
   ((or
     (equal (car constraint) :siex-ctrue)
     (equal (car constraint) :siex-cfalse))
    nil)
   ((or
     (equal (car constraint) :siex-ceq)
     (equal (car constraint) :siex-cneq))
    (siex-svar-set-union
     (siex-symbolic-expr-vars (cadr constraint))
     (siex-symbolic-expr-vars (caddr constraint))))
   ((equal (car constraint) :siex-cconj)
    (siex-svar-set-union
     (siex-constraint-vars (cadr constraint))
     (siex-constraint-vars (caddr constraint))))
   ((equal (car constraint) :siex-cexists)
    (siex-svar-set-insert
     (cadr constraint)
     (siex-constraint-vars (caddr constraint))))
   (t nil)))

;; A valuation handle denotes an arbitrary total function from symbolic
;; variables to integers. IFIX only totalizes ill-typed raw ACL2 outputs.

(defstub siex-rho-raw (handle svar) t)

(defun siex-rho-p (rho)
  (and
   (true-listp rho)
   (equal (len rho) 2)
   (equal (car rho) :siex-rho)))

(defun siex-rho-apply (rho svar)
  (ifix (siex-rho-raw (cadr rho) svar)))

(defun siex-interp-symbolic-expr (rho expr)
  (cond
   ((equal (car expr) :siex-slit)
    (cadr expr))
   ((equal (car expr) :siex-svar-expr)
    (siex-rho-apply rho (cadr expr)))
   ((equal (car expr) :siex-ssub)
    (-
     (siex-interp-symbolic-expr rho (cadr expr))
     (siex-interp-symbolic-expr rho (caddr expr))))
   (t 0)))

;; Sigma is the source finite map from program variables to symbolic variables.
;; The middle field preserves the identity of the abstract map representation.

(defun siex-sigma-binding-p (binding)
  (and
   (true-listp binding)
   (equal (len binding) 3)
   (equal (car binding) :siex-sigma-binding)
   (siex-program-var-p (cadr binding))
   (siex-svar-p (caddr binding))))

(defun siex-sigma-bindings-p (bindings)
  (if (consp bindings)
      (and
       (siex-sigma-binding-p (car bindings))
       (siex-sigma-bindings-p (cdr bindings)))
    (equal bindings nil)))

(defun siex-sigma-key-member-p (key bindings)
  (if (consp bindings)
      (or
       (equal key (cadar bindings))
       (siex-sigma-key-member-p key (cdr bindings)))
    nil))

(defun siex-sigma-unique-keys-p (bindings)
  (if (consp bindings)
      (and
       (not
        (siex-sigma-key-member-p
         (cadar bindings)
         (cdr bindings)))
       (siex-sigma-unique-keys-p (cdr bindings)))
    (equal bindings nil)))

(defun siex-sigma-p (sigma)
  (and
   (true-listp sigma)
   (equal (len sigma) 3)
   (equal (car sigma) :siex-sigma)
   (siex-sigma-bindings-p (caddr sigma))
   (siex-sigma-unique-keys-p (caddr sigma))))

(defun siex-sigma-get-bindings (bindings program-var)
  (if (consp bindings)
      (if (equal program-var (cadar bindings))
          (siex-some (caddar bindings))
        (siex-sigma-get-bindings
         (cdr bindings) program-var))
    nil))

(defun siex-sigma-get (sigma program-var)
  (siex-sigma-get-bindings
   (caddr sigma) program-var))

;; Symbolic states retain all four source fields and both source invariants.

(defun siex-sigma-range-in-vars-p (bindings vars)
  (if (consp bindings)
      (and
       (member-equal (caddar bindings) vars)
       (siex-sigma-range-in-vars-p
        (cdr bindings) vars))
    (equal bindings nil)))

(defun siex-sym-state-p (st)
  (and
   (true-listp st)
   (equal (len st) 5)
   (equal (car st) :siex-state)
   (siex-sigma-p (cadr st))
   (siex-constraint-p (caddr st))
   (siex-rho-p (cadddr st))
   (siex-svar-set-p (car (cddddr st)))
   (siex-set-subset-p
    (siex-constraint-vars (caddr st))
    (car (cddddr st)))
   (siex-sigma-range-in-vars-p
    (caddr (cadr st))
    (car (cddddr st)))))

(defun siex-state-sigma (st)
  (cadr st))

(defun siex-state-rho (st)
  (cadddr st))

;; Compose is defined pointwise exactly as in the three source statements.

(defun siex-compose-get (rho sigma program-var)
  (let ((entry (siex-sigma-get sigma program-var)))
    (if (equal entry nil)
        nil
      (siex-some
       (siex-rho-apply rho (cadr entry))))))

;; On valid expressions this evaluator is bidirectionally equivalent to the
;; source inductive eval_expr relation, including both subtraction errors.

(defun siex-eval-expr-value (rho sigma expr)
  (cond
   ((equal (car expr) :siex-elit)
    (list :siex-enormal (cadr expr)))
   ((equal (car expr) :siex-evar)
    (let ((entry
           (siex-compose-get rho sigma (cadr expr))))
      (if (equal entry nil)
          :siex-eunbound-var
        (list :siex-enormal (cadr entry)))))
   ((equal (car expr) :siex-esub)
    (let ((left
           (siex-eval-expr-value
            rho sigma (cadr expr))))
      (if (equal left :siex-eunbound-var)
          :siex-eunbound-var
        (let ((right
               (siex-eval-expr-value
                rho sigma (caddr expr))))
          (if (equal right :siex-eunbound-var)
              :siex-eunbound-var
            (list
             :siex-enormal
             (- (cadr left) (cadr right))))))))
   (t :siex-eunbound-var)))

(defun siex-eval-expr-p (rho sigma expr behavior)
  (equal
   behavior
   (siex-eval-expr-value rho sigma expr)))

;; This is the source's nested match testing whether a selected expression is
;; one of the two immediate children of a subtraction expression.

(defun siex-immediate-component-p (expression component)
  (cond
   ((equal (car expression) :siex-elit)
    nil)
   ((equal (car expression) :siex-evar)
    nil)
   ((equal (car expression) :siex-esub)
    (or
     (equal (cadr expression) component)
     (equal (caddr expression) component)))
   (t nil)))

;; Preserve the internal existential asserting that each symbolic variable in
;; a produced expression has a program-variable preimage in sigma.

(defun-sk siex-sigma-preimage-p (sigma svar)
  (exists (program-var)
    (and
     (siex-program-var-p program-var)
     (equal
      (siex-sigma-get sigma program-var)
      (siex-some svar)))))

(defun-sk siex-all-symbolic-vars-mapped-p
    (sigma symbolic-expression)
  (forall (svar)
    (implies
     (siex-svar-p svar)
     (implies
      (member-equal
       svar
       (siex-symbolic-expr-vars symbolic-expression))
      (siex-sigma-preimage-p sigma svar)))))

(defun siex-symbolic-result-p
    (rho sigma expression symbolic-expression)
  (and
   (siex-eval-expr-p
    rho sigma expression
    (list
     :siex-enormal
     (siex-interp-symbolic-expr
      rho symbolic-expression)))
   (siex-all-symbolic-vars-mapped-p
    sigma symbolic-expression)))

;; The variable branch universally quantifies every symbolic variable returned
;; by sigma, then separately preserves the None/unbound implication.

(defun-sk siex-all-variable-results-p
    (rho sigma expression program-var)
  (forall (o1)
    (implies
     (siex-svar-p o1)
     (implies
      (equal
       (siex-sigma-get sigma program-var)
       (siex-some o1))
      (siex-symbolic-result-p
       rho sigma expression
       (list :siex-svar-expr o1))))))

(defun siex-variable-branch-p
    (rho sigma expression program-var)
  (and
   (siex-all-variable-results-p
    rho sigma expression program-var)
   (implies
    (equal
     (siex-sigma-get sigma program-var)
     nil)
    (siex-eval-expr-p
     rho sigma expression :siex-eunbound-var))))

;; O2 remains universally quantified inside the implication for each O1.

(defun-sk siex-all-left-results-p
    (rho sigma expression left-expression o1)
  (forall (o2)
    (implies
     (siex-symbolic-expr-p o2)
     (implies
      (siex-symbolic-result-p
       rho sigma left-expression o2)
      (siex-symbolic-result-p
       rho sigma expression
       (list :siex-ssub o2 o1))))))

(defun siex-right-result-conclusion-p
    (rho sigma expression left-expression o1)
  (and
   (siex-immediate-component-p
    expression left-expression)
   (siex-all-left-results-p
    rho sigma expression left-expression o1)
   (implies
    (siex-eval-expr-p
     rho sigma left-expression :siex-eunbound-var)
    (siex-eval-expr-p
     rho sigma expression :siex-eunbound-var))))

;; Preserve the outer universal quantifier over every symbolic result O1 of
;; the right operand.

(defun-sk siex-all-right-results-p
    (rho sigma expression left-expression right-expression)
  (forall (o1)
    (implies
     (siex-symbolic-expr-p o1)
     (implies
      (siex-symbolic-result-p
       rho sigma right-expression o1)
      (siex-right-result-conclusion-p
       rho sigma expression left-expression o1)))))

(defun siex-subtraction-branch-p
    (rho sigma expression left-expression right-expression)
  (and
   (siex-immediate-component-p
    expression right-expression)
   (siex-all-right-results-p
    rho sigma expression left-expression right-expression)
   (implies
    (siex-eval-expr-p
     rho sigma right-expression :siex-eunbound-var)
    (siex-eval-expr-p
     rho sigma expression :siex-eunbound-var))))

(defun
  ntp4vc-pearl-imp-symbolicinterpreter-symbolic-interp-exprqtvc-statement
  (expression st)
  (implies
   (and
    (siex-expr-p expression)
    (siex-sym-state-p st))
   (let ((rho (siex-state-rho st))
         (sigma (siex-state-sigma st)))
     (cond
      ((equal (car expression) :siex-elit)
       (siex-symbolic-result-p
        rho sigma expression
        (list :siex-slit (cadr expression))))
      ((equal (car expression) :siex-evar)
       (siex-variable-branch-p
        rho sigma expression (cadr expression)))
      ((equal (car expression) :siex-esub)
       (siex-subtraction-branch-p
        rho sigma expression
        (cadr expression)
        (caddr expression)))
      (t nil)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
