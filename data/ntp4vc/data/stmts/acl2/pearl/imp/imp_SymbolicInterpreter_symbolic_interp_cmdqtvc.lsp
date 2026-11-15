;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/imp/imp_SymbolicInterpreter_symbolic_interp_cmdqtvc: the
;; command-level symbolic-interpreter verification condition, including
;; assignment-state construction, sequencing, conditionals, bounded loops,
;; and sound and complete normal, unbound-variable, and loop-limit results.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Program variables and symbolic variables are disjoint inhabited copies of
;; ACL2's unbounded universe.  This preserves the source's arbitrary carrier
;; values without enumerating either carrier.

(defun sivc-program-var-p (x)
  (and
   (true-listp x)
   (equal (len x) 2)
   (equal (car x) :sivc-program-var)))

(defun sivc-svar-p (x)
  (and
   (true-listp x)
   (equal (len x) 2)
   (equal (car x) :sivc-svar)))

;; Options are represented bijectively by NIL and (:SIVC-SOME value).

(defun sivc-some (value)
  (list :sivc-some value))

(defun sivc-some-p (value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (equal (car value) :sivc-some)))

(defun sivc-option-svar-p (value)
  (or
   (equal value nil)
   (and
    (sivc-some-p value)
    (sivc-svar-p (cadr value)))))

(defun sivc-option-integer-p (value)
  (or
   (equal value nil)
   (and
    (sivc-some-p value)
    (integerp (cadr value)))))

;; Source expressions and commands are represented by their exact inductive
;; constructor trees.

(defun sivc-expr-p (expr)
  (and
   (consp expr)
   (cond
    ((equal (car expr) :sivc-elit)
     (and
      (true-listp expr)
      (equal (len expr) 2)
      (integerp (cadr expr))))
    ((equal (car expr) :sivc-evar)
     (and
      (true-listp expr)
      (equal (len expr) 2)
      (sivc-program-var-p (cadr expr))))
    ((equal (car expr) :sivc-esub)
     (and
      (true-listp expr)
      (equal (len expr) 3)
      (sivc-expr-p (cadr expr))
      (sivc-expr-p (caddr expr))))
    (t nil))))

(defun sivc-command-p (command)
  (and
   (consp command)
   (cond
    ((equal (car command) :sivc-cskip)
     (and
      (true-listp command)
      (equal (len command) 1)))
    ((equal (car command) :sivc-cassign)
     (and
      (true-listp command)
      (equal (len command) 3)
      (sivc-program-var-p (cadr command))
      (sivc-expr-p (caddr command))))
    ((equal (car command) :sivc-cseq)
     (and
      (true-listp command)
      (equal (len command) 3)
      (sivc-command-p (cadr command))
      (sivc-command-p (caddr command))))
    ((equal (car command) :sivc-cif)
     (and
      (true-listp command)
      (equal (len command) 4)
      (sivc-expr-p (cadr command))
      (sivc-command-p (caddr command))
      (sivc-command-p (cadddr command))))
    ((equal (car command) :sivc-cwhile)
     (and
      (true-listp command)
      (equal (len command) 3)
      (sivc-expr-p (cadr command))
      (sivc-command-p (caddr command))))
    (t nil))))

;; The source behavior datatype has exactly these three constructors.

(defun sivc-behavior-p (behavior)
  (or
   (equal behavior :sivc-normal)
   (equal behavior :sivc-unbound-var)
   (equal behavior :sivc-loop-limit)))

;; Symbolic expressions and constraints use the source constructors exactly.

(defun sivc-symbolic-expr-p (expr)
  (and
   (consp expr)
   (cond
    ((equal (car expr) :sivc-slit)
     (and
      (true-listp expr)
      (equal (len expr) 2)
      (integerp (cadr expr))))
    ((equal (car expr) :sivc-svar-expr)
     (and
      (true-listp expr)
      (equal (len expr) 2)
      (sivc-svar-p (cadr expr))))
    ((equal (car expr) :sivc-ssub)
     (and
      (true-listp expr)
      (equal (len expr) 3)
      (sivc-symbolic-expr-p (cadr expr))
      (sivc-symbolic-expr-p (caddr expr))))
    (t nil))))

(defun sivc-constraint-p (constraint)
  (and
   (consp constraint)
   (cond
    ((or
      (equal (car constraint) :sivc-ctrue)
      (equal (car constraint) :sivc-cfalse))
     (and
      (true-listp constraint)
      (equal (len constraint) 1)))
    ((or
      (equal (car constraint) :sivc-ceq)
      (equal (car constraint) :sivc-cneq))
     (and
      (true-listp constraint)
      (equal (len constraint) 3)
      (sivc-symbolic-expr-p (cadr constraint))
      (sivc-symbolic-expr-p (caddr constraint))))
    ((equal (car constraint) :sivc-cconj)
     (and
      (true-listp constraint)
      (equal (len constraint) 3)
      (sivc-constraint-p (cadr constraint))
      (sivc-constraint-p (caddr constraint))))
    ((equal (car constraint) :sivc-cexists)
     (and
      (true-listp constraint)
      (equal (len constraint) 3)
      (sivc-svar-p (cadr constraint))
      (sivc-constraint-p (caddr constraint))))
    (t nil))))

;; Source finite sets are represented extensionally by duplicate-free proper
;; lists. Source lists retain their order and may contain duplicates.

(defun sivc-no-duplicates-p (xs)
  (if (consp xs)
      (and
       (not (member-equal (car xs) (cdr xs)))
       (sivc-no-duplicates-p (cdr xs)))
    (equal xs nil)))

(defun sivc-svar-list-p (xs)
  (if (consp xs)
      (and
       (sivc-svar-p (car xs))
       (sivc-svar-list-p (cdr xs)))
    (equal xs nil)))

(defun sivc-svar-set-p (xs)
  (and
   (sivc-svar-list-p xs)
   (sivc-no-duplicates-p xs)))

(defun sivc-set-subset-p (left right)
  (if (consp left)
      (and
       (member-equal (car left) right)
       (sivc-set-subset-p (cdr left) right))
    (equal left nil)))

(defun sivc-svar-set-equiv-p (left right)
  (and
   (sivc-set-subset-p left right)
   (sivc-set-subset-p right left)))

(defun sivc-svar-set-insert (element set)
  (if (member-equal element set)
      set
    (cons element set)))

(defun sivc-svar-set-union (left right)
  (if (consp left)
      (sivc-svar-set-insert
       (car left)
       (sivc-svar-set-union (cdr left) right))
    right))

;; A base valuation is a handle for an arbitrary total function from symbolic
;; variables to integers.  Update nodes represent every source-level
;; functional update without restricting the arbitrary base valuation.

(defstub sivc-rho-raw (handle svar) t)

(defun sivc-rho-p (rho)
  (and
   (consp rho)
   (cond
    ((equal (car rho) :sivc-rho)
     (and
      (true-listp rho)
      (equal (len rho) 2)))
    ((equal (car rho) :sivc-rho-update)
     (and
      (true-listp rho)
      (equal (len rho) 4)
      (sivc-rho-p (cadr rho))
      (sivc-svar-p (caddr rho))
      (integerp (cadddr rho))))
    (t nil))))

(defun sivc-rho-apply (rho svar)
  (if (equal (car rho) :sivc-rho-update)
      (if (equal svar (caddr rho))
          (cadddr rho)
        (sivc-rho-apply (cadr rho) svar))
    (ifix (sivc-rho-raw (cadr rho) svar))))

(defun sivc-rho-update (rho svar value)
  (list :sivc-rho-update rho svar value))

(defun-sk sivc-rho-equiv-p (left right)
  (forall (svar)
    (implies
     (sivc-svar-p svar)
     (equal
      (sivc-rho-apply left svar)
      (sivc-rho-apply right svar)))))

;; Constraint maps are finite maps, matching the source gmap representation.
;; A tag preserves the identity of the source abstract map even when two maps
;; have the same pointwise contents.

(defun sivc-sigma-binding-p (binding)
  (and
   (true-listp binding)
   (equal (len binding) 3)
   (equal (car binding) :sivc-sigma-binding)
   (sivc-program-var-p (cadr binding))
   (sivc-svar-p (caddr binding))))

(defun sivc-sigma-bindings-p (bindings)
  (if (consp bindings)
      (and
       (sivc-sigma-binding-p (car bindings))
       (sivc-sigma-bindings-p (cdr bindings)))
    (equal bindings nil)))

(defun sivc-sigma-key-member-p (key bindings)
  (if (consp bindings)
      (or
       (equal key (cadar bindings))
       (sivc-sigma-key-member-p key (cdr bindings)))
    nil))

(defun sivc-sigma-unique-keys-p (bindings)
  (if (consp bindings)
      (and
       (not
        (sivc-sigma-key-member-p
         (cadar bindings)
         (cdr bindings)))
       (sivc-sigma-unique-keys-p (cdr bindings)))
    (equal bindings nil)))

(defun sivc-sigma-p (sigma)
  (and
   (true-listp sigma)
   (equal (len sigma) 3)
   (equal (car sigma) :sivc-sigma)
   (sivc-sigma-bindings-p (caddr sigma))
   (sivc-sigma-unique-keys-p (caddr sigma))))

(defun sivc-sigma-get-bindings (bindings program-var)
  (if (consp bindings)
      (if (equal program-var (cadar bindings))
          (sivc-some (caddar bindings))
        (sivc-sigma-get-bindings
         (cdr bindings) program-var))
    nil))

(defun sivc-sigma-get (sigma program-var)
  (sivc-sigma-get-bindings
   (caddr sigma) program-var))

(defun sivc-sigma-set-bindings
    (bindings program-var svar)
  (if (consp bindings)
      (if (equal program-var (cadar bindings))
          (cons
           (list :sivc-sigma-binding program-var svar)
           (cdr bindings))
        (cons
         (car bindings)
         (sivc-sigma-set-bindings
          (cdr bindings) program-var svar)))
    (list
     (list :sivc-sigma-binding program-var svar))))

(defun sivc-sigma-set (sigma program-var svar)
  (list
   :sivc-sigma
   (list :sivc-sigma-set
         (cadr sigma)
         program-var
         svar)
   (sivc-sigma-set-bindings
    (caddr sigma) program-var svar)))

(defun-sk sivc-sigma-equiv-p (left right)
  (forall (program-var)
    (implies
     (sivc-program-var-p program-var)
     (equal
      (sivc-sigma-get left program-var)
      (sivc-sigma-get right program-var)))))

;; Constraint variables and satisfaction are computed by structural recursion.

(defun sivc-symbolic-expr-vars (expr)
  (cond
   ((equal (car expr) :sivc-slit)
    nil)
   ((equal (car expr) :sivc-svar-expr)
    (list (cadr expr)))
   ((equal (car expr) :sivc-ssub)
    (sivc-svar-set-union
     (sivc-symbolic-expr-vars (cadr expr))
     (sivc-symbolic-expr-vars (caddr expr))))
   (t nil)))

(defun sivc-constraint-vars (constraint)
  (cond
   ((or
     (equal (car constraint) :sivc-ctrue)
     (equal (car constraint) :sivc-cfalse))
    nil)
   ((or
     (equal (car constraint) :sivc-ceq)
     (equal (car constraint) :sivc-cneq))
    (sivc-svar-set-union
     (sivc-symbolic-expr-vars (cadr constraint))
     (sivc-symbolic-expr-vars (caddr constraint))))
   ((equal (car constraint) :sivc-cconj)
    (sivc-svar-set-union
     (sivc-constraint-vars (cadr constraint))
     (sivc-constraint-vars (caddr constraint))))
   ((equal (car constraint) :sivc-cexists)
    (sivc-svar-set-insert
     (cadr constraint)
     (sivc-constraint-vars (caddr constraint))))
   (t nil)))

(defun sivc-interp-symbolic-expr (rho expr)
  (cond
   ((equal (car expr) :sivc-slit)
    (cadr expr))
   ((equal (car expr) :sivc-svar-expr)
    (sivc-rho-apply rho (cadr expr)))
   ((equal (car expr) :sivc-ssub)
    (-
     (sivc-interp-symbolic-expr rho (cadr expr))
     (sivc-interp-symbolic-expr rho (caddr expr))))
   (t 0)))

(defun sivc-is-solution-p (rho constraint)
  (cond
   ((equal (car constraint) :sivc-ctrue)
    t)
   ((equal (car constraint) :sivc-cfalse)
    nil)
   ((equal (car constraint) :sivc-ceq)
    (equal
     (sivc-interp-symbolic-expr rho (cadr constraint))
     (sivc-interp-symbolic-expr rho (caddr constraint))))
   ((equal (car constraint) :sivc-cneq)
    (not
     (equal
      (sivc-interp-symbolic-expr rho (cadr constraint))
      (sivc-interp-symbolic-expr rho (caddr constraint)))))
   ((equal (car constraint) :sivc-cconj)
    (and
     (sivc-is-solution-p rho (cadr constraint))
     (sivc-is-solution-p rho (caddr constraint))))
   ((equal (car constraint) :sivc-cexists)
    (sivc-is-solution-p rho (caddr constraint)))
   (t nil)))

;; Symbolic states are concrete records satisfying exactly the two source
;; invariants: constraint variables and sigma-range variables lie in vars.

(defun sivc-sigma-range-in-vars-p (bindings vars)
  (if (consp bindings)
      (and
       (member-equal (caddar bindings) vars)
       (sivc-sigma-range-in-vars-p
        (cdr bindings) vars))
    (equal bindings nil)))

(defun sivc-sym-state-p (st)
  (and
   (true-listp st)
   (equal (len st) 5)
   (equal (car st) :sivc-state)
   (sivc-sigma-p (cadr st))
   (sivc-constraint-p (caddr st))
   (sivc-rho-p (cadddr st))
   (sivc-svar-set-p (car (cddddr st)))
   (sivc-set-subset-p
    (sivc-constraint-vars (caddr st))
    (car (cddddr st)))
   (sivc-sigma-range-in-vars-p
    (caddr (cadr st))
    (car (cddddr st)))))

(defun sivc-state-sigma (st)
  (cadr st))

(defun sivc-state-constraint (st)
  (caddr st))

(defun sivc-state-rho (st)
  (cadddr st))

(defun sivc-state-vars (st)
  (car (cddddr st)))

(defun sivc-state-equiv-p (left right)
  (and
   (equal
    (cadr (sivc-state-sigma left))
    (cadr (sivc-state-sigma right)))
   (sivc-sigma-equiv-p
    (sivc-state-sigma left)
    (sivc-state-sigma right))
   (equal
    (sivc-state-constraint left)
    (sivc-state-constraint right))
   (sivc-rho-equiv-p
    (sivc-state-rho left)
    (sivc-state-rho right))
   (sivc-svar-set-equiv-p
    (sivc-state-vars left)
    (sivc-state-vars right))))

(defun sivc-state-member-p (st states)
  (if (consp states)
      (or
       (sivc-state-equiv-p st (car states))
       (sivc-state-member-p st (cdr states)))
    nil))

(defun sivc-state-list-p (xs)
  (if (consp xs)
      (and
       (sivc-sym-state-p (car xs))
       (sivc-state-list-p (cdr xs)))
    (equal xs nil)))

(defun sivc-state-no-duplicates-p (xs)
  (if (consp xs)
      (and
       (not (sivc-state-member-p (car xs) (cdr xs)))
       (sivc-state-no-duplicates-p (cdr xs)))
    (equal xs nil)))

(defun sivc-state-set-p (xs)
  (and
   (sivc-state-list-p xs)
   (sivc-state-no-duplicates-p xs)))

(defun sivc-state-set-subset-p (left right)
  (if (consp left)
      (and
       (sivc-state-member-p (car left) right)
       (sivc-state-set-subset-p (cdr left) right))
    (equal left nil)))

(defun sivc-state-set-equiv-p (left right)
  (and
   (sivc-state-set-subset-p left right)
   (sivc-state-set-subset-p right left)))

(defun sivc-state-set-insert (st states)
  (if (sivc-state-member-p st states)
      states
    (cons st states)))

(defun sivc-state-set-union (left right)
  (if (consp left)
      (sivc-state-set-insert
       (car left)
       (sivc-state-set-union (cdr left) right))
    right))

;; Environments are finite maps because compose has finite sigma support and
;; command execution only applies finitely many functional updates.

(defun sivc-environment-binding-p (binding)
  (and
   (true-listp binding)
   (equal (len binding) 3)
   (equal (car binding) :sivc-environment-binding)
   (sivc-program-var-p (cadr binding))
   (integerp (caddr binding))))

(defun sivc-environment-bindings-p (environment)
  (if (consp environment)
      (and
       (sivc-environment-binding-p (car environment))
       (sivc-environment-bindings-p (cdr environment)))
    (equal environment nil)))

(defun sivc-environment-key-member-p (key environment)
  (if (consp environment)
      (or
       (equal key (cadar environment))
       (sivc-environment-key-member-p
        key (cdr environment)))
    nil))

(defun sivc-environment-unique-keys-p (environment)
  (if (consp environment)
      (and
       (not
        (sivc-environment-key-member-p
         (cadar environment)
         (cdr environment)))
       (sivc-environment-unique-keys-p
        (cdr environment)))
    (equal environment nil)))

(defun sivc-environment-p (environment)
  (and
   (sivc-environment-bindings-p environment)
   (sivc-environment-unique-keys-p environment)))

(defun sivc-environment-get (environment program-var)
  (if (consp environment)
      (if (equal program-var (cadar environment))
          (sivc-some (caddar environment))
        (sivc-environment-get
         (cdr environment) program-var))
    nil))

(defun sivc-environment-update
    (environment program-var value)
  (if (consp environment)
      (if (equal program-var (cadar environment))
          (cons
           (list
            :sivc-environment-binding
            program-var
            value)
           (cdr environment))
        (cons
         (car environment)
         (sivc-environment-update
          (cdr environment) program-var value)))
    (list
     (list
      :sivc-environment-binding
      program-var
      value))))

(defun sivc-compose-bindings (rho bindings)
  (if (consp bindings)
      (cons
       (list
        :sivc-environment-binding
        (cadar bindings)
        (sivc-rho-apply rho (caddar bindings)))
       (sivc-compose-bindings rho (cdr bindings)))
    nil))

(defun sivc-compose-op (rho sigma)
  (sivc-compose-bindings rho (caddr sigma)))

(defun-sk sivc-environment-equiv-p (left right)
  (forall (program-var)
    (implies
     (sivc-program-var-p program-var)
     (equal
      (sivc-environment-get left program-var)
      (sivc-environment-get right program-var)))))

;; Deterministic evaluation of source expressions.

(defun sivc-eval-expr (environment expr)
  (cond
   ((equal (car expr) :sivc-elit)
    (list :sivc-enormal (cadr expr)))
   ((equal (car expr) :sivc-evar)
    (let ((entry
           (sivc-environment-get
            environment (cadr expr))))
      (if (equal entry nil)
          :sivc-eunbound
        (list :sivc-enormal (cadr entry)))))
   ((equal (car expr) :sivc-esub)
    (let ((left
           (sivc-eval-expr environment (cadr expr))))
      (if (equal left :sivc-eunbound)
          :sivc-eunbound
        (let ((right
               (sivc-eval-expr
                environment (caddr expr))))
          (if (equal right :sivc-eunbound)
              :sivc-eunbound
            (list
             :sivc-enormal
             (- (cadr left) (cadr right))))))))
   (t :sivc-eunbound)))

;; A structural upper bound supplies fuel only to make the mutually recursive
;; command/while semantics admissible in ACL2. It does not bound source data:
;; every loop-limit value and every finite command tree is represented.

(defun sivc-command-cost (command loop-limit)
  (cond
   ((or
     (equal (car command) :sivc-cskip)
     (equal (car command) :sivc-cassign))
    2)
   ((equal (car command) :sivc-cseq)
    (+
     2
     (sivc-command-cost (cadr command) loop-limit)
     (sivc-command-cost (caddr command) loop-limit)))
   ((equal (car command) :sivc-cif)
    (+
     2
     (sivc-command-cost (caddr command) loop-limit)
     (sivc-command-cost (cadddr command) loop-limit)))
   ((equal (car command) :sivc-cwhile)
    (+
     3
     (*
      (+ 1 (nfix loop-limit))
      (+
       2
       (sivc-command-cost
        (caddr command) loop-limit)))))
   (t 1)))

(defun sivc-run-result (environment behavior)
  (list :sivc-run-result environment behavior))

(defun sivc-run-result-p (result)
  (and
   (true-listp result)
   (equal (len result) 3)
   (equal (car result) :sivc-run-result)
   (sivc-environment-p (cadr result))
   (sivc-behavior-p (caddr result))))

(defun sivc-run
    (fuel mode loop-limit environment object counter)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (list :sivc-fuel-exhausted environment)
    (if (equal mode :sivc-command-mode)
        (cond
         ((equal (car object) :sivc-cskip)
          (sivc-run-result
           environment :sivc-normal))
         ((equal (car object) :sivc-cassign)
          (let ((value
                 (sivc-eval-expr
                  environment (caddr object))))
            (if (equal value :sivc-eunbound)
                (sivc-run-result
                 environment :sivc-unbound-var)
              (sivc-run-result
               (sivc-environment-update
                environment
                (cadr object)
                (cadr value))
               :sivc-normal))))
         ((equal (car object) :sivc-cseq)
          (let ((first
                 (sivc-run
                  (- fuel 1)
                  :sivc-command-mode
                  loop-limit
                  environment
                  (cadr object)
                  0)))
            (if
             (and
              (sivc-run-result-p first)
              (equal (caddr first) :sivc-normal))
             (sivc-run
              (- fuel 1)
              :sivc-command-mode
              loop-limit
              (cadr first)
              (caddr object)
              0)
             first)))
         ((equal (car object) :sivc-cif)
          (let ((test
                 (sivc-eval-expr
                  environment (cadr object))))
            (cond
             ((equal test :sivc-eunbound)
              (sivc-run-result
               environment :sivc-unbound-var))
             ((equal (cadr test) 0)
              (sivc-run
               (- fuel 1)
               :sivc-command-mode
               loop-limit
               environment
               (cadddr object)
               0))
             (t
              (sivc-run
               (- fuel 1)
               :sivc-command-mode
               loop-limit
               environment
               (caddr object)
               0)))))
         ((equal (car object) :sivc-cwhile)
          (sivc-run
           (- fuel 1)
           :sivc-while-mode
           loop-limit
           environment
           (list (cadr object) (caddr object))
           0))
         (t
          (list :sivc-fuel-exhausted environment)))
      (if (<= loop-limit counter)
          (sivc-run-result
           environment :sivc-loop-limit)
        (let ((test
               (sivc-eval-expr
                environment (car object))))
          (cond
           ((equal test :sivc-eunbound)
            (sivc-run-result
             environment :sivc-unbound-var))
           ((equal (cadr test) 0)
            (sivc-run-result
             environment :sivc-normal))
           (t
            (let ((body
                   (sivc-run
                    (- fuel 1)
                    :sivc-command-mode
                    loop-limit
                    environment
                    (cadr object)
                    0)))
              (if
               (and
                (sivc-run-result-p body)
                (equal (caddr body) :sivc-normal))
               (sivc-run
                (- fuel 1)
                :sivc-while-mode
                loop-limit
                (cadr body)
                object
                (+ counter 1))
               body)))))))))

(defun sivc-exec-cmd-p
    (loop-limit environment command output behavior)
  (and
   (integerp loop-limit)
   (<= 0 loop-limit)
   (sivc-environment-p environment)
   (sivc-command-p command)
   (sivc-environment-p output)
   (sivc-behavior-p behavior)
   (let ((result
          (sivc-run
           (sivc-command-cost command loop-limit)
           :sivc-command-mode
           loop-limit
           environment
           command
           0)))
     (and
      (sivc-run-result-p result)
      (equal behavior (caddr result))
      (sivc-environment-equiv-p
       output (cadr result))))))

(defun sivc-exec-while-p
    (loop-limit counter environment test body output behavior)
  (and
   (integerp loop-limit)
   (<= 0 loop-limit)
   (integerp counter)
   (sivc-environment-p environment)
   (sivc-expr-p test)
   (sivc-command-p body)
   (sivc-environment-p output)
   (sivc-behavior-p behavior)
   (let ((result
          (sivc-run
           (+
            2
            (*
             (+ 1 (nfix (- loop-limit counter)))
             (+
              2
              (sivc-command-cost body loop-limit))))
           :sivc-while-mode
           loop-limit
           environment
           (list test body)
           counter)))
     (and
      (sivc-run-result-p result)
      (equal behavior (caddr result))
      (sivc-environment-equiv-p
       output (cadr result))))))

;; Exact ACL2 rendering of state_extends and results_extend.

(defun-sk sivc-rho-agrees-on-state-vars-p
    (st state-prime)
  (forall (svar)
    (implies
     (sivc-svar-p svar)
     (implies
      (member-equal
       svar
       (sivc-state-vars st))
      (equal
       (sivc-rho-apply
        (sivc-state-rho st)
        svar)
       (sivc-rho-apply
        (sivc-state-rho state-prime)
        svar))))))

(defun sivc-state-extends-p (st state-prime)
  (and
   (sivc-set-subset-p
    (sivc-state-vars st)
    (sivc-state-vars state-prime))
   (sivc-rho-agrees-on-state-vars-p
    st state-prime)))

(defun sivc-result-member-p
    (st behavior normals unbounds limits)
  (cond
   ((equal behavior :sivc-normal)
    (sivc-state-member-p st normals))
   ((equal behavior :sivc-unbound-var)
    (sivc-state-member-p st unbounds))
   ((equal behavior :sivc-loop-limit)
    (sivc-state-member-p st limits))
   (t nil)))

(defun-sk sivc-results-extend-p
    (st normals unbounds limits)
  (forall (state-prime)
    (implies
     (sivc-sym-state-p state-prime)
     (implies
      (or
       (sivc-state-member-p state-prime normals)
       (sivc-state-member-p state-prime unbounds)
       (sivc-state-member-p state-prime limits))
      (sivc-state-extends-p
       st state-prime)))))

;; Forward symbolic coverage for one concrete execution retains the source
;; result state as an internal existential witness.

(defun-sk sivc-output-covered-p
    (output behavior normals unbounds limits)
  (exists (state-prime)
    (and
     (sivc-sym-state-p state-prime)
     (sivc-result-member-p
      state-prime behavior normals unbounds limits)
     (sivc-is-solution-p
      (sivc-state-rho state-prime)
      (sivc-state-constraint state-prime))
     (sivc-environment-equiv-p
      output
      (sivc-compose-op
       (sivc-state-rho state-prime)
       (sivc-state-sigma state-prime))))))

(defun-sk sivc-all-executions-covered-p
    (source-state loop-limit command normals unbounds limits)
  (forall (output behavior)
    (implies
     (and
      (sivc-environment-p output)
      (sivc-behavior-p behavior))
     (implies
      (sivc-exec-cmd-p
       loop-limit
       (sivc-compose-op
        (sivc-state-rho source-state)
        (sivc-state-sigma source-state))
       command
       output
      behavior)
      (sivc-output-covered-p
       output behavior normals unbounds limits)))))

;; The first match branch contains the recursive-call measure implication,
;; not the reverse-simulation postcondition used later in the theorem.

(defun-sk sivc-head-measure-condition-p
    (st loop-limit command full-list tail
           normals unbounds limits)
  (forall (behavior state-prime)
    (implies
     (and
      (sivc-behavior-p behavior)
      (sivc-sym-state-p state-prime))
     (implies
      (sivc-result-member-p
       state-prime behavior normals unbounds limits)
      (implies
       (sivc-is-solution-p
        (sivc-state-rho state-prime)
        (sivc-state-constraint state-prime))
       (implies
        (and
         (sivc-is-solution-p
          (sivc-state-rho st)
          (sivc-state-constraint st))
         (sivc-exec-cmd-p
          loop-limit
          (sivc-compose-op
           (sivc-state-rho st)
           (sivc-state-sigma st))
          command
          (sivc-compose-op
           (sivc-state-rho state-prime)
           (sivc-state-sigma state-prime))
          behavior))
        (and
         (and
          (<= 0 (len full-list))
          (< (len tail) (len full-list)))
         (<= 0 loop-limit))))))))

(defun-sk sivc-all-head-result-sets-measured-p
    (st loop-limit command full-list tail)
  (forall (normals unbounds limits)
    (implies
     (and
      (sivc-state-set-p normals)
      (sivc-state-set-p unbounds)
      (sivc-state-set-p limits))
     (and
      (sivc-results-extend-p
       st normals unbounds limits)
      (implies
       (sivc-is-solution-p
        (sivc-state-rho st)
        (sivc-state-constraint st))
       (sivc-all-executions-covered-p
        st loop-limit command normals unbounds limits))
      (sivc-head-measure-condition-p
       st loop-limit command full-list tail
       normals unbounds limits)))))

(defun sivc-first-match-obligation-p
    (loop-limit states command)
  (if (endp states)
      t
    (let ((st (car states))
          (tail (cdr states)))
      (and
       (and
        (and
         (<= 0 (len states))
         (< 0 (len states)))
        (<= 0 loop-limit))
       (sivc-all-head-result-sets-measured-p
        st loop-limit command states tail)))))

;; Reverse simulation for the head result sets in the nonempty premise.

(defun-sk sivc-head-reverse-simulation-p
    (st loop-limit command normals unbounds limits)
  (forall (behavior state-prime)
    (implies
     (and
      (sivc-behavior-p behavior)
      (sivc-sym-state-p state-prime))
     (implies
      (sivc-result-member-p
       state-prime behavior normals unbounds limits)
      (implies
       (sivc-is-solution-p
        (sivc-state-rho state-prime)
        (sivc-state-constraint state-prime))
       (and
        (sivc-is-solution-p
         (sivc-state-rho st)
         (sivc-state-constraint st))
        (sivc-exec-cmd-p
         loop-limit
         (sivc-compose-op
          (sivc-state-rho st)
          (sivc-state-sigma st))
         command
         (sivc-compose-op
          (sivc-state-rho state-prime)
          (sivc-state-sigma state-prime))
         behavior)))))))

(defun sivc-head-result-correct-p
    (st loop-limit command normals unbounds limits)
  (and
   (sivc-results-extend-p
    st normals unbounds limits)
   (implies
    (sivc-is-solution-p
     (sivc-state-rho st)
     (sivc-state-constraint st))
    (sivc-all-executions-covered-p
     st loop-limit command normals unbounds limits))
   (sivc-head-reverse-simulation-p
    st loop-limit command normals unbounds limits)))

;; The following three predicates are the exact combined result
;; postcondition for an arbitrary source list.

(defun-sk sivc-extending-origin-exists-p
    (source-states state-prime)
  (exists (st)
    (and
     (sivc-sym-state-p st)
     (sivc-state-member-p st source-states)
     (sivc-state-extends-p
      st state-prime))))

(defun-sk sivc-all-results-extend-an-origin-p
    (source-states normals unbounds limits)
  (forall (state-prime)
    (implies
     (sivc-sym-state-p state-prime)
     (implies
      (or
       (sivc-state-member-p state-prime normals)
       (sivc-state-member-p state-prime unbounds)
       (sivc-state-member-p state-prime limits))
      (sivc-extending-origin-exists-p
       source-states state-prime)))))

(defun-sk sivc-all-source-executions-covered-p
    (source-states loop-limit command normals unbounds limits)
  (forall (st)
    (implies
     (sivc-sym-state-p st)
     (implies
      (sivc-state-member-p st source-states)
      (implies
       (sivc-is-solution-p
        (sivc-state-rho st)
        (sivc-state-constraint st))
       (sivc-all-executions-covered-p
        st loop-limit command normals unbounds limits))))))

(defun-sk sivc-reverse-origin-exists-p
    (source-states loop-limit command behavior state-prime)
  (exists (st)
    (and
     (sivc-sym-state-p st)
     (sivc-state-member-p st source-states)
     (sivc-is-solution-p
      (sivc-state-rho st)
      (sivc-state-constraint st))
     (sivc-exec-cmd-p
      loop-limit
      (sivc-compose-op
       (sivc-state-rho st)
       (sivc-state-sigma st))
      command
      (sivc-compose-op
       (sivc-state-rho state-prime)
       (sivc-state-sigma state-prime))
      behavior))))

(defun-sk sivc-all-results-have-an-origin-p
    (source-states loop-limit command normals unbounds limits)
  (forall (behavior state-prime)
    (implies
     (and
      (sivc-behavior-p behavior)
      (sivc-sym-state-p state-prime))
     (implies
      (sivc-result-member-p
       state-prime behavior normals unbounds limits)
      (implies
       (sivc-is-solution-p
        (sivc-state-rho state-prime)
        (sivc-state-constraint state-prime))
       (sivc-reverse-origin-exists-p
        source-states loop-limit command
        behavior state-prime))))))

(defun sivc-result-summary-p
    (source-states loop-limit command normals unbounds limits)
  (and
   (sivc-all-results-extend-an-origin-p
    source-states normals unbounds limits)
   (sivc-all-source-executions-covered-p
    source-states loop-limit command normals unbounds limits)
   (sivc-all-results-have-an-origin-p
    source-states loop-limit command normals unbounds limits)))

;; Exact field equality for the source symbolic-state record.  Sigma, rho,
;; and finite-set fields are compared by their source extensional equalities.

(defun sivc-state-fields-equal-p
    (st sigma constraint rho vars)
  (and
   (equal
    (cadr (sivc-state-sigma st))
    (cadr sigma))
   (sivc-sigma-equiv-p
    (sivc-state-sigma st) sigma)
   (equal
    (sivc-state-constraint st)
    constraint)
   (sivc-rho-equiv-p
    (sivc-state-rho st) rho)
   (sivc-svar-set-equiv-p
    (sivc-state-vars st) vars)))

(defun sivc-state-fields-valid-p
    (sigma constraint rho vars)
  (and
   (sivc-sigma-p sigma)
   (sivc-constraint-p constraint)
   (sivc-rho-p rho)
   (sivc-svar-set-p vars)
   (sivc-set-subset-p
    (sivc-constraint-vars constraint)
    vars)
   (sivc-sigma-range-in-vars-p
    (caddr sigma) vars)))

(defun-sk sivc-sigma-other-lookups-unchanged-p
    (old new assigned-var)
  (forall (program-var)
    (implies
     (sivc-program-var-p program-var)
     (implies
      (not (equal program-var assigned-var))
      (equal
       (sivc-sigma-get new program-var)
       (sivc-sigma-get old program-var))))))

(defun sivc-sigma-set-laws-p
    (old new assigned-var fresh-var)
  (and
   (equal
    (sivc-sigma-get new assigned-var)
    (sivc-some fresh-var))
   (sivc-sigma-other-lookups-unchanged-p
    old new assigned-var)))

(defun-sk sivc-program-var-mapping-exists-p (st svar)
  (exists (program-var)
    (and
     (sivc-program-var-p program-var)
     (equal
      (sivc-sigma-get
       (sivc-state-sigma st)
       program-var)
      (sivc-some svar)))))

(defun-sk sivc-symbolic-expr-mapped-p (st symbolic-expr)
  (forall (svar)
    (implies
     (sivc-svar-p svar)
     (implies
      (member-equal
       svar
       (sivc-symbolic-expr-vars symbolic-expr))
      (sivc-program-var-mapping-exists-p st svar)))))

(defun sivc-symbolic-eval-normal-p
    (st expr symbolic-expr)
  (equal
   (sivc-eval-expr
    (sivc-compose-op
     (sivc-state-rho st)
     (sivc-state-sigma st))
    expr)
   (list
    :sivc-enormal
    (sivc-interp-symbolic-expr
     (sivc-state-rho st)
     symbolic-expr))))

(defun-sk sivc-constraint-solution-equiv-p
    (left right)
  (forall (rho)
    (implies
     (sivc-rho-p rho)
     (iff
      (sivc-is-solution-p rho left)
      (sivc-is-solution-p rho right)))))

(defun-sk sivc-old-binding-rewrite-p
    (st assigned-var constraint-prime constraint)
  (exists (old-svar)
    (and
     (sivc-svar-p old-svar)
     (equal
      (sivc-sigma-get
       (sivc-state-sigma st)
       assigned-var)
      (sivc-some old-svar))
     (sivc-constraint-solution-equiv-p
      constraint-prime
      (list :sivc-cexists old-svar constraint))
     (sivc-set-subset-p
      (sivc-constraint-vars constraint-prime)
      (sivc-constraint-vars
       (list :sivc-cexists old-svar constraint))))))

(defun sivc-constraint-rewrite-premise-p
    (st assigned-var fresh-var symbolic-expr constraint-prime)
  (let ((constraint
         (list
          :sivc-cconj
          (sivc-state-constraint st)
          (list
           :sivc-ceq
           (list :sivc-svar-expr fresh-var)
           symbolic-expr))))
    (or
     (sivc-old-binding-rewrite-p
      st assigned-var constraint-prime constraint)
     (and
      (equal
       (sivc-sigma-get
        (sivc-state-sigma st)
        assigned-var)
       nil)
      (equal constraint-prime constraint)))))

(defun sivc-vars-add-premise-p
    (old-vars fresh-var vars-prime)
  (and
   (sivc-svar-set-equiv-p
    vars-prime
    (sivc-svar-set-insert
     fresh-var old-vars))
   (if (member-equal fresh-var old-vars)
       (equal
        (len vars-prime)
        (len old-vars))
     (equal
      (len vars-prime)
      (+ 1 (len old-vars))))))

(defun sivc-assignment-vars-conclusion-p
    (sigma-prime constraint-prime vars-prime)
  (and
   (sivc-set-subset-p
    (sivc-constraint-vars constraint-prime)
    vars-prime)
   (sivc-sigma-range-in-vars-p
    (caddr sigma-prime)
    vars-prime)))

(defun-sk sivc-all-assignment-vars-obligations-p
    (st fresh-var sigma-prime constraint-prime)
  (forall (vars-prime)
    (implies
     (sivc-svar-set-p vars-prime)
     (implies
      (sivc-vars-add-premise-p
       (sivc-state-vars st)
       fresh-var
       vars-prime)
      (sivc-assignment-vars-conclusion-p
       sigma-prime
       constraint-prime
       vars-prime)))))

(defun-sk sivc-all-constraint-rewrite-obligations-p
    (st assigned-var fresh-var symbolic-expr sigma-prime)
  (forall (constraint-prime)
    (implies
     (sivc-constraint-p constraint-prime)
     (implies
      (sivc-constraint-rewrite-premise-p
       st assigned-var fresh-var
       symbolic-expr constraint-prime)
      (sivc-all-assignment-vars-obligations-p
       st fresh-var sigma-prime constraint-prime)))))

(defun-sk sivc-all-fresh-assignment-obligations-p
    (st assigned-var symbolic-expr)
  (forall (fresh-var)
    (implies
     (sivc-svar-p fresh-var)
     (implies
      (not
       (member-equal
        fresh-var
        (sivc-state-vars st)))
      (let ((sigma-prime
             (sivc-sigma-set
              (sivc-state-sigma st)
              assigned-var
              fresh-var)))
        (implies
         (sivc-sigma-set-laws-p
          (sivc-state-sigma st)
          sigma-prime
          assigned-var
          fresh-var)
         (sivc-all-constraint-rewrite-obligations-p
          st assigned-var fresh-var
          symbolic-expr sigma-prime)))))))

(defun-sk sivc-assignment-first-obligation-p
    (st assigned-var expr)
  (forall (symbolic-expr)
    (implies
     (sivc-symbolic-expr-p symbolic-expr)
     (implies
      (and
       (sivc-symbolic-eval-normal-p
        st expr symbolic-expr)
       (sivc-symbolic-expr-mapped-p
        st symbolic-expr))
      (sivc-all-fresh-assignment-obligations-p
       st assigned-var symbolic-expr)))))

;; This is the source match used to justify structurally recursive calls.

(defun sivc-direct-subcommand-p (command target)
  (cond
   ((equal (car command) :sivc-cseq)
    (or
     (equal (cadr command) target)
     (equal (caddr command) target)))
   ((equal (car command) :sivc-cif)
    (or
     (equal (caddr command) target)
     (equal (cadddr command) target)))
   ((equal (car command) :sivc-cwhile)
    (equal (caddr command) target))
   (t nil)))

(defun-sk sivc-sequence-first-obligation-p
    (st loop-limit command first second)
  (forall (normals1 unbounds1 limits1)
    (implies
     (and
      (sivc-state-set-p normals1)
      (sivc-state-set-p unbounds1)
      (sivc-state-set-p limits1))
     (implies
      (and
       (sivc-results-extend-p
        st normals1 unbounds1 limits1)
       (implies
        (sivc-is-solution-p
         (sivc-state-rho st)
         (sivc-state-constraint st))
        (sivc-all-executions-covered-p
         st loop-limit first
         normals1 unbounds1 limits1))
       (sivc-head-reverse-simulation-p
        st loop-limit first
        normals1 unbounds1 limits1))
      (and
       (or
        (sivc-direct-subcommand-p command second)
        (and
         (equal command second)
         (<= 0 0)
         (< (len normals1) 0)))
       (<= 0 loop-limit))))))

(defun-sk sivc-no-solutions-p (st)
  (forall (rho)
    (implies
     (sivc-rho-p rho)
     (not
      (sivc-is-solution-p
       rho
       (sivc-state-constraint st))))))

(defun sivc-empty-state-sets-p
    (normals unbounds limits)
  (and
   (and
    (sivc-state-set-equiv-p limits nil)
    (equal (len limits) 0))
   (and
    (sivc-state-set-equiv-p unbounds nil)
    (equal (len unbounds) 0))
   (sivc-state-set-equiv-p normals nil)
   (equal (len normals) 0)))

(defun-sk sivc-branch-result-choice-p
    (st loop-limit branch normals unbounds limits)
  (exists (enabled)
    (and
     (booleanp enabled)
     (implies
      (not enabled)
      (sivc-no-solutions-p st))
     (if enabled
         (sivc-head-result-correct-p
          st loop-limit branch
          normals unbounds limits)
       (sivc-empty-state-sets-p
        normals unbounds limits)))))

(defun-sk sivc-all-first-branch-result-sets-p
    (state1 loop-limit command else-command)
  (forall (normals1 unbounds1 limits1)
    (implies
     (and
      (sivc-state-set-p normals1)
      (sivc-state-set-p unbounds1)
      (sivc-state-set-p limits1))
     (implies
      (sivc-branch-result-choice-p
       state1 loop-limit
       (caddr command)
       normals1 unbounds1 limits1)
      (and
       (sivc-direct-subcommand-p
        command else-command)
       (<= 0 loop-limit))))))

(defun-sk sivc-all-second-branch-states-p
    (state1 st symbolic-expr loop-limit
            command then-command else-command)
  (forall (state2)
    (implies
     (sivc-sym-state-p state2)
     (let ((zero-constraint
            (list
             :sivc-cconj
             (sivc-state-constraint st)
             (list
              :sivc-ceq
              symbolic-expr
              (list :sivc-slit 0)))))
       (implies
        (sivc-state-fields-equal-p
         state2
         (sivc-state-sigma st)
         zero-constraint
         (sivc-state-rho st)
         (sivc-state-vars st))
        (and
         (and
          (sivc-direct-subcommand-p
           command then-command)
          (<= 0 loop-limit))
         (sivc-all-first-branch-result-sets-p
          state1 loop-limit command else-command)))))))

(defun-sk sivc-all-first-branch-states-p
    (st symbolic-expr loop-limit
        command then-command else-command)
  (forall (state1)
    (implies
     (sivc-sym-state-p state1)
     (let ((nonzero-constraint
            (list
             :sivc-cconj
             (sivc-state-constraint st)
             (list
              :sivc-cneq
              symbolic-expr
              (list :sivc-slit 0)))))
       (implies
        (sivc-state-fields-equal-p
         state1
         (sivc-state-sigma st)
         nonzero-constraint
         (sivc-state-rho st)
         (sivc-state-vars st))
        (sivc-all-second-branch-states-p
         state1 st symbolic-expr loop-limit
         command then-command else-command))))))

(defun-sk sivc-conditional-first-obligation-p
    (st loop-limit command test then-command else-command)
  (forall (symbolic-expr)
    (implies
     (sivc-symbolic-expr-p symbolic-expr)
     (implies
      (and
       (sivc-symbolic-eval-normal-p
        st test symbolic-expr)
       (sivc-symbolic-expr-mapped-p
        st symbolic-expr))
      (let ((nonzero-constraint
             (list
              :sivc-cconj
              (sivc-state-constraint st)
              (list
               :sivc-cneq
               symbolic-expr
               (list :sivc-slit 0))))
            (zero-constraint
             (list
              :sivc-cconj
              (sivc-state-constraint st)
              (list
               :sivc-ceq
               symbolic-expr
               (list :sivc-slit 0)))))
        (and
         (sivc-state-fields-valid-p
          (sivc-state-sigma st)
          nonzero-constraint
          (sivc-state-rho st)
          (sivc-state-vars st))
         (sivc-state-fields-valid-p
          (sivc-state-sigma st)
          zero-constraint
          (sivc-state-rho st)
          (sivc-state-vars st))
         (sivc-all-first-branch-states-p
          st symbolic-expr loop-limit
          command then-command else-command)))))))

(defun sivc-first-command-obligation-p
    (loop-limit command st)
  (cond
   ((equal (car command) :sivc-cskip)
    t)
   ((equal (car command) :sivc-cassign)
    (sivc-assignment-first-obligation-p
     st (cadr command) (caddr command)))
   ((equal (car command) :sivc-cseq)
    (and
     (sivc-direct-subcommand-p
      command (cadr command))
     (<= 0 loop-limit)
     (sivc-sequence-first-obligation-p
      st loop-limit command
      (cadr command)
      (caddr command))))
   ((equal (car command) :sivc-cif)
    (sivc-conditional-first-obligation-p
     st loop-limit command
     (cadr command)
     (caddr command)
     (cadddr command)))
   ((equal (car command) :sivc-cwhile)
    (and
     (or
      (sivc-direct-subcommand-p command command)
      (and
       (equal command command)
       (<= 0 (+ loop-limit 1))
       (< (- loop-limit 0)
          (+ loop-limit 1))))
     (<= 0 0)
     (<= 0 loop-limit)))
   (t nil)))

;; The second half of the VC describes the result sets produced by each
;; command constructor and then demands the common semantic postcondition.

(defun sivc-singleton-state-set-p (states st)
  (and
   (sivc-state-set-equiv-p states (list st))
   (equal (len states) 1)))

(defun-sk sivc-assignment-normal-result-p
    (st assigned-var expr normals unbounds limits)
  (exists
    (symbolic-expr fresh-var constraint-prime
                   vars-prime state-prime)
    (and
     (sivc-symbolic-expr-p symbolic-expr)
     (sivc-svar-p fresh-var)
     (sivc-constraint-p constraint-prime)
     (sivc-svar-set-p vars-prime)
     (sivc-sym-state-p state-prime)
     (sivc-symbolic-eval-normal-p
      st expr symbolic-expr)
     (sivc-symbolic-expr-mapped-p
      st symbolic-expr)
     (not
      (member-equal
       fresh-var
       (sivc-state-vars st)))
     (let ((sigma-prime
            (sivc-sigma-set
             (sivc-state-sigma st)
             assigned-var
             fresh-var)))
       (and
        (sivc-sigma-set-laws-p
         (sivc-state-sigma st)
         sigma-prime
         assigned-var
         fresh-var)
        (sivc-constraint-rewrite-premise-p
         st assigned-var fresh-var
         symbolic-expr constraint-prime)
        (sivc-vars-add-premise-p
         (sivc-state-vars st)
         fresh-var vars-prime)
        (sivc-state-fields-equal-p
         state-prime
         sigma-prime
         constraint-prime
         (sivc-rho-update
          (sivc-state-rho st)
          fresh-var
          (sivc-interp-symbolic-expr
           (sivc-state-rho st)
           symbolic-expr))
         vars-prime)
        (sivc-empty-state-sets-p
         nil unbounds limits)
        (sivc-singleton-state-set-p
         normals state-prime))))))

(defun sivc-assignment-unbound-result-p
    (st expr normals unbounds limits)
  (and
   (equal
    (sivc-eval-expr
     (sivc-compose-op
      (sivc-state-rho st)
      (sivc-state-sigma st))
     expr)
    :sivc-eunbound)
   (sivc-state-set-equiv-p limits nil)
   (equal (len limits) 0)
   (sivc-singleton-state-set-p unbounds st)
   (sivc-state-set-equiv-p normals nil)
   (equal (len normals) 0)))

(defun-sk sivc-sequence-result-premise-p
    (st loop-limit first second normals unbounds limits)
  (exists (normals1 unbounds1 limits1 unbounds2 limits2)
    (and
     (sivc-state-set-p normals1)
     (sivc-state-set-p unbounds1)
     (sivc-state-set-p limits1)
     (sivc-state-set-p unbounds2)
     (sivc-state-set-p limits2)
     (sivc-head-result-correct-p
      st loop-limit first
      normals1 unbounds1 limits1)
     (sivc-result-summary-p
      normals1 loop-limit second
      normals unbounds2 limits2)
     (sivc-state-set-equiv-p
      limits
      (sivc-state-set-union
       limits1 limits2))
     (sivc-state-set-equiv-p
      unbounds
      (sivc-state-set-union
       unbounds1 unbounds2)))))

(defun-sk sivc-conditional-normal-result-p
    (st loop-limit test then-command else-command
        normals unbounds limits)
  (exists
    (symbolic-expr state1 state2
                   normals1 unbounds1 limits1
                   normals2 unbounds2 limits2)
    (and
     (sivc-symbolic-expr-p symbolic-expr)
     (sivc-sym-state-p state1)
     (sivc-sym-state-p state2)
     (sivc-state-set-p normals1)
     (sivc-state-set-p unbounds1)
     (sivc-state-set-p limits1)
     (sivc-state-set-p normals2)
     (sivc-state-set-p unbounds2)
     (sivc-state-set-p limits2)
     (sivc-symbolic-eval-normal-p
      st test symbolic-expr)
     (sivc-symbolic-expr-mapped-p
      st symbolic-expr)
     (sivc-state-fields-equal-p
      state1
      (sivc-state-sigma st)
      (list
       :sivc-cconj
       (sivc-state-constraint st)
       (list
        :sivc-cneq
        symbolic-expr
        (list :sivc-slit 0)))
      (sivc-state-rho st)
      (sivc-state-vars st))
     (sivc-state-fields-equal-p
      state2
      (sivc-state-sigma st)
      (list
       :sivc-cconj
       (sivc-state-constraint st)
       (list
        :sivc-ceq
        symbolic-expr
        (list :sivc-slit 0)))
      (sivc-state-rho st)
      (sivc-state-vars st))
     (sivc-branch-result-choice-p
      state1 loop-limit then-command
      normals1 unbounds1 limits1)
     (sivc-branch-result-choice-p
      state2 loop-limit else-command
      normals2 unbounds2 limits2)
     (sivc-state-set-equiv-p
      limits
      (sivc-state-set-union
       limits1 limits2))
     (sivc-state-set-equiv-p
      unbounds
      (sivc-state-set-union
       unbounds1 unbounds2))
     (sivc-state-set-equiv-p
      normals
      (sivc-state-set-union
       normals1 normals2)))))

(defun sivc-conditional-unbound-result-p
    (st test normals unbounds limits)
  (and
   (equal
    (sivc-eval-expr
     (sivc-compose-op
      (sivc-state-rho st)
      (sivc-state-sigma st))
     test)
    :sivc-eunbound)
   (sivc-state-set-equiv-p limits nil)
   (equal (len limits) 0)
   (sivc-singleton-state-set-p unbounds st)
   (sivc-state-set-equiv-p normals nil)
   (equal (len normals) 0)))

(defun-sk sivc-while-output-covered-p
    (output behavior normals unbounds limits)
  (exists (state-prime)
    (and
     (sivc-sym-state-p state-prime)
     (sivc-result-member-p
      state-prime behavior normals unbounds limits)
     (sivc-is-solution-p
      (sivc-state-rho state-prime)
      (sivc-state-constraint state-prime))
     (sivc-environment-equiv-p
      output
      (sivc-compose-op
       (sivc-state-rho state-prime)
       (sivc-state-sigma state-prime))))))

(defun-sk sivc-all-while-executions-covered-p
    (st loop-limit test body normals unbounds limits)
  (forall (output behavior)
    (implies
     (and
      (sivc-environment-p output)
      (sivc-behavior-p behavior))
     (implies
      (sivc-exec-while-p
       loop-limit 0
       (sivc-compose-op
        (sivc-state-rho st)
        (sivc-state-sigma st))
       test body output behavior)
      (sivc-while-output-covered-p
       output behavior normals unbounds limits)))))

(defun-sk sivc-while-reverse-simulation-p
    (st loop-limit test body normals unbounds limits)
  (forall (behavior state-prime)
    (implies
     (and
      (sivc-behavior-p behavior)
      (sivc-sym-state-p state-prime))
     (implies
      (sivc-result-member-p
       state-prime behavior normals unbounds limits)
      (implies
       (sivc-is-solution-p
        (sivc-state-rho state-prime)
        (sivc-state-constraint state-prime))
       (and
        (sivc-is-solution-p
         (sivc-state-rho st)
         (sivc-state-constraint st))
        (sivc-exec-while-p
         loop-limit 0
         (sivc-compose-op
          (sivc-state-rho st)
          (sivc-state-sigma st))
         test body
         (sivc-compose-op
          (sivc-state-rho state-prime)
          (sivc-state-sigma state-prime))
         behavior)))))))

(defun sivc-while-result-correct-p
    (st loop-limit test body normals unbounds limits)
  (and
   (sivc-results-extend-p
    st normals unbounds limits)
   (implies
    (sivc-is-solution-p
     (sivc-state-rho st)
     (sivc-state-constraint st))
    (sivc-all-while-executions-covered-p
     st loop-limit test body
     normals unbounds limits))
   (sivc-while-reverse-simulation-p
    st loop-limit test body
    normals unbounds limits)))

(defun sivc-command-result-premise-p
    (st loop-limit command normals unbounds limits)
  (cond
   ((equal (car command) :sivc-cskip)
    (and
     (sivc-state-set-equiv-p limits nil)
     (equal (len limits) 0)
     (sivc-state-set-equiv-p unbounds nil)
     (equal (len unbounds) 0)
     (sivc-singleton-state-set-p normals st)))
   ((equal (car command) :sivc-cassign)
    (or
     (sivc-assignment-normal-result-p
      st (cadr command) (caddr command)
      normals unbounds limits)
     (sivc-assignment-unbound-result-p
      st (caddr command)
      normals unbounds limits)))
   ((equal (car command) :sivc-cseq)
    (sivc-sequence-result-premise-p
     st loop-limit
     (cadr command)
     (caddr command)
     normals unbounds limits))
   ((equal (car command) :sivc-cif)
    (or
     (sivc-conditional-normal-result-p
      st loop-limit
      (cadr command)
      (caddr command)
      (cadddr command)
      normals unbounds limits)
     (sivc-conditional-unbound-result-p
      st (cadr command)
      normals unbounds limits)))
   ((equal (car command) :sivc-cwhile)
    (sivc-while-result-correct-p
     st loop-limit
     (cadr command)
     (caddr command)
     normals unbounds limits))
   (t nil)))

(defun-sk sivc-all-command-result-sets-p
    (st loop-limit command)
  (forall (normals unbounds limits)
    (implies
     (and
      (sivc-state-set-p normals)
      (sivc-state-set-p unbounds)
      (sivc-state-set-p limits))
     (implies
      (sivc-command-result-premise-p
       st loop-limit command
       normals unbounds limits)
      (sivc-head-result-correct-p
       st loop-limit command
       normals unbounds limits)))))

(defun
  ntp4vc-pearl-imp-symbolicinterpreter-symbolic-interp-cmdqtvc-statement
  (loop-limit command st)
  (implies
   (and
    (integerp loop-limit)
    (sivc-command-p command)
    (sivc-sym-state-p st)
    (<= 0 loop-limit))
   (and
    (sivc-first-command-obligation-p
     loop-limit command st)
    (sivc-all-command-result-sets-p
     st loop-limit command))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
