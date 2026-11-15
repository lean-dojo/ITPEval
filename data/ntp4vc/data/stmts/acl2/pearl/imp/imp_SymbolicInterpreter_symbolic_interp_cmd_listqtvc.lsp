;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/imp/imp_SymbolicInterpreter_symbolic_interp_cmd_listqtvc: the
;; list-level symbolic-interpreter verification condition, with concrete
;; expression, command, constraint, symbolic-state, and bounded-execution
;; semantics for normal, unbound-variable, and loop-limit results.
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

;; A valuation is a handle for an arbitrary total function from symbolic
;; variables to integers.  This is the one generic operation symbol retained
;; from the source's function type; IFIX makes its codomain total and typed.

(defstub sivc-rho-raw (handle svar) t)

(defun sivc-rho-p (rho)
  (and
   (true-listp rho)
   (equal (len rho) 2)
   (equal (car rho) :sivc-rho)))

(defun sivc-rho-apply (rho svar)
  (ifix (sivc-rho-raw (cadr rho) svar)))

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

;; The head call's reverse-simulation postcondition is part of the premise
;; from which the recursive-call measure follows.

(defun-sk sivc-head-measure-condition-p
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

(defun-sk sivc-all-head-result-sets-measured-p
    (st loop-limit command full-list tail)
  (forall (normals unbounds limits)
    (implies
     (and
      (sivc-state-set-p normals)
      (sivc-state-set-p unbounds)
      (sivc-state-set-p limits))
     (implies
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
        st loop-limit command normals unbounds limits))
      (and
       (and
        (<= 0 (len full-list))
        (< (len tail) (len full-list)))
       (<= 0 loop-limit))))))

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

;; The recursive-tail premise keeps all three tail result sets existential and
;; requires the final sets to be their finite-set unions with the head sets.

(defun-sk sivc-nonempty-result-premise-p
    (st tail loop-limit command normals unbounds limits)
  (exists
    (normals1 unbounds1 limits1 normals2 unbounds2 limits2)
    (and
     (sivc-state-set-p normals1)
     (sivc-state-set-p unbounds1)
     (sivc-state-set-p limits1)
     (sivc-state-set-p normals2)
     (sivc-state-set-p unbounds2)
     (sivc-state-set-p limits2)
     (sivc-head-result-correct-p
      st loop-limit command normals1 unbounds1 limits1)
     (sivc-result-summary-p
      tail loop-limit command normals2 unbounds2 limits2)
     (sivc-state-set-equiv-p
      limits
      (sivc-state-set-union limits1 limits2))
     (sivc-state-set-equiv-p
      unbounds
      (sivc-state-set-union unbounds1 unbounds2))
     (sivc-state-set-equiv-p
      normals
      (sivc-state-set-union normals1 normals2)))))

(defun sivc-empty-result-premise-p
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

(defun sivc-result-premise-p
    (states loop-limit command normals unbounds limits)
  (if (endp states)
      (sivc-empty-result-premise-p
       normals unbounds limits)
    (sivc-nonempty-result-premise-p
     (car states)
     (cdr states)
     loop-limit command normals unbounds limits)))

(defun-sk sivc-all-final-result-sets-p
    (states loop-limit command)
  (forall (normals unbounds limits)
    (implies
     (and
      (sivc-state-set-p normals)
      (sivc-state-set-p unbounds)
      (sivc-state-set-p limits))
     (implies
      (sivc-result-premise-p
       states loop-limit command normals unbounds limits)
      (sivc-result-summary-p
       states loop-limit command normals unbounds limits)))))

(defun
  ntp4vc-pearl-imp-symbolicinterpreter-symbolic-interp-cmd-listqtvc-statement
  (loop-limit states command)
  (implies
   (and
    (integerp loop-limit)
    (sivc-state-list-p states)
    (sivc-command-p command)
    (<= 0 loop-limit))
   (and
    (sivc-first-match-obligation-p
     loop-limit states command)
    (sivc-all-final-result-sets-p
     states loop-limit command))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
