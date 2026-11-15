;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/register_allocation_FiniteNumberOfRegisters_compileqtvc: the
;; finite-register expression compiler verification condition, including
;; direct register allocation, stack spilling, and double-WP correctness.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Addresses form an arbitrary inhabited carrier. Expressions and
;; instructions are represented bijectively by their source constructors.

(defun fra-addr-p (value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (equal (car value) :fra-addr)))

(defun fra-expr-p (expr)
  (declare (xargs :measure (acl2-count expr)))
  (and
   (consp expr)
   (cond
    ((equal (car expr) :fra-evar)
     (and
      (true-listp expr)
      (equal (len expr) 2)
      (fra-addr-p (cadr expr))))
    ((equal (car expr) :fra-eneg)
     (and
      (true-listp expr)
      (equal (len expr) 2)
      (fra-expr-p (cadr expr))))
    ((equal (car expr) :fra-eadd)
     (and
      (true-listp expr)
      (equal (len expr) 3)
      (fra-expr-p (cadr expr))
      (fra-expr-p (caddr expr))))
    (t nil))))

(defun fra-instr-p (instr)
  (and
   (consp instr)
   (cond
    ((equal (car instr) :fra-iload)
     (and
      (true-listp instr)
      (equal (len instr) 3)
      (fra-addr-p (cadr instr))
      (integerp (caddr instr))))
    ((or
      (equal (car instr) :fra-ineg)
      (equal (car instr) :fra-ipush)
      (equal (car instr) :fra-ipop))
     (and
      (true-listp instr)
      (equal (len instr) 2)
      (integerp (cadr instr))))
    ((equal (car instr) :fra-iadd)
     (and
      (true-listp instr)
      (equal (len instr) 3)
      (integerp (cadr instr))
      (integerp (caddr instr))))
    (t nil))))

(defun fra-code-p (code)
  (if (consp code)
      (and
       (fra-instr-p (car code))
       (fra-code-p (cdr code)))
    (equal code nil)))

(defun fra-integer-list-p (values)
  (if (consp values)
      (and
       (integerp (car values))
       (fra-integer-list-p (cdr values)))
    (equal values nil)))

(defun fra-iload (address register)
  (list :fra-iload address register))

(defun fra-ineg (register)
  (list :fra-ineg register))

(defun fra-iadd (left-register right-register)
  (list :fra-iadd left-register right-register))

(defun fra-ipush (register)
  (list :fra-ipush register))

(defun fra-ipop (register)
  (list :fra-ipop register))

;; A memory or register-function handle denotes an arbitrary total source
;; function. Register-update nodes are the exact source functional updates.

(defstub fra-memory-raw (handle address) t)
(defstub fra-registers-raw (handle register) t)

(defun fra-memory-p (memory)
  (and
   (true-listp memory)
   (equal (len memory) 2)
   (equal (car memory) :fra-memory)))

(defun fra-registers-p (registers)
  (declare (xargs :measure (acl2-count registers)))
  (and
   (consp registers)
   (cond
    ((equal (car registers) :fra-registers)
     (and
      (true-listp registers)
      (equal (len registers) 2)))
    ((equal (car registers) :fra-registers-update)
     (and
      (true-listp registers)
      (equal (len registers) 4)
      (fra-registers-p (cadr registers))
      (integerp (caddr registers))
      (integerp (cadddr registers))))
    (t nil))))

(defun fra-memory-apply (memory address)
  (ifix (fra-memory-raw (cadr memory) address)))

(defun fra-registers-apply (registers register)
  (declare (xargs :measure (acl2-count registers)))
  (if (equal (car registers) :fra-registers-update)
      (if (equal register (caddr registers))
          (cadddr registers)
        (fra-registers-apply (cadr registers) register))
    (ifix (fra-registers-raw (cadr registers) register))))

(defun fra-registers-update (registers register value)
  (list :fra-registers-update registers register value))

(defun-sk fra-memory-equiv-p (left right)
  (forall (address)
    (implies
     (fra-addr-p address)
     (equal
      (fra-memory-apply left address)
      (fra-memory-apply right address)))))

(defun-sk fra-registers-equiv-p (left right)
  (forall (register)
    (implies
     (integerp register)
     (equal
      (fra-registers-apply left register)
      (fra-registers-apply right register)))))

;; States are exact source records. State equality uses the extensional
;; equalities of the two function-valued fields.

(defun fra-state-p (st)
  (and
   (true-listp st)
   (equal (len st) 4)
   (equal (car st) :fra-state)
   (fra-memory-p (cadr st))
   (fra-registers-p (caddr st))
   (fra-integer-list-p (cadddr st))))

(defun fra-state (memory registers stack)
  (list :fra-state memory registers stack))

(defun fra-state-memory (st)
  (cadr st))

(defun fra-state-registers (st)
  (caddr st))

(defun fra-state-stack (st)
  (cadddr st))

(defun fra-state-equiv-p (left right)
  (and
   (fra-memory-equiv-p
    (fra-state-memory left)
    (fra-state-memory right))
   (fra-registers-equiv-p
    (fra-state-registers left)
    (fra-state-registers right))
   (equal
    (fra-state-stack left)
    (fra-state-stack right))))

(defun fra-eval (memory expr)
  (declare (xargs :measure (acl2-count expr)))
  (cond
   ((equal (car expr) :fra-evar)
    (fra-memory-apply memory (cadr expr)))
   ((equal (car expr) :fra-eneg)
    (- (fra-eval memory (cadr expr))))
   ((equal (car expr) :fra-eadd)
    (+
     (fra-eval memory (cadr expr))
     (fra-eval memory (caddr expr))))
   (t 0)))

(defun fra-exec (instr st)
  (let ((memory (fra-state-memory st))
        (registers (fra-state-registers st))
        (stack (fra-state-stack st)))
    (cond
     ((equal (car instr) :fra-iload)
      (fra-state
       memory
       (fra-registers-update
        registers
        (caddr instr)
        (fra-memory-apply memory (cadr instr)))
       stack))
     ((equal (car instr) :fra-ineg)
      (fra-state
       memory
       (fra-registers-update
        registers
        (cadr instr)
        (- (fra-registers-apply registers (cadr instr))))
       stack))
     ((equal (car instr) :fra-iadd)
      (fra-state
       memory
       (fra-registers-update
        registers
        (caddr instr)
        (+
         (fra-registers-apply registers (cadr instr))
         (fra-registers-apply registers (caddr instr))))
       stack))
     ((equal (car instr) :fra-ipush)
      (fra-state
       memory
       registers
       (cons
        (fra-registers-apply registers (cadr instr))
        stack)))
     ((equal (car instr) :fra-ipop)
      (if (consp stack)
          (fra-state
           memory
           (fra-registers-update
            registers
            (cadr instr)
            (car stack))
           (cdr stack))
        st))
     (t st))))

(defun fra-exec-list (code st)
  (if (consp code)
      (fra-exec-list
       (cdr code)
       (fra-exec (car code) st))
    st))

(defun-sk fra-register-prefix-equal-p
    (left-registers right-registers bound)
  (forall (register)
    (implies
     (integerp register)
     (implies
      (< register bound)
      (equal
       (fra-registers-apply left-registers register)
       (fra-registers-apply right-registers register))))))

(defun fra-expr-post-apply (expr register initial final)
  (and
   (fra-memory-equiv-p
    (fra-state-memory final)
    (fra-state-memory initial))
   (equal
    (fra-registers-apply
     (fra-state-registers final)
     register)
    (fra-eval (fra-state-memory initial) expr))
   (equal
    (fra-state-stack final)
    (fra-state-stack initial))
   (fra-register-prefix-equal-p
    (fra-state-registers final)
    (fra-state-registers initial)
    register)))

;; Posts, state predicates, and predicate transformers represent the source
;; higher-order values extensionally. Raw handles cover arbitrary functions;
;; constructor nodes denote the lambdas occurring in the VC.

(defstub fra-post-raw-apply (handle initial final) t)
(defstub fra-state-pred-raw-apply (handle st) t)
(defstub fra-trans-raw-apply (handle predicate st) t)
(defstub fra-trans-section-apply (trans predicate st) t)

(defun fra-post-p (post)
  (and
   (consp post)
   (cond
    ((equal (car post) :fra-post-raw)
     (and
      (true-listp post)
      (equal (len post) 2)))
    ((equal (car post) :fra-expr-post)
     (and
      (true-listp post)
      (equal (len post) 3)
      (fra-expr-p (cadr post))
      (integerp (caddr post))))
    (t nil))))

(defun fra-post-apply (post initial final)
  (if (equal (car post) :fra-expr-post)
      (fra-expr-post-apply
       (cadr post)
       (caddr post)
       initial
       final)
    (if
        (fra-post-raw-apply
         (cadr post)
         initial
         final)
        t
      nil)))

(defun-sk fra-post-equiv-p (left right)
  (forall (initial final)
    (implies
     (and
      (fra-state-p initial)
      (fra-state-p final))
     (equal
      (fra-post-apply left initial final)
      (fra-post-apply right initial final)))))

(defun fra-trans-p (trans)
  (declare (xargs :measure (acl2-count trans)))
  (and
   (consp trans)
   (cond
    ((or
      (equal (car trans) :fra-trans-raw)
      (equal (car trans) :fra-trans-id))
     (and
      (true-listp trans)
      (equal
       (len trans)
       (if (equal (car trans) :fra-trans-id) 1 2))))
    ((equal (car trans) :fra-trans-to-wp)
     (and
      (true-listp trans)
      (equal (len trans) 2)
      (fra-post-p (cadr trans))))
    ((equal (car trans) :fra-trans-exec)
     (and
      (true-listp trans)
      (equal (len trans) 2)
      (fra-instr-p (cadr trans))))
    ((equal (car trans) :fra-trans-compose)
     (and
      (true-listp trans)
      (equal (len trans) 3)
      (fra-trans-p (cadr trans))
      (fra-trans-p (caddr trans))))
    (t nil))))

(defun fra-state-pred-p (predicate)
  (declare (xargs :measure (acl2-count predicate)))
  (and
   (consp predicate)
   (cond
    ((equal (car predicate) :fra-state-pred-raw)
     (and
      (true-listp predicate)
      (equal (len predicate) 2)))
    ((equal (car predicate) :fra-post-section)
     (and
      (true-listp predicate)
      (equal (len predicate) 3)
      (fra-post-p (cadr predicate))
      (fra-state-p (caddr predicate))))
    ((equal (car predicate) :fra-trans-section)
     (and
      (true-listp predicate)
      (equal (len predicate) 3)
      (fra-trans-p (cadr predicate))
      (fra-state-pred-p (caddr predicate))))
    (t nil))))

(defun fra-state-pred-apply (predicate st)
  (cond
   ((equal (car predicate) :fra-post-section)
    (fra-post-apply
     (cadr predicate)
     (caddr predicate)
     st))
   ((equal (car predicate) :fra-trans-section)
    (if
        (fra-trans-section-apply
         (cadr predicate)
         (caddr predicate)
         st)
        t
      nil))
   (t
    (if
        (fra-state-pred-raw-apply
         (cadr predicate)
         st)
        t
      nil))))

(defun-sk fra-state-pred-equiv-p (left right)
  (forall (st)
    (implies
     (fra-state-p st)
     (equal
      (fra-state-pred-apply left st)
      (fra-state-pred-apply right st)))))

(defun-sk fra-to-wp-apply
    (post predicate initial)
  (forall (final)
    (implies
     (fra-state-p final)
     (implies
      (fra-post-apply post initial final)
      (fra-state-pred-apply predicate final)))))

(defun fra-trans-apply (trans predicate st)
  (declare (xargs :measure (acl2-count trans)))
  (cond
   ((equal (car trans) :fra-trans-id)
    (fra-state-pred-apply predicate st))
   ((equal (car trans) :fra-trans-to-wp)
    (fra-to-wp-apply (cadr trans) predicate st))
   ((equal (car trans) :fra-trans-exec)
    (fra-state-pred-apply
     predicate
     (fra-exec (cadr trans) st)))
   ((equal (car trans) :fra-trans-compose)
    (fra-trans-apply
     (caddr trans)
     (list
      :fra-trans-section
      (cadr trans)
      predicate)
     st))
   (t
    (if
        (fra-trans-raw-apply
         (cadr trans)
         predicate
         st)
        t
      nil))))

(defun-sk fra-trans-equiv-p (left right)
  (forall (predicate st)
    (implies
     (and
      (fra-state-pred-p predicate)
      (fra-state-p st))
     (equal
      (fra-trans-apply left predicate st)
      (fra-trans-apply right predicate st)))))

(defun fra-expr-post (expr register)
  (list :fra-expr-post expr register))

(defun fra-post-section (post st)
  (list :fra-post-section post st))

(defun fra-trans-id ()
  (list :fra-trans-id))

(defun fra-trans-to-wp (post)
  (list :fra-trans-to-wp post))

(defun fra-trans-exec (instr)
  (list :fra-trans-exec instr))

(defun fra-trans-compose (left right)
  (list :fra-trans-compose left right))

;; These are exactly the extensionality and lambda-application laws implicit
;; in the source function spaces. They quotient first-order handles by
;; pointwise equality without restricting any carrier to a finite table.

(defun-sk fra-state-predicate-extensionality-p ()
  (forall
   (predicate left-state right-state)
   (implies
    (and
     (fra-state-pred-p predicate)
     (fra-state-p left-state)
     (fra-state-p right-state)
     (fra-state-equiv-p left-state right-state))
    (equal
     (fra-state-pred-apply predicate left-state)
     (fra-state-pred-apply predicate right-state)))))

(defun-sk fra-post-extensionality-p ()
  (forall
   (post left-initial right-initial left-final right-final)
   (implies
    (and
     (fra-post-p post)
     (fra-state-p left-initial)
     (fra-state-p right-initial)
     (fra-state-p left-final)
     (fra-state-p right-final)
     (fra-state-equiv-p left-initial right-initial)
     (fra-state-equiv-p left-final right-final))
    (equal
     (fra-post-apply post left-initial left-final)
     (fra-post-apply post right-initial right-final)))))

(defun-sk fra-transformer-extensionality-p ()
  (forall
   (trans left-predicate right-predicate st)
   (implies
    (and
     (fra-trans-p trans)
     (fra-state-pred-p left-predicate)
     (fra-state-pred-p right-predicate)
     (fra-state-p st)
     (fra-state-pred-equiv-p
      left-predicate
      right-predicate))
    (equal
     (fra-trans-apply trans left-predicate st)
     (fra-trans-apply trans right-predicate st)))))

(defun-sk fra-transformer-section-law-p ()
  (forall
   (trans predicate st)
   (implies
    (and
     (fra-trans-p trans)
     (fra-state-pred-p predicate)
     (fra-state-p st))
    (equal
     (if
         (fra-trans-section-apply
          trans predicate st)
         t
       nil)
     (fra-trans-apply trans predicate st)))))

(defun fra-function-space-laws-p ()
  (and
   (fra-state-predicate-extensionality-p)
   (fra-post-extensionality-p)
   (fra-transformer-extensionality-p)
   (fra-transformer-section-law-p)))

;; H-code and W-code are exact source records.

(defun fra-hcode-p (hcode)
  (and
   (true-listp hcode)
   (equal (len hcode) 3)
   (equal (car hcode) :fra-hcode)
   (fra-code-p (cadr hcode))
   (fra-post-p (caddr hcode))))

(defun fra-wcode-p (wcode)
  (and
   (true-listp wcode)
   (equal (len wcode) 3)
   (equal (car wcode) :fra-wcode)
   (fra-trans-p (cadr wcode))
   (fra-code-p (caddr wcode))))

(defun fra-hcode-code (hcode)
  (cadr hcode))

(defun fra-hcode-post (hcode)
  (caddr hcode))

(defun fra-wcode-trans (wcode)
  (cadr wcode))

(defun fra-wcode-code (wcode)
  (caddr wcode))

(defun-sk fra-hcode-ok-p (hcode)
  (forall (st)
    (implies
     (fra-state-p st)
     (fra-post-apply
      (fra-hcode-post hcode)
      st
      (fra-exec-list
       (fra-hcode-code hcode)
       st)))))

(defun-sk fra-wcode-ok-p (wcode)
  (forall (predicate st)
    (implies
     (and
      (fra-state-pred-p predicate)
      (fra-state-p st))
     (implies
      (fra-trans-apply
       (fra-wcode-trans wcode)
       predicate
       st)
      (fra-state-pred-apply
       predicate
       (fra-exec-list
        (fra-wcode-code wcode)
        st))))))

(defun fra-immediate-subexpr-p (whole part)
  (cond
   ((equal (car whole) :fra-evar)
    nil)
   ((equal (car whole) :fra-eneg)
    (equal (cadr whole) part))
   ((equal (car whole) :fra-eadd)
    (or
     (equal (cadr whole) part)
     (equal (caddr whole) part)))
   (t nil)))

;; Verification obligations for the Evar and Eneg branches.

(defun-sk fra-evar-obligation-p ()
  (forall (o2)
    (implies
     (fra-wcode-p o2)
     (implies
      (and
       (fra-wcode-ok-p o2)
       (fra-trans-equiv-p
        (fra-wcode-trans o2)
        (fra-trans-id)))
      (fra-wcode-ok-p o2)))))

(defun-sk fra-neg-o5-obligation-p (o3 o4)
  (forall (o5)
    (implies
     (fra-wcode-p o5)
     (implies
      (and
       (fra-wcode-ok-p o5)
       (fra-trans-equiv-p
        (fra-wcode-trans o5)
        (fra-trans-to-wp
         (fra-hcode-post o4))))
      (and
       (fra-wcode-ok-p o5)
       (fra-wcode-ok-p o3))))))

(defun-sk fra-neg-o4-obligation-p (subexpr register o3)
  (forall (o4)
    (implies
     (fra-hcode-p o4)
     (implies
      (and
       (fra-hcode-ok-p o4)
       (fra-post-equiv-p
        (fra-hcode-post o4)
        (fra-expr-post subexpr register)))
      (and
       (fra-hcode-ok-p o4)
       (fra-neg-o5-obligation-p o3 o4))))))

(defun-sk fra-neg-o3-obligation-p
    (expr subexpr register register-count o2)
  (forall (o3)
    (implies
     (fra-wcode-p o3)
     (implies
      (and
       (fra-wcode-ok-p o3)
       (fra-trans-equiv-p
        (fra-wcode-trans o3)
        (fra-trans-compose
         (fra-wcode-trans o2)
         (fra-trans-exec
          (fra-ineg register)))))
      (and
       (and
        (fra-immediate-subexpr-p expr subexpr)
        (<= 0 register)
        (< register register-count))
       (fra-neg-o4-obligation-p
        subexpr register o3))))))

(defun-sk fra-neg-obligation-p
    (expr subexpr register register-count)
  (forall (o2)
    (implies
     (fra-wcode-p o2)
     (implies
      (and
       (fra-wcode-ok-p o2)
       (fra-trans-equiv-p
        (fra-wcode-trans o2)
        (fra-trans-id)))
      (and
       (fra-wcode-ok-p o2)
       (fra-neg-o3-obligation-p
        expr subexpr register register-count o2))))))

;; Verification obligations for Eadd when register + 1 is available.

(defun-sk fra-add-direct-o9-obligation-p (o3 o6 o8)
  (forall (o9)
    (implies
     (fra-wcode-p o9)
     (implies
      (and
       (fra-wcode-ok-p o9)
       (fra-trans-equiv-p
        (fra-wcode-trans o9)
        (fra-trans-compose
         (fra-wcode-trans o6)
         (fra-wcode-trans o8))))
      (and
       (fra-wcode-ok-p o9)
       (fra-wcode-ok-p o3))))))

(defun-sk fra-add-direct-o8-obligation-p (o3 o6 o7)
  (forall (o8)
    (implies
     (fra-wcode-p o8)
     (implies
      (and
       (fra-wcode-ok-p o8)
       (fra-trans-equiv-p
        (fra-wcode-trans o8)
        (fra-trans-to-wp
         (fra-hcode-post o7))))
      (and
       (and
        (fra-wcode-ok-p o8)
        (fra-wcode-ok-p o6))
       (fra-add-direct-o9-obligation-p
        o3 o6 o8))))))

(defun-sk fra-add-direct-o7-obligation-p
    (left-expr register o3 o6)
  (forall (o7)
    (implies
     (fra-hcode-p o7)
     (implies
      (and
       (fra-hcode-ok-p o7)
       (fra-post-equiv-p
        (fra-hcode-post o7)
        (fra-expr-post left-expr register)))
      (and
       (fra-hcode-ok-p o7)
       (fra-add-direct-o8-obligation-p
        o3 o6 o7))))))

(defun-sk fra-add-direct-o6-obligation-p
    (expr left-expr register register-count o3 o5)
  (forall (o6)
    (implies
     (fra-wcode-p o6)
     (implies
      (and
       (fra-wcode-ok-p o6)
       (fra-trans-equiv-p
        (fra-wcode-trans o6)
        (fra-trans-to-wp
         (fra-hcode-post o5))))
      (and
       (and
        (fra-immediate-subexpr-p expr left-expr)
        (<= 0 register)
        (< register register-count))
       (fra-add-direct-o7-obligation-p
        left-expr register o3 o6))))))

(defun-sk fra-add-direct-o5-obligation-p
    (expr left-expr right-expr register register-count o3)
  (forall (o5)
    (implies
     (fra-hcode-p o5)
     (implies
      (and
       (fra-hcode-ok-p o5)
       (fra-post-equiv-p
        (fra-hcode-post o5)
        (fra-expr-post
         right-expr
         (+ register 1))))
      (and
       (fra-hcode-ok-p o5)
       (fra-add-direct-o6-obligation-p
        expr
        left-expr
        register
        register-count
        o3
        o5))))))

(defun-sk fra-add-direct-o3-obligation-p
    (expr left-expr right-expr register register-count o2)
  (forall (o3)
    (implies
     (fra-wcode-p o3)
     (implies
      (and
       (fra-wcode-ok-p o3)
       (fra-trans-equiv-p
        (fra-wcode-trans o3)
        (fra-trans-compose
         (fra-wcode-trans o2)
         (fra-trans-exec
          (fra-iadd
           (+ register 1)
           register)))))
      (let ((next-register (+ register 1)))
        (and
         (and
          (fra-immediate-subexpr-p
           expr right-expr)
          (<= 0 next-register)
          (< next-register register-count))
         (fra-add-direct-o5-obligation-p
          expr
          left-expr
          right-expr
          register
          register-count
          o3)))))))

(defun-sk fra-add-direct-obligation-p
    (expr left-expr right-expr register register-count)
  (forall (o2)
    (implies
     (fra-wcode-p o2)
     (implies
      (and
       (fra-wcode-ok-p o2)
       (fra-trans-equiv-p
        (fra-wcode-trans o2)
        (fra-trans-id)))
      (and
       (fra-wcode-ok-p o2)
       (fra-add-direct-o3-obligation-p
        expr
        left-expr
        right-expr
        register
        register-count
        o2))))))

;; Verification obligations for Eadd when spilling through the stack.

(defun-sk fra-add-spill-o12-obligation-p (o4 o11)
  (forall (o12)
    (implies
     (fra-wcode-p o12)
     (implies
      (and
       (fra-wcode-ok-p o12)
       (fra-trans-equiv-p
        (fra-wcode-trans o12)
        (fra-trans-compose
         (fra-wcode-trans o4)
         (fra-wcode-trans o11))))
      (fra-wcode-ok-p o12)))))

(defun-sk fra-add-spill-o11-obligation-p (o4 o7 o10)
  (forall (o11)
    (implies
     (fra-wcode-p o11)
     (implies
      (and
       (fra-wcode-ok-p o11)
       (fra-trans-equiv-p
        (fra-wcode-trans o11)
        (fra-trans-compose
         (fra-wcode-trans o7)
         (fra-wcode-trans o10))))
      (and
       (and
        (fra-wcode-ok-p o11)
        (fra-wcode-ok-p o4))
       (fra-add-spill-o12-obligation-p
        o4 o11))))))

(defun-sk fra-add-spill-o10-obligation-p (o4 o7 o9)
  (forall (o10)
    (implies
     (fra-wcode-p o10)
     (implies
      (and
       (fra-wcode-ok-p o10)
       (fra-trans-equiv-p
        (fra-wcode-trans o10)
        (fra-trans-to-wp
         (fra-hcode-post o9))))
      (and
       (and
        (fra-wcode-ok-p o10)
        (fra-wcode-ok-p o7))
       (fra-add-spill-o11-obligation-p
        o4 o7 o10))))))

(defun-sk fra-add-spill-o9-obligation-p
    (left-expr left-register o4 o7)
  (forall (o9)
    (implies
     (fra-hcode-p o9)
     (implies
      (and
       (fra-hcode-ok-p o9)
       (fra-post-equiv-p
        (fra-hcode-post o9)
        (fra-expr-post
         left-expr
         left-register)))
      (and
       (fra-hcode-ok-p o9)
       (fra-add-spill-o10-obligation-p
        o4 o7 o9))))))

(defun-sk fra-add-spill-o7-obligation-p
    (expr left-expr register-count o4 o6)
  (forall (o7)
    (implies
     (fra-wcode-p o7)
     (implies
      (and
       (fra-wcode-ok-p o7)
       (fra-trans-equiv-p
        (fra-wcode-trans o7)
        (fra-trans-to-wp
         (fra-hcode-post o6))))
      (let ((left-register (- register-count 2)))
        (and
         (and
          (fra-immediate-subexpr-p
           expr left-expr)
          (<= 0 left-register)
          (< left-register register-count))
         (fra-add-spill-o9-obligation-p
          left-expr left-register o4 o7)))))))

(defun-sk fra-add-spill-o6-obligation-p
    (expr left-expr right-expr register-count o4)
  (forall (o6)
    (implies
     (fra-hcode-p o6)
     (implies
      (and
       (fra-hcode-ok-p o6)
       (fra-post-equiv-p
        (fra-hcode-post o6)
        (fra-expr-post
         right-expr
         (- register-count 1))))
      (and
       (fra-hcode-ok-p o6)
       (fra-add-spill-o7-obligation-p
        expr
        left-expr
        register-count
        o4
        o6))))))

(defun-sk fra-add-spill-o4-obligation-p
    (expr left-expr right-expr register-count o3)
  (forall (o4)
    (implies
     (fra-wcode-p o4)
     (implies
      (and
       (fra-wcode-ok-p o4)
       (fra-trans-equiv-p
        (fra-wcode-trans o4)
        (fra-trans-compose
         (fra-wcode-trans o3)
         (fra-trans-exec
          (fra-iadd
           (- register-count 2)
           (- register-count 1))))))
      (let ((right-register (- register-count 1)))
        (and
         (and
          (fra-immediate-subexpr-p
           expr right-expr)
          (<= 0 right-register)
          (< right-register register-count))
         (fra-add-spill-o6-obligation-p
          expr
          left-expr
          right-expr
          register-count
          o4)))))))

(defun-sk fra-add-spill-o3-obligation-p
    (expr left-expr right-expr register-count o2)
  (forall (o3)
    (implies
     (fra-wcode-p o3)
     (implies
      (and
       (fra-wcode-ok-p o3)
       (fra-trans-equiv-p
        (fra-wcode-trans o3)
        (fra-trans-compose
         (fra-wcode-trans o2)
         (fra-trans-exec
          (fra-ipop
           (- register-count 2))))))
      (and
       (fra-wcode-ok-p o3)
       (fra-add-spill-o4-obligation-p
        expr
        left-expr
        right-expr
        register-count
        o3))))))

(defun-sk fra-add-spill-obligation-p
    (expr left-expr right-expr register-count)
  (forall (o2)
    (implies
     (fra-wcode-p o2)
     (implies
      (and
       (fra-wcode-ok-p o2)
       (fra-trans-equiv-p
        (fra-wcode-trans o2)
        (fra-trans-id)))
      (and
       (fra-wcode-ok-p o2)
       (fra-add-spill-o3-obligation-p
        expr
        left-expr
        right-expr
        register-count
        o2))))))

(defun fra-branch-obligation-p
    (expr register register-count)
  (cond
   ((equal (car expr) :fra-evar)
    (fra-evar-obligation-p))
   ((equal (car expr) :fra-eneg)
    (fra-neg-obligation-p
     expr
     (cadr expr)
     register
     register-count))
   ((equal (car expr) :fra-eadd)
    (if (< register (- register-count 1))
        (fra-add-direct-obligation-p
         expr
         (cadr expr)
         (caddr expr)
         register
         register-count)
      (fra-add-spill-obligation-p
       expr
       (cadr expr)
       (caddr expr)
       register-count)))
   (t nil)))

;; Existential construction side of the generated compiler VC.

(defun-sk fra-evar-construction-p
    (address register o2)
  (exists (o3)
    (and
     (fra-wcode-p o3)
     (fra-wcode-ok-p o3)
     (fra-trans-equiv-p
      (fra-wcode-trans o3)
      (fra-trans-id))
     (fra-wcode-ok-p o2)
     (fra-trans-equiv-p
      (fra-wcode-trans o2)
      (fra-trans-compose
       (fra-wcode-trans o3)
       (fra-trans-exec
        (fra-iload address register)))))))

(defun-sk fra-neg-construction-p
    (subexpr register o2)
  (exists (o3 o4 o5 o6)
    (and
     (fra-wcode-p o3)
     (fra-wcode-p o4)
     (fra-hcode-p o5)
     (fra-wcode-p o6)
     (fra-wcode-ok-p o3)
     (fra-trans-equiv-p
      (fra-wcode-trans o3)
      (fra-trans-id))
     (fra-wcode-ok-p o4)
     (fra-trans-equiv-p
      (fra-wcode-trans o4)
      (fra-trans-compose
       (fra-wcode-trans o3)
       (fra-trans-exec
        (fra-ineg register))))
     (fra-hcode-ok-p o5)
     (fra-post-equiv-p
      (fra-hcode-post o5)
      (fra-expr-post subexpr register))
     (fra-wcode-ok-p o6)
     (fra-trans-equiv-p
      (fra-wcode-trans o6)
      (fra-trans-to-wp
       (fra-hcode-post o5)))
     (fra-wcode-ok-p o2)
     (fra-trans-equiv-p
      (fra-wcode-trans o2)
      (fra-trans-compose
       (fra-wcode-trans o4)
       (fra-wcode-trans o6))))))

(defun-sk fra-add-direct-construction-p
    (left-expr right-expr register o2)
  (exists (o3 o4 o5 o6 o7 o8 o9)
    (and
     (fra-wcode-p o3)
     (fra-wcode-p o4)
     (fra-hcode-p o5)
     (fra-wcode-p o6)
     (fra-hcode-p o7)
     (fra-wcode-p o8)
     (fra-wcode-p o9)
     (fra-wcode-ok-p o3)
     (fra-trans-equiv-p
      (fra-wcode-trans o3)
      (fra-trans-id))
     (fra-wcode-ok-p o4)
     (fra-trans-equiv-p
      (fra-wcode-trans o4)
      (fra-trans-compose
       (fra-wcode-trans o3)
       (fra-trans-exec
        (fra-iadd
         (+ register 1)
         register))))
     (fra-hcode-ok-p o5)
     (fra-post-equiv-p
      (fra-hcode-post o5)
      (fra-expr-post
       right-expr
       (+ register 1)))
     (fra-wcode-ok-p o6)
     (fra-trans-equiv-p
      (fra-wcode-trans o6)
      (fra-trans-to-wp
       (fra-hcode-post o5)))
     (fra-hcode-ok-p o7)
     (fra-post-equiv-p
      (fra-hcode-post o7)
      (fra-expr-post left-expr register))
     (fra-wcode-ok-p o8)
     (fra-trans-equiv-p
      (fra-wcode-trans o8)
      (fra-trans-to-wp
       (fra-hcode-post o7)))
     (fra-wcode-ok-p o9)
     (fra-trans-equiv-p
      (fra-wcode-trans o9)
      (fra-trans-compose
       (fra-wcode-trans o6)
       (fra-wcode-trans o8)))
     (fra-wcode-ok-p o2)
     (fra-trans-equiv-p
      (fra-wcode-trans o2)
      (fra-trans-compose
       (fra-wcode-trans o4)
       (fra-wcode-trans o9))))))

(defun-sk fra-add-spill-construction-p
    (left-expr right-expr register-count o2)
  (exists (o3 o4 o5 o6 o7 o8 o9 o10 o11)
    (and
     (fra-wcode-p o3)
     (fra-wcode-p o4)
     (fra-wcode-p o5)
     (fra-hcode-p o6)
     (fra-wcode-p o7)
     (fra-hcode-p o8)
     (fra-wcode-p o9)
     (fra-wcode-p o10)
     (fra-wcode-p o11)
     (fra-wcode-ok-p o3)
     (fra-trans-equiv-p
      (fra-wcode-trans o3)
      (fra-trans-id))
     (fra-wcode-ok-p o4)
     (fra-trans-equiv-p
      (fra-wcode-trans o4)
      (fra-trans-compose
       (fra-wcode-trans o3)
       (fra-trans-exec
        (fra-ipop
         (- register-count 2)))))
     (fra-wcode-ok-p o5)
     (fra-trans-equiv-p
      (fra-wcode-trans o5)
      (fra-trans-compose
       (fra-wcode-trans o4)
       (fra-trans-exec
        (fra-iadd
         (- register-count 2)
         (- register-count 1)))))
     (fra-hcode-ok-p o6)
     (fra-post-equiv-p
      (fra-hcode-post o6)
      (fra-expr-post
       right-expr
       (- register-count 1)))
     (fra-wcode-ok-p o7)
     (fra-trans-equiv-p
      (fra-wcode-trans o7)
      (fra-trans-to-wp
       (fra-hcode-post o6)))
     (fra-hcode-ok-p o8)
     (fra-post-equiv-p
      (fra-hcode-post o8)
      (fra-expr-post
       left-expr
       (- register-count 2)))
     (fra-wcode-ok-p o9)
     (fra-trans-equiv-p
      (fra-wcode-trans o9)
      (fra-trans-to-wp
       (fra-hcode-post o8)))
     (fra-wcode-ok-p o10)
     (fra-trans-equiv-p
      (fra-wcode-trans o10)
      (fra-trans-compose
       (fra-wcode-trans o7)
       (fra-wcode-trans o9)))
     (fra-wcode-ok-p o11)
     (fra-trans-equiv-p
      (fra-wcode-trans o11)
      (fra-trans-compose
       (fra-wcode-trans o5)
       (fra-wcode-trans o10)))
     (fra-wcode-ok-p o2)
     (fra-trans-equiv-p
      (fra-wcode-trans o2)
      (fra-trans-compose
       (fra-wcode-trans o11)
       (fra-trans-exec
        (fra-ipush
         (- register-count 2))))))))

(defun fra-construction-p
    (expr register register-count o2)
  (cond
   ((equal (car expr) :fra-evar)
    (fra-evar-construction-p
     (cadr expr) register o2))
   ((equal (car expr) :fra-eneg)
    (fra-neg-construction-p
     (cadr expr) register o2))
   ((equal (car expr) :fra-eadd)
    (if (< register (- register-count 1))
        (fra-add-direct-construction-p
         (cadr expr)
         (caddr expr)
         register
         o2)
      (fra-add-spill-construction-p
       (cadr expr)
       (caddr expr)
       register-count
       o2)))
   (t nil)))

(defun-sk fra-wcode-postcondition-p (wcode post)
  (forall (st)
    (implies
     (fra-state-p st)
     (fra-trans-apply
      (fra-wcode-trans wcode)
      (fra-post-section post st)
      st))))

(defun-sk fra-result-obligation-p
    (expr register post)
  (forall (result)
    (implies
     (fra-hcode-p result)
     (implies
      (and
       (fra-hcode-ok-p result)
       (fra-post-equiv-p
        (fra-hcode-post result)
        post))
      (and
       (fra-hcode-ok-p result)
       (fra-post-equiv-p
        (fra-hcode-post result)
        (fra-expr-post expr register)))))))

(defun-sk fra-all-wcodes-obligation-p
    (expr register register-count post)
  (forall (o2)
    (implies
     (fra-wcode-p o2)
     (implies
      (fra-construction-p
       expr register register-count o2)
      (and
       (and
        (fra-wcode-ok-p o2)
        (fra-wcode-postcondition-p o2 post))
       (fra-result-obligation-p
        expr register post))))))

(defun
  ntp4vc-pearl-register-allocation-finite-number-of-registers-compileqtvc-statement
  (register-count register expr)
  (implies
   (and
    (integerp register-count)
    (<= 2 register-count)
    (integerp register)
    (fra-expr-p expr)
    (<= 0 register)
    (< register register-count)
    (fra-function-space-laws-p))
   (let ((post (fra-expr-post expr register)))
     (and
      (fra-branch-obligation-p
       expr register register-count)
      (fra-all-wcodes-obligation-p
       expr register register-count post)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
