;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/register_allocation_OptimalNumberOfRegisters_compileqtvc: the
;; optimal-register expression compiler verification condition, including
;; register-demand ordering, stack spilling, and double-WP correctness.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The address carrier is arbitrary. Expressions and instructions use the
;; source constructors, and registers retain their unbounded integer domain.

(defun ora-addr-p (x) (declare (ignore x)) t)

(defun ora-expr-p (e)
  (declare (xargs :measure (acl2-count e)))
  (and (consp e)
       (cond
        ((equal (car e) :ora-evar)
         (and (true-listp e) (equal (len e) 2)
              (ora-addr-p (cadr e))))
        ((equal (car e) :ora-eneg)
         (and (true-listp e) (equal (len e) 2)
              (ora-expr-p (cadr e))))
        ((equal (car e) :ora-eadd)
         (and (true-listp e) (equal (len e) 3)
              (ora-expr-p (cadr e))
              (ora-expr-p (caddr e))))
        (t nil))))

(defun ora-instr-p (i)
  (and (consp i)
       (cond
        ((equal (car i) :ora-iload)
         (and (true-listp i) (equal (len i) 3)
              (ora-addr-p (cadr i)) (integerp (caddr i))))
        ((member-eq (car i) '(:ora-ineg :ora-ipush :ora-ipop))
         (and (true-listp i) (equal (len i) 2)
              (integerp (cadr i))))
        ((equal (car i) :ora-iadd)
         (and (true-listp i) (equal (len i) 3)
              (integerp (cadr i)) (integerp (caddr i))))
        (t nil))))

(defun ora-code-p (xs)
  (if (consp xs)
      (and (ora-instr-p (car xs)) (ora-code-p (cdr xs)))
    (equal xs nil)))

(defun ora-int-list-p (xs)
  (if (consp xs)
      (and (integerp (car xs)) (ora-int-list-p (cdr xs)))
    (equal xs nil)))

(defun ora-iload (x r) (list :ora-iload x r))
(defun ora-ineg (r) (list :ora-ineg r))
(defun ora-iadd (r1 r2) (list :ora-iadd r1 r2))
(defun ora-ipush (r) (list :ora-ipush r))
(defun ora-ipop (r) (list :ora-ipop r))

;; Raw handles range over arbitrary total functions. Update nodes implement
;; source functional update without replacing functions by finite tables.

(defstub ora-memory-raw (handle address) t)
(defstub ora-registers-raw (handle register) t)

(defun ora-memory-p (m)
  (and (true-listp m) (equal (len m) 2)
       (equal (car m) :ora-memory)))

(defun ora-registers-p (rs)
  (declare (xargs :measure (acl2-count rs)))
  (and (consp rs)
       (cond
        ((equal (car rs) :ora-registers)
         (and (true-listp rs) (equal (len rs) 2)))
        ((equal (car rs) :ora-registers-update)
         (and (true-listp rs) (equal (len rs) 4)
              (ora-registers-p (cadr rs))
              (integerp (caddr rs))
              (integerp (cadddr rs))))
        (t nil))))

(defun ora-memory-apply (m x)
  (ifix (ora-memory-raw (cadr m) x)))

(defun ora-registers-apply (rs r)
  (declare (xargs :measure (acl2-count rs)))
  (if (equal (car rs) :ora-registers-update)
      (if (equal r (caddr rs))
          (cadddr rs)
        (ora-registers-apply (cadr rs) r))
    (ifix (ora-registers-raw (cadr rs) r))))

(defun ora-registers-update (rs r v)
  (list :ora-registers-update rs r v))

(defun-sk ora-memory-equiv-p (a b)
  (forall (x)
    (implies (ora-addr-p x)
             (equal (ora-memory-apply a x)
                    (ora-memory-apply b x)))))

(defun-sk ora-registers-equiv-p (a b)
  (forall (r)
    (implies (integerp r)
             (equal (ora-registers-apply a r)
                    (ora-registers-apply b r)))))

(defun ora-state-p (s)
  (and (true-listp s) (equal (len s) 4)
       (equal (car s) :ora-state)
       (ora-memory-p (cadr s))
       (ora-registers-p (caddr s))
       (ora-int-list-p (cadddr s))))

(defun ora-state (m rs st) (list :ora-state m rs st))
(defun ora-state-memory (s) (cadr s))
(defun ora-state-registers (s) (caddr s))
(defun ora-state-stack (s) (cadddr s))

(defun ora-state-equiv-p (a b)
  (and (ora-memory-equiv-p (ora-state-memory a) (ora-state-memory b))
       (ora-registers-equiv-p
        (ora-state-registers a) (ora-state-registers b))
       (equal (ora-state-stack a) (ora-state-stack b))))

(defun ora-eval (m e)
  (declare (xargs :measure (acl2-count e)))
  (cond
   ((equal (car e) :ora-evar) (ora-memory-apply m (cadr e)))
   ((equal (car e) :ora-eneg) (- (ora-eval m (cadr e))))
   ((equal (car e) :ora-eadd)
    (+ (ora-eval m (cadr e)) (ora-eval m (caddr e))))
   (t 0)))

(defun ora-exec (i s)
  (let ((m (ora-state-memory s))
        (rs (ora-state-registers s))
        (st (ora-state-stack s)))
    (cond
     ((equal (car i) :ora-iload)
      (ora-state m
                 (ora-registers-update
                  rs (caddr i) (ora-memory-apply m (cadr i)))
                 st))
     ((equal (car i) :ora-ineg)
      (ora-state m
                 (ora-registers-update
                  rs (cadr i) (- (ora-registers-apply rs (cadr i))))
                 st))
     ((equal (car i) :ora-iadd)
      (ora-state m
                 (ora-registers-update
                  rs (caddr i)
                  (+ (ora-registers-apply rs (cadr i))
                     (ora-registers-apply rs (caddr i))))
                 st))
     ((equal (car i) :ora-ipush)
      (ora-state m rs (cons (ora-registers-apply rs (cadr i)) st)))
     ((equal (car i) :ora-ipop)
      (if (consp st)
          (ora-state m
                     (ora-registers-update rs (cadr i) (car st))
                     (cdr st))
        s))
     (t s))))

(defun ora-exec-list (code s)
  (if (consp code)
      (ora-exec-list (cdr code) (ora-exec (car code) s))
    s))

(defun-sk ora-register-prefix-equal-p (a b bound)
  (forall (r)
    (implies (integerp r)
             (implies (< r bound)
                      (equal (ora-registers-apply a r)
                             (ora-registers-apply b r))))))

(defun ora-expr-post-apply (e r initial final)
  (and (ora-memory-equiv-p
        (ora-state-memory final) (ora-state-memory initial))
       (equal (ora-registers-apply (ora-state-registers final) r)
              (ora-eval (ora-state-memory initial) e))
       (equal (ora-state-stack final) (ora-state-stack initial))
       (ora-register-prefix-equal-p
        (ora-state-registers final)
        (ora-state-registers initial)
        r)))

;; Posts, predicates, and transformers are extensional function objects.

(defstub ora-post-raw-apply (handle initial final) t)
(defstub ora-pred-raw-apply (handle st) t)
(defstub ora-trans-raw-apply (handle predicate st) t)
(defstub ora-trans-section-apply (trans predicate st) t)

(defun ora-post-p (p)
  (and (consp p)
       (cond
        ((equal (car p) :ora-post-raw)
         (and (true-listp p) (equal (len p) 2)))
        ((equal (car p) :ora-expr-post)
         (and (true-listp p) (equal (len p) 3)
              (ora-expr-p (cadr p)) (integerp (caddr p))))
        (t nil))))

(defun ora-trans-p (tr)
  (declare (xargs :measure (acl2-count tr)))
  (and (consp tr)
       (cond
        ((equal (car tr) :ora-trans-raw)
         (and (true-listp tr) (equal (len tr) 2)))
        ((equal (car tr) :ora-trans-id)
         (equal tr (list :ora-trans-id)))
        ((equal (car tr) :ora-trans-to-wp)
         (and (true-listp tr) (equal (len tr) 2)
              (ora-post-p (cadr tr))))
        ((equal (car tr) :ora-trans-exec)
         (and (true-listp tr) (equal (len tr) 2)
              (ora-instr-p (cadr tr))))
        ((equal (car tr) :ora-trans-compose)
         (and (true-listp tr) (equal (len tr) 3)
              (ora-trans-p (cadr tr)) (ora-trans-p (caddr tr))))
        (t nil))))

(defun ora-pred-p (p)
  (declare (xargs :measure (acl2-count p)))
  (and (consp p)
       (cond
        ((equal (car p) :ora-pred-raw)
         (and (true-listp p) (equal (len p) 2)))
        ((equal (car p) :ora-post-section)
         (and (true-listp p) (equal (len p) 3)
              (ora-post-p (cadr p)) (ora-state-p (caddr p))))
        ((equal (car p) :ora-trans-section)
         (and (true-listp p) (equal (len p) 3)
              (ora-trans-p (cadr p)) (ora-pred-p (caddr p))))
        (t nil))))

(defun ora-post-apply (p s1 s2)
  (if (equal (car p) :ora-expr-post)
      (ora-expr-post-apply (cadr p) (caddr p) s1 s2)
    (if (ora-post-raw-apply (cadr p) s1 s2) t nil)))

(defun ora-pred-apply (p s)
  (cond
   ((equal (car p) :ora-post-section)
    (ora-post-apply (cadr p) (caddr p) s))
   ((equal (car p) :ora-trans-section)
    (if (ora-trans-section-apply (cadr p) (caddr p) s) t nil))
   (t (if (ora-pred-raw-apply (cadr p) s) t nil))))

(defun-sk ora-to-wp-apply (post pred s1)
  (forall (s2)
    (implies (ora-state-p s2)
             (implies (ora-post-apply post s1 s2)
                      (ora-pred-apply pred s2)))))

(defun ora-trans-apply (tr pred s)
  (declare (xargs :measure (acl2-count tr)))
  (cond
   ((equal (car tr) :ora-trans-id) (ora-pred-apply pred s))
   ((equal (car tr) :ora-trans-to-wp)
    (ora-to-wp-apply (cadr tr) pred s))
   ((equal (car tr) :ora-trans-exec)
    (ora-pred-apply pred (ora-exec (cadr tr) s)))
   ((equal (car tr) :ora-trans-compose)
    (ora-trans-apply
     (caddr tr) (list :ora-trans-section (cadr tr) pred) s))
   (t (if (ora-trans-raw-apply (cadr tr) pred s) t nil))))

(defun-sk ora-post-equiv-p (a b)
  (forall (s1 s2)
    (implies (and (ora-state-p s1) (ora-state-p s2))
             (equal (ora-post-apply a s1 s2)
                    (ora-post-apply b s1 s2)))))

(defun-sk ora-pred-equiv-p (a b)
  (forall (s)
    (implies (ora-state-p s)
             (equal (ora-pred-apply a s)
                    (ora-pred-apply b s)))))

(defun-sk ora-trans-equiv-p (a b)
  (forall (p s)
    (implies (and (ora-pred-p p) (ora-state-p s))
             (equal (ora-trans-apply a p s)
                    (ora-trans-apply b p s)))))

(defun ora-expr-post (e r) (list :ora-expr-post e r))
(defun ora-post-section (p s) (list :ora-post-section p s))
(defun ora-trans-id () (list :ora-trans-id))
(defun ora-trans-to-wp (p) (list :ora-trans-to-wp p))
(defun ora-trans-exec (i) (list :ora-trans-exec i))
(defun ora-trans-compose (a b) (list :ora-trans-compose a b))

;; These laws are the source function-space extensionality and the defining
;; application law for a partially applied transformer.

(defun-sk ora-pred-extensionality-p ()
  (forall (p s1 s2)
    (implies (and (ora-pred-p p) (ora-state-p s1) (ora-state-p s2)
                  (ora-state-equiv-p s1 s2))
             (equal (ora-pred-apply p s1)
                    (ora-pred-apply p s2)))))

(defun-sk ora-post-extensionality-p ()
  (forall (p a1 a2 b1 b2)
    (implies
     (and (ora-post-p p)
          (ora-state-p a1) (ora-state-p a2)
          (ora-state-p b1) (ora-state-p b2)
          (ora-state-equiv-p a1 a2)
          (ora-state-equiv-p b1 b2))
     (equal (ora-post-apply p a1 b1)
            (ora-post-apply p a2 b2)))))

(defun-sk ora-trans-extensionality-p ()
  (forall (tr p1 p2 s)
    (implies
     (and (ora-trans-p tr) (ora-pred-p p1) (ora-pred-p p2)
          (ora-state-p s) (ora-pred-equiv-p p1 p2))
     (equal (ora-trans-apply tr p1 s)
            (ora-trans-apply tr p2 s)))))

(defun-sk ora-trans-section-law-p ()
  (forall (tr p s)
    (implies
     (and (ora-trans-p tr) (ora-pred-p p) (ora-state-p s))
     (equal (if (ora-trans-section-apply tr p s) t nil)
            (ora-trans-apply tr p s)))))

(defun ora-function-space-laws-p ()
  (and (ora-pred-extensionality-p)
       (ora-post-extensionality-p)
       (ora-trans-extensionality-p)
       (ora-trans-section-law-p)))

(defun ora-hcode-p (h)
  (and (true-listp h) (equal (len h) 3)
       (equal (car h) :ora-hcode)
       (ora-code-p (cadr h)) (ora-post-p (caddr h))))

(defun ora-wcode-p (w)
  (and (true-listp w) (equal (len w) 3)
       (equal (car w) :ora-wcode)
       (ora-trans-p (cadr w)) (ora-code-p (caddr w))))

(defun ora-hcode-code (h) (cadr h))
(defun ora-hcode-post (h) (caddr h))
(defun ora-wcode-trans (w) (cadr w))
(defun ora-wcode-code (w) (caddr w))

(defun-sk ora-hcode-ok-p (h)
  (forall (s)
    (implies
     (ora-state-p s)
     (ora-post-apply
      (ora-hcode-post h) s
      (ora-exec-list (ora-hcode-code h) s)))))

(defun-sk ora-wcode-ok-p (w)
  (forall (p s)
    (implies
     (and (ora-pred-p p) (ora-state-p s))
     (implies
      (ora-trans-apply (ora-wcode-trans w) p s)
      (ora-pred-apply
       p (ora-exec-list (ora-wcode-code w) s))))))

;; The source register demand and termination measure.

(defun ora-n (e)
  (declare (xargs :measure (acl2-count e)))
  (cond
   ((equal (car e) :ora-evar) 1)
   ((equal (car e) :ora-eneg) (ora-n (cadr e)))
   ((equal (car e) :ora-eadd)
    (let ((n1 (ora-n (cadr e))) (n2 (ora-n (caddr e))))
      (if (equal n1 n2) (+ 1 n1) (max n1 n2))))
   (t 0)))

(defun ora-measure (e)
  (declare (xargs :measure (acl2-count e)))
  (cond
   ((equal (car e) :ora-evar) 0)
   ((equal (car e) :ora-eneg) (+ 1 (ora-measure (cadr e))))
   ((equal (car e) :ora-eadd)
    (+ 1
       (if (<= (ora-n (caddr e)) (ora-n (cadr e)))
           (+ (ora-measure (cadr e)) (ora-measure (caddr e)))
         (+ 1 (ora-measure (cadr e)) (ora-measure (caddr e))))))
   (t 0)))

(defun ora-bounds-p (r k) (and (<= 0 r) (< r k)))
(defun ora-decrease-p (whole part)
  (and (<= 0 (ora-measure whole))
       (< (ora-measure part) (ora-measure whole))))

;; Universal verification obligations for the expression branches.

(defun-sk ora-evar-obligation-p ()
  (forall (o2)
    (implies
     (ora-wcode-p o2)
     (implies
      (and (ora-wcode-ok-p o2)
           (ora-trans-equiv-p (ora-wcode-trans o2) (ora-trans-id)))
      (ora-wcode-ok-p o2)))))

(defun-sk ora-neg-o5-p (o3 o4)
  (forall (o5)
    (implies
     (ora-wcode-p o5)
     (implies
      (and (ora-wcode-ok-p o5)
           (ora-trans-equiv-p
            (ora-wcode-trans o5)
            (ora-trans-to-wp (ora-hcode-post o4))))
      (and (ora-wcode-ok-p o5) (ora-wcode-ok-p o3))))))

(defun-sk ora-neg-o4-p (sub r o3)
  (forall (o4)
    (implies
     (ora-hcode-p o4)
     (implies
      (and (ora-hcode-ok-p o4)
           (ora-post-equiv-p
            (ora-hcode-post o4) (ora-expr-post sub r)))
      (and (ora-hcode-ok-p o4) (ora-neg-o5-p o3 o4))))))

(defun-sk ora-neg-o3-p (e sub r k o2)
  (forall (o3)
    (implies
     (ora-wcode-p o3)
     (implies
      (and (ora-wcode-ok-p o3)
           (ora-trans-equiv-p
            (ora-wcode-trans o3)
            (ora-trans-compose
             (ora-wcode-trans o2) (ora-trans-exec (ora-ineg r)))))
      (and (and (ora-decrease-p e sub) (ora-bounds-p r k))
           (ora-neg-o4-p sub r o3))))))

(defun-sk ora-neg-obligation-p (e sub r k)
  (forall (o2)
    (implies
     (ora-wcode-p o2)
     (implies
      (and (ora-wcode-ok-p o2)
           (ora-trans-equiv-p (ora-wcode-trans o2) (ora-trans-id)))
      (and (ora-wcode-ok-p o2) (ora-neg-o3-p e sub r k o2))))))

(defun-sk ora-direct-o9-p (o3 o6 o8)
  (forall (o9)
    (implies
     (ora-wcode-p o9)
     (implies
      (and (ora-wcode-ok-p o9)
           (ora-trans-equiv-p
            (ora-wcode-trans o9)
            (ora-trans-compose
             (ora-wcode-trans o6) (ora-wcode-trans o8))))
      (and (ora-wcode-ok-p o9) (ora-wcode-ok-p o3))))))

(defun-sk ora-direct-o8-p (o3 o6 o7)
  (forall (o8)
    (implies
     (ora-wcode-p o8)
     (implies
      (and (ora-wcode-ok-p o8)
           (ora-trans-equiv-p
            (ora-wcode-trans o8)
            (ora-trans-to-wp (ora-hcode-post o7))))
      (and (and (ora-wcode-ok-p o8) (ora-wcode-ok-p o6))
           (ora-direct-o9-p o3 o6 o8))))))

(defun-sk ora-direct-o7-p (left r o3 o6)
  (forall (o7)
    (implies
     (ora-hcode-p o7)
     (implies
      (and (ora-hcode-ok-p o7)
           (ora-post-equiv-p
            (ora-hcode-post o7) (ora-expr-post left r)))
      (and (ora-hcode-ok-p o7) (ora-direct-o8-p o3 o6 o7))))))

(defun-sk ora-direct-o6-p (e left r k o3 o5)
  (forall (o6)
    (implies
     (ora-wcode-p o6)
     (implies
      (and (ora-wcode-ok-p o6)
           (ora-trans-equiv-p
            (ora-wcode-trans o6)
            (ora-trans-to-wp (ora-hcode-post o5))))
      (and (and (ora-decrease-p e left) (ora-bounds-p r k))
           (ora-direct-o7-p left r o3 o6))))))

(defun-sk ora-direct-o5-p (e left right r k o3)
  (forall (o5)
    (implies
     (ora-hcode-p o5)
     (implies
      (and (ora-hcode-ok-p o5)
           (ora-post-equiv-p
            (ora-hcode-post o5) (ora-expr-post right (+ r 1))))
      (and (ora-hcode-ok-p o5)
           (ora-direct-o6-p e left r k o3 o5))))))

(defun-sk ora-direct-o3-p (e left right r k o2)
  (forall (o3)
    (implies
     (ora-wcode-p o3)
     (implies
      (and (ora-wcode-ok-p o3)
           (ora-trans-equiv-p
            (ora-wcode-trans o3)
            (ora-trans-compose
             (ora-wcode-trans o2)
             (ora-trans-exec (ora-iadd (+ r 1) r)))))
      (and (and (ora-decrease-p e right) (ora-bounds-p (+ r 1) k))
           (ora-direct-o5-p e left right r k o3))))))

(defun-sk ora-direct-obligation-p (e left right r k)
  (forall (o2)
    (implies
     (ora-wcode-p o2)
     (implies
      (and (ora-wcode-ok-p o2)
           (ora-trans-equiv-p (ora-wcode-trans o2) (ora-trans-id)))
      (and (ora-wcode-ok-p o2)
           (ora-direct-o3-p e left right r k o2))))))

(defun-sk ora-spill-o12-p (o4 o11)
  (forall (o12)
    (implies
     (ora-wcode-p o12)
     (implies
      (and (ora-wcode-ok-p o12)
           (ora-trans-equiv-p
            (ora-wcode-trans o12)
            (ora-trans-compose
             (ora-wcode-trans o4) (ora-wcode-trans o11))))
      (ora-wcode-ok-p o12)))))

(defun-sk ora-spill-o11-p (o4 o7 o10)
  (forall (o11)
    (implies
     (ora-wcode-p o11)
     (implies
      (and (ora-wcode-ok-p o11)
           (ora-trans-equiv-p
            (ora-wcode-trans o11)
            (ora-trans-compose
             (ora-wcode-trans o7) (ora-wcode-trans o10))))
      (and (and (ora-wcode-ok-p o11) (ora-wcode-ok-p o4))
           (ora-spill-o12-p o4 o11))))))

(defun-sk ora-spill-o10-p (o4 o7 o9)
  (forall (o10)
    (implies
     (ora-wcode-p o10)
     (implies
      (and (ora-wcode-ok-p o10)
           (ora-trans-equiv-p
            (ora-wcode-trans o10)
            (ora-trans-to-wp (ora-hcode-post o9))))
      (and (and (ora-wcode-ok-p o10) (ora-wcode-ok-p o7))
           (ora-spill-o11-p o4 o7 o10))))))

(defun-sk ora-spill-o9-p (left left-r o4 o7)
  (forall (o9)
    (implies
     (ora-hcode-p o9)
     (implies
      (and (ora-hcode-ok-p o9)
           (ora-post-equiv-p
            (ora-hcode-post o9) (ora-expr-post left left-r)))
      (and (ora-hcode-ok-p o9) (ora-spill-o10-p o4 o7 o9))))))

(defun-sk ora-spill-o7-p (e left k o4 o6)
  (forall (o7)
    (implies
     (ora-wcode-p o7)
     (implies
      (and (ora-wcode-ok-p o7)
           (ora-trans-equiv-p
            (ora-wcode-trans o7)
            (ora-trans-to-wp (ora-hcode-post o6))))
      (let ((left-r (- k 2)))
        (and (and (ora-decrease-p e left) (ora-bounds-p left-r k))
             (ora-spill-o9-p left left-r o4 o7)))))))

(defun-sk ora-spill-o6-p (e left right k o4)
  (forall (o6)
    (implies
     (ora-hcode-p o6)
     (implies
      (and (ora-hcode-ok-p o6)
           (ora-post-equiv-p
            (ora-hcode-post o6) (ora-expr-post right (- k 1))))
      (and (ora-hcode-ok-p o6)
           (ora-spill-o7-p e left k o4 o6))))))

(defun-sk ora-spill-o4-p (e left right k o3)
  (forall (o4)
    (implies
     (ora-wcode-p o4)
     (implies
      (and (ora-wcode-ok-p o4)
           (ora-trans-equiv-p
            (ora-wcode-trans o4)
            (ora-trans-compose
             (ora-wcode-trans o3)
             (ora-trans-exec (ora-iadd (- k 2) (- k 1))))))
      (let ((right-r (- k 1)))
        (and (and (ora-decrease-p e right) (ora-bounds-p right-r k))
             (ora-spill-o6-p e left right k o4)))))))

(defun-sk ora-spill-o3-p (e left right k o2)
  (forall (o3)
    (implies
     (ora-wcode-p o3)
     (implies
      (and (ora-wcode-ok-p o3)
           (ora-trans-equiv-p
            (ora-wcode-trans o3)
            (ora-trans-compose
             (ora-wcode-trans o2)
             (ora-trans-exec (ora-ipop (- k 2))))))
      (and (ora-wcode-ok-p o3)
           (ora-spill-o4-p e left right k o3))))))

(defun-sk ora-spill-obligation-p (e left right k)
  (forall (o2)
    (implies
     (ora-wcode-p o2)
     (implies
      (and (ora-wcode-ok-p o2)
           (ora-trans-equiv-p (ora-wcode-trans o2) (ora-trans-id)))
      (and (ora-wcode-ok-p o2)
           (ora-spill-o3-p e left right k o2))))))

(defun-sk ora-swap-obligation-p (e swapped r k)
  (forall (o3)
    (implies
     (ora-hcode-p o3)
     (implies
      (and (ora-hcode-ok-p o3)
           (ora-post-equiv-p
            (ora-hcode-post o3) (ora-expr-post swapped r)))
      (ora-hcode-ok-p o3)))))

(defun ora-branch-obligation-p (e r k)
  (cond
   ((equal (car e) :ora-evar) (ora-evar-obligation-p))
   ((equal (car e) :ora-eneg)
    (ora-neg-obligation-p e (cadr e) r k))
   ((equal (car e) :ora-eadd)
    (let ((left (cadr e)) (right (caddr e)))
      (if (<= (ora-n right) (ora-n left))
          (if (< r (- k 1))
              (ora-direct-obligation-p e left right r k)
            (ora-spill-obligation-p e left right k))
        (let ((swapped (list :ora-eadd right left)))
          (and (and (ora-decrease-p e swapped) (ora-bounds-p r k))
               (ora-swap-obligation-p e swapped r k))))))
   (t nil)))

;; Existential construction side of the generated VC.

(defun-sk ora-evar-construction-p (x r o2)
  (exists (o3)
    (and (ora-wcode-p o3)
         (ora-wcode-ok-p o3)
         (ora-trans-equiv-p (ora-wcode-trans o3) (ora-trans-id))
         (ora-wcode-ok-p o2)
         (ora-trans-equiv-p
          (ora-wcode-trans o2)
          (ora-trans-compose
           (ora-wcode-trans o3) (ora-trans-exec (ora-iload x r)))))))

(defun-sk ora-neg-construction-p (sub r o2)
  (exists (o3 o4 o5 o6)
    (and
     (ora-wcode-p o3) (ora-wcode-p o4)
     (ora-hcode-p o5) (ora-wcode-p o6)
     (ora-wcode-ok-p o3)
     (ora-trans-equiv-p (ora-wcode-trans o3) (ora-trans-id))
     (ora-wcode-ok-p o4)
     (ora-trans-equiv-p
      (ora-wcode-trans o4)
      (ora-trans-compose
       (ora-wcode-trans o3) (ora-trans-exec (ora-ineg r))))
     (ora-hcode-ok-p o5)
     (ora-post-equiv-p
      (ora-hcode-post o5) (ora-expr-post sub r))
     (ora-wcode-ok-p o6)
     (ora-trans-equiv-p
      (ora-wcode-trans o6) (ora-trans-to-wp (ora-hcode-post o5)))
     (ora-wcode-ok-p o2)
     (ora-trans-equiv-p
      (ora-wcode-trans o2)
      (ora-trans-compose (ora-wcode-trans o4) (ora-wcode-trans o6))))))

(defun-sk ora-direct-construction-p (left right r o2)
  (exists (o3 o4 o5 o6 o7 o8 o9)
    (and
     (ora-wcode-p o3) (ora-wcode-p o4) (ora-hcode-p o5)
     (ora-wcode-p o6) (ora-hcode-p o7) (ora-wcode-p o8)
     (ora-wcode-p o9)
     (ora-wcode-ok-p o3)
     (ora-trans-equiv-p (ora-wcode-trans o3) (ora-trans-id))
     (ora-wcode-ok-p o4)
     (ora-trans-equiv-p
      (ora-wcode-trans o4)
      (ora-trans-compose
       (ora-wcode-trans o3) (ora-trans-exec (ora-iadd (+ r 1) r))))
     (ora-hcode-ok-p o5)
     (ora-post-equiv-p
      (ora-hcode-post o5) (ora-expr-post right (+ r 1)))
     (ora-wcode-ok-p o6)
     (ora-trans-equiv-p
      (ora-wcode-trans o6) (ora-trans-to-wp (ora-hcode-post o5)))
     (ora-hcode-ok-p o7)
     (ora-post-equiv-p
      (ora-hcode-post o7) (ora-expr-post left r))
     (ora-wcode-ok-p o8)
     (ora-trans-equiv-p
      (ora-wcode-trans o8) (ora-trans-to-wp (ora-hcode-post o7)))
     (ora-wcode-ok-p o9)
     (ora-trans-equiv-p
      (ora-wcode-trans o9)
      (ora-trans-compose (ora-wcode-trans o6) (ora-wcode-trans o8)))
     (ora-wcode-ok-p o2)
     (ora-trans-equiv-p
      (ora-wcode-trans o2)
      (ora-trans-compose (ora-wcode-trans o4) (ora-wcode-trans o9))))))

(defun-sk ora-spill-construction-p (left right k o2)
  (exists (o3 o4 o5 o6 o7 o8 o9 o10 o11)
    (and
     (ora-wcode-p o3) (ora-wcode-p o4) (ora-wcode-p o5)
     (ora-hcode-p o6) (ora-wcode-p o7) (ora-hcode-p o8)
     (ora-wcode-p o9) (ora-wcode-p o10) (ora-wcode-p o11)
     (ora-wcode-ok-p o3)
     (ora-trans-equiv-p (ora-wcode-trans o3) (ora-trans-id))
     (ora-wcode-ok-p o4)
     (ora-trans-equiv-p
      (ora-wcode-trans o4)
      (ora-trans-compose
       (ora-wcode-trans o3) (ora-trans-exec (ora-ipop (- k 2)))))
     (ora-wcode-ok-p o5)
     (ora-trans-equiv-p
      (ora-wcode-trans o5)
      (ora-trans-compose
       (ora-wcode-trans o4)
       (ora-trans-exec (ora-iadd (- k 2) (- k 1)))))
     (ora-hcode-ok-p o6)
     (ora-post-equiv-p
      (ora-hcode-post o6) (ora-expr-post right (- k 1)))
     (ora-wcode-ok-p o7)
     (ora-trans-equiv-p
      (ora-wcode-trans o7) (ora-trans-to-wp (ora-hcode-post o6)))
     (ora-hcode-ok-p o8)
     (ora-post-equiv-p
      (ora-hcode-post o8) (ora-expr-post left (- k 2)))
     (ora-wcode-ok-p o9)
     (ora-trans-equiv-p
      (ora-wcode-trans o9) (ora-trans-to-wp (ora-hcode-post o8)))
     (ora-wcode-ok-p o10)
     (ora-trans-equiv-p
      (ora-wcode-trans o10)
      (ora-trans-compose (ora-wcode-trans o7) (ora-wcode-trans o9)))
     (ora-wcode-ok-p o11)
     (ora-trans-equiv-p
      (ora-wcode-trans o11)
      (ora-trans-compose (ora-wcode-trans o5) (ora-wcode-trans o10)))
     (ora-wcode-ok-p o2)
     (ora-trans-equiv-p
      (ora-wcode-trans o2)
      (ora-trans-compose
       (ora-wcode-trans o11) (ora-trans-exec (ora-ipush (- k 2))))))))

(defun-sk ora-swap-construction-p (right left r o2)
  (exists (o3)
    (and
     (ora-hcode-p o3)
     (ora-hcode-ok-p o3)
     (ora-post-equiv-p
      (ora-hcode-post o3)
      (ora-expr-post (list :ora-eadd right left) r))
     (ora-wcode-ok-p o2)
     (ora-trans-equiv-p
      (ora-wcode-trans o2)
      (ora-trans-to-wp (ora-hcode-post o3))))))

(defun ora-construction-p (e r k o2)
  (cond
   ((equal (car e) :ora-evar)
    (ora-evar-construction-p (cadr e) r o2))
   ((equal (car e) :ora-eneg)
    (ora-neg-construction-p (cadr e) r o2))
   ((equal (car e) :ora-eadd)
    (let ((left (cadr e)) (right (caddr e)))
      (if (<= (ora-n right) (ora-n left))
          (if (< r (- k 1))
              (ora-direct-construction-p left right r o2)
            (ora-spill-construction-p left right k o2))
        (ora-swap-construction-p right left r o2))))
   (t nil)))

(defun-sk ora-wcode-postcondition-p (w post)
  (forall (s)
    (implies
     (ora-state-p s)
     (ora-trans-apply
      (ora-wcode-trans w) (ora-post-section post s) s))))

(defun-sk ora-result-obligation-p (e r post)
  (forall (result)
    (implies
     (ora-hcode-p result)
     (implies
      (and (ora-hcode-ok-p result)
           (ora-post-equiv-p (ora-hcode-post result) post))
      (and
       (ora-hcode-ok-p result)
       (ora-post-equiv-p
        (ora-hcode-post result) (ora-expr-post e r)))))))

(defun-sk ora-all-wcodes-obligation-p (e r k post)
  (forall (o2)
    (implies
     (ora-wcode-p o2)
     (implies
      (ora-construction-p e r k o2)
      (and
       (and (ora-wcode-ok-p o2)
            (ora-wcode-postcondition-p o2 post))
       (ora-result-obligation-p e r post))))))

(defun
  ntp4vc-pearl-register-allocation-optimal-number-of-registers-compileqtvc-statement
  (register-count register expr)
  (implies
   (and
    (integerp register-count)
    (<= 2 register-count)
    (integerp register)
    (ora-expr-p expr)
    (<= 0 register)
    (< register register-count)
    (ora-function-space-laws-p))
   (let ((post (ora-expr-post expr register)))
     (and
      (ora-branch-obligation-p expr register register-count)
      (ora-all-wcodes-obligation-p
       expr register register-count post)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
