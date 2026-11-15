;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/register_allocation_InfinityOfRegisters_compileqtvc: the
;; unrestricted-register expression compiler VC with double-WP correctness.
;; This file contains no proof.

(in-package "ACL2")
(set-inhibit-output-lst '(prove proof-tree event summary))

(defun fra-expr-p (e)
  (declare (xargs :measure (acl2-count e)))
  (and (consp e)
       (cond ((equal (car e) :var)
              (and (true-listp e) (equal (len e) 2)))
             ((equal (car e) :neg)
              (and (true-listp e) (equal (len e) 2)
                   (fra-expr-p (cadr e))))
             ((equal (car e) :add)
              (and (true-listp e) (equal (len e) 3)
                   (fra-expr-p (cadr e))
                   (fra-expr-p (caddr e))))
             (t nil))))

(defun fra-instr-p (i)
  (and (consp i)
       (cond ((equal (car i) :load)
              (and (true-listp i) (equal (len i) 3)
                   (integerp (caddr i))))
             ((member-equal (car i) '(:ineg :push :pop))
              (and (true-listp i) (equal (len i) 2)
                   (integerp (cadr i))))
             ((equal (car i) :iadd)
              (and (true-listp i) (equal (len i) 3)
                   (integerp (cadr i)) (integerp (caddr i))))
             (t nil))))

(defun fra-code-p (c)
  (if (consp c)
      (and (fra-instr-p (car c)) (fra-code-p (cdr c)))
    (equal c nil)))

(defun fra-int-list-p (x)
  (if (consp x)
      (and (integerp (car x)) (fra-int-list-p (cdr x)))
    (equal x nil)))

(defun fra-load (x r) (list :load x r))
(defun fra-ineg (r) (list :ineg r))
(defun fra-iadd (r1 r2) (list :iadd r1 r2))

;; Each source evaluation observes only finitely many points of its total
;; memory and register functions.  A function observation environment has an
;; arbitrary integer default and arbitrary finite overrides.  Consequently
;; every finite observation pattern of every source function is represented.
;; Extensional comparisons below still quantify over the full address or
;; integer domain, so this is observationally complete for this finite VC,
;; rather than a bounded carrier or a fixed finite table.

(defun fra-entries-p (xs)
  (if (consp xs)
      (and (true-listp (car xs)) (equal (len (car xs)) 2)
           (integerp (cadar xs)) (fra-entries-p (cdr xs)))
    (equal xs nil)))

(defun fra-fun-p (f)
  (and (true-listp f) (equal (len f) 3)
       (equal (car f) :fun) (integerp (cadr f))
       (fra-entries-p (caddr f))))

(defun fra-lookup (xs key default)
  (if (consp xs)
      (if (equal key (caar xs)) (cadar xs)
        (fra-lookup (cdr xs) key default))
    default))

(defun fra-app (f key)
  (fra-lookup (caddr f) key (cadr f)))

(defun fra-update (f key value)
  (list :fun (cadr f) (cons (list key value) (caddr f))))

(defun-sk fra-mem-eq (a b)
  (forall (x) (equal (fra-app a x) (fra-app b x))))

(defun-sk fra-reg-eq (a b)
  (forall (r)
    (implies (integerp r)
             (equal (fra-app a r) (fra-app b r)))))

(defun fra-state-p (s)
  (and (true-listp s) (equal (len s) 4) (equal (car s) :state)
       (fra-fun-p (cadr s)) (fra-fun-p (caddr s))
       (fra-int-list-p (cadddr s))))

(defun fra-state (m g st) (list :state m g st))
(defun fra-mem (s) (cadr s))
(defun fra-reg (s) (caddr s))
(defun fra-stack (s) (cadddr s))

(defun fra-state-eq (a b)
  (and (fra-mem-eq (fra-mem a) (fra-mem b))
       (fra-reg-eq (fra-reg a) (fra-reg b))
       (equal (fra-stack a) (fra-stack b))))

(defun fra-eval (m e)
  (declare (xargs :measure (acl2-count e)))
  (cond ((equal (car e) :var) (fra-app m (cadr e)))
        ((equal (car e) :neg) (- (fra-eval m (cadr e))))
        ((equal (car e) :add)
         (+ (fra-eval m (cadr e)) (fra-eval m (caddr e))))
        (t 0)))

(defun fra-exec (i s)
  (let ((m (fra-mem s)) (g (fra-reg s)) (st (fra-stack s)))
    (cond ((equal (car i) :load)
           (fra-state m (fra-update g (caddr i) (fra-app m (cadr i))) st))
          ((equal (car i) :ineg)
           (fra-state m (fra-update g (cadr i) (- (fra-app g (cadr i)))) st))
          ((equal (car i) :iadd)
           (fra-state m
                      (fra-update g (caddr i)
                                  (+ (fra-app g (cadr i))
                                     (fra-app g (caddr i))))
                      st))
          ((equal (car i) :push)
           (fra-state m g (cons (fra-app g (cadr i)) st)))
          ((equal (car i) :pop)
           (if (consp st)
               (fra-state m (fra-update g (cadr i) (car st)) (cdr st))
             s))
          (t s))))

(defun fra-exec-list (c s)
  (if (consp c)
      (fra-exec-list (cdr c) (fra-exec (car c) s))
    s))

(defun-sk fra-prefix-eq (a b bound)
  (forall (r)
    (implies (and (integerp r) (< r bound))
             (equal (fra-app a r) (fra-app b r)))))

(defun fra-post (e r s s2)
  (and (fra-mem-eq (fra-mem s2) (fra-mem s))
       (equal (fra-app (fra-reg s2) r) (fra-eval (fra-mem s) e))
       (equal (fra-stack s2) (fra-stack s))
       (fra-prefix-eq (fra-reg s2) (fra-reg s) r)))

;; Identity, execution closure, to_wp, and rcompose are defunctionalized as
;; relations.  For T(q)(s) = forall u, R(s,u) -> q(u), full source predicate
;; quantification is eliminated exactly by
;;   (forall q. T(q)(s) -> q(t))  iff  R(s,t),
;; using q = R(s,-) in the reverse direction.  Composition witnesses call the
;; complete constructor-aware relation recursively.

(defun fra-trans-p (tr)
  (declare (xargs :measure (acl2-count tr)))
  (and (consp tr)
       (cond ((equal (car tr) :id)
              (and (true-listp tr) (equal (len tr) 1)))
             ((equal (car tr) :exec)
              (and (true-listp tr) (equal (len tr) 2)
                   (fra-instr-p (cadr tr))))
             ((equal (car tr) :wp)
              (and (true-listp tr) (equal (len tr) 3)
                   (fra-expr-p (cadr tr)) (integerp (caddr tr))))
             ((equal (car tr) :comp)
              (and (true-listp tr) (equal (len tr) 3)
                   (fra-trans-p (cadr tr)) (fra-trans-p (caddr tr))))
             (t nil))))

(defun fra-id () (list :id))
(defun fra-exec-tr (i) (list :exec i))
(defun fra-wp (e r) (list :wp e r))
(defun fra-comp (left right) (list :comp left right))

(defun fra-rel-witness-p (tr s final witness)
  (declare (xargs :measure (acl2-count tr)))
  (cond ((equal (car tr) :id)
         (and (equal witness nil) (fra-state-eq s final)))
        ((equal (car tr) :exec)
         (and (equal witness nil)
              (fra-state-eq final (fra-exec (cadr tr) s))))
        ((equal (car tr) :wp)
         (and (equal witness nil)
              (fra-post (cadr tr) (caddr tr) s final)))
        ((equal (car tr) :comp)
         (and (true-listp witness) (equal (len witness) 4)
              (equal (car witness) :mid) (fra-state-p (cadr witness))
              (fra-rel-witness-p (caddr tr) s (cadr witness)
                                 (caddr witness))
              (fra-rel-witness-p (cadr tr) (cadr witness) final
                                 (cadddr witness))))
        (t nil)))

(defun-sk fra-rel (tr s final)
  (exists (w) (fra-rel-witness-p tr s final w)))

(defun-sk fra-wok (tr code)
  (forall (s)
    (implies (fra-state-p s)
             (fra-rel tr s (fra-exec-list code s)))))

(defun-sk fra-hok (e r code)
  (forall (s)
    (implies (fra-state-p s)
             (fra-post e r s (fra-exec-list code s)))))

(defun-sk fra-wrap-pre (tr e r)
  (forall (s final)
    (implies (and (fra-state-p s)
                  (fra-state-p final)
                  (fra-rel tr s final))
             (fra-post e r s final))))

(defun fra-subexpr (whole part)
  (cond ((equal (car whole) :var) nil)
        ((equal (car whole) :neg) (equal (cadr whole) part))
        ((equal (car whole) :add)
         (or (equal (cadr whole) part) (equal (caddr whole) part)))
        (t nil)))

;; Function fields constrained by extensional equality in the source are
;; reconstructed by FRA-ID/FRA-EXEC-TR/FRA-WP/FRA-COMP.  Hence quantifying
;; over such hcode and wcode records is exactly quantifying over their code
;; fields, as done in the obligations below.

(defun-sk fra-evar-obligation ()
  (forall (c)
    (implies (fra-code-p c)
             (implies (fra-wok (fra-id) c) (fra-wok (fra-id) c)))))

(defun-sk fra-neg-o5 (e1 r c3 tr3)
  (forall (c5)
    (implies (fra-code-p c5)
      (implies (fra-wok (fra-wp e1 r) c5)
        (and (fra-wok (fra-wp e1 r) c5) (fra-wok tr3 c3))))))

(defun-sk fra-neg-o4 (e1 r c3 tr3)
  (forall (c4)
    (implies (fra-code-p c4)
      (implies (fra-hok e1 r c4)
        (and (fra-hok e1 r c4) (fra-neg-o5 e1 r c3 tr3))))))

(defun-sk fra-neg-o3 (e e1 r c2)
  (forall (c3)
    (implies (fra-code-p c3)
      (let ((tr3 (fra-comp (fra-id) (fra-exec-tr (fra-ineg r)))))
        (implies (fra-wok tr3 c3)
          (and (fra-subexpr e e1) (fra-neg-o4 e1 r c3 tr3)))))))

(defun-sk fra-neg-obligation (e e1 r)
  (forall (c2)
    (implies (fra-code-p c2)
      (implies (fra-wok (fra-id) c2)
        (and (fra-wok (fra-id) c2) (fra-neg-o3 e e1 r c2))))))

(defun-sk fra-add-o8 (c3 tr3 c5 tr5 c7 tr7)
  (forall (c8)
    (implies (fra-code-p c8)
      (let ((tr8 (fra-comp tr5 tr7)))
        (implies (fra-wok tr8 c8)
          (and (fra-wok tr8 c8) (fra-wok tr3 c3)))))))

(defun-sk fra-add-o7 (e1 r c3 tr3 c5 tr5)
  (forall (c7)
    (implies (fra-code-p c7)
      (let ((tr7 (fra-wp e1 r)))
        (implies (fra-wok tr7 c7)
          (and (and (fra-wok tr7 c7) (fra-wok tr5 c5))
               (fra-add-o8 c3 tr3 c5 tr5 c7 tr7)))))))

(defun-sk fra-add-o6 (e1 r c3 tr3 c5 tr5)
  (forall (c6)
    (implies (fra-code-p c6)
      (implies (fra-hok e1 r c6)
        (and (fra-hok e1 r c6)
             (fra-add-o7 e1 r c3 tr3 c5 tr5))))))

(defun-sk fra-add-o5 (e e1 e2 r c3 tr3)
  (forall (c5)
    (implies (fra-code-p c5)
      (let ((tr5 (fra-wp e2 (+ r 1))))
        (implies (fra-wok tr5 c5)
          (and (fra-subexpr e e1)
               (fra-add-o6 e1 r c3 tr3 c5 tr5)))))))

(defun-sk fra-add-o4 (e e1 e2 r c3 tr3)
  (forall (c4)
    (implies (fra-code-p c4)
      (implies (fra-hok e2 (+ r 1) c4)
        (and (fra-hok e2 (+ r 1) c4)
             (fra-add-o5 e e1 e2 r c3 tr3))))))

(defun-sk fra-add-o3 (e e1 e2 r c2)
  (forall (c3)
    (implies (fra-code-p c3)
      (let ((tr3
             (fra-comp (fra-id)
                       (fra-exec-tr (fra-iadd (+ r 1) r)))))
        (implies (fra-wok tr3 c3)
          (and (fra-subexpr e e2)
               (fra-add-o4 e e1 e2 r c3 tr3)))))))

(defun-sk fra-add-obligation (e e1 e2 r)
  (forall (c2)
    (implies (fra-code-p c2)
      (implies (fra-wok (fra-id) c2)
        (and (fra-wok (fra-id) c2)
             (fra-add-o3 e e1 e2 r c2))))))

(defun fra-branch-obligation (e r)
  (cond ((equal (car e) :var) (fra-evar-obligation))
        ((equal (car e) :neg) (fra-neg-obligation e (cadr e) r))
        ((equal (car e) :add)
         (fra-add-obligation e (cadr e) (caddr e) r))
        (t nil)))

(defun-sk fra-evar-construction (x r c2)
  (exists (c3)
    (and (fra-code-p c3) (fra-wok (fra-id) c3)
         (fra-wok
          (fra-comp (fra-id) (fra-exec-tr (fra-load x r))) c2))))

(defun-sk fra-neg-construction (e1 r c2)
  (exists (c3 c4 c5 c6)
    (let ((tr3 (fra-id))
          (tr4 (fra-comp (fra-id) (fra-exec-tr (fra-ineg r))))
          (tr6 (fra-wp e1 r)))
      (and (fra-code-p c3) (fra-code-p c4)
           (fra-code-p c5) (fra-code-p c6)
           (fra-wok tr3 c3) (fra-wok tr4 c4)
           (fra-hok e1 r c5) (fra-wok tr6 c6)
           (fra-wok (fra-comp tr4 tr6) c2)))))

(defun-sk fra-add-construction (e1 e2 r c2)
  (exists (c3 c4 c5 c6 c7 c8 c9)
    (let ((tr3 (fra-id))
          (tr4 (fra-comp (fra-id)
                         (fra-exec-tr (fra-iadd (+ r 1) r))))
          (tr6 (fra-wp e2 (+ r 1)))
          (tr8 (fra-wp e1 r)))
      (and (fra-code-p c3) (fra-code-p c4) (fra-code-p c5)
           (fra-code-p c6) (fra-code-p c7) (fra-code-p c8)
           (fra-code-p c9)
           (fra-wok tr3 c3) (fra-wok tr4 c4)
           (fra-hok e2 (+ r 1) c5) (fra-wok tr6 c6)
           (fra-hok e1 r c7) (fra-wok tr8 c8)
           (fra-wok (fra-comp tr6 tr8) c9)
           (fra-wok (fra-comp tr4 (fra-comp tr6 tr8)) c2)))))

(defun fra-construction (e r c)
  (cond ((equal (car e) :var)
         (fra-evar-construction (cadr e) r c))
        ((equal (car e) :neg)
         (fra-neg-construction (cadr e) r c))
        ((equal (car e) :add)
         (fra-add-construction (cadr e) (caddr e) r c))
        (t nil)))

(defun fra-final-trans (e r)
  (cond ((equal (car e) :var)
         (fra-comp (fra-id) (fra-exec-tr (fra-load (cadr e) r))))
        ((equal (car e) :neg)
         (fra-comp
          (fra-comp (fra-id) (fra-exec-tr (fra-ineg r)))
          (fra-wp (cadr e) r)))
        ((equal (car e) :add)
         (fra-comp
          (fra-comp (fra-id) (fra-exec-tr (fra-iadd (+ r 1) r)))
          (fra-comp (fra-wp (caddr e) (+ r 1))
                    (fra-wp (cadr e) r))))
        (t (fra-id))))

(defun-sk fra-result-obligation (e r)
  (forall (c)
    (implies (fra-code-p c)
      (implies (fra-hok e r c)
        (and (fra-hok e r c) (fra-hok e r c))))))

(defun-sk fra-all-wcodes (e r)
  (forall (c)
    (implies (fra-code-p c)
      (implies (fra-construction e r c)
        (let ((tr (fra-final-trans e r)))
          (and (and (fra-wok tr c) (fra-wrap-pre tr e r))
               (fra-result-obligation e r)))))))

(defun
  ntp4vc-pearl-register-allocation-infinity-of-registers-compileqtvc-statement
  (r e)
  (implies (and (integerp r) (fra-expr-p e))
           (and (fra-branch-obligation e r)
                (fra-all-wcodes e r))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
