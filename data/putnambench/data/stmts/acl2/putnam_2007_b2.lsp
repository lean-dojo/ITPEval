;; Statement-only formalization of PutnamBench corpus artifact putnam_2007_b2:
;; an integral bound for every arbitrary continuously differentiable real
;; function on [0,1] whose integral is zero. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces for an arbitrary real field, its subsets, and an
;; arbitrary real-valued function.  The context parameter keeps the function
;; and scalar structure generic; none of them is represented by a finite table.

(defstub p07b2-real-p (ctx x) t)
(defstub p07b2-zero (ctx) t)
(defstub p07b2-one (ctx) t)
(defstub p07b2-add (ctx x y) t)
(defstub p07b2-mul (ctx x y) t)
(defstub p07b2-neg (ctx x) t)
(defstub p07b2-inv (ctx x) t)
(defstub p07b2-lt (ctx x y) t)
(defstub p07b2-set-member-p (ctx set x) t)
(defstub p07b2-f (ctx x) t)

(defun p07b2-sub (ctx x y)
  (p07b2-add ctx x (p07b2-neg ctx y)))

(defun p07b2-div (ctx x y)
  (p07b2-mul ctx x (p07b2-inv ctx y)))

(defun p07b2-le (ctx x y)
  (not (p07b2-lt ctx y x)))

(defun p07b2-abs (ctx x)
  (if (p07b2-lt ctx x (p07b2-zero ctx))
      (p07b2-neg ctx x)
    x))

(defun p07b2-nat-value (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p07b2-zero ctx)
    (p07b2-add
     ctx
     (p07b2-one ctx)
     (p07b2-nat-value ctx (1- n)))))

(defun p07b2-positive-p (ctx x)
  (and
   (p07b2-real-p ctx x)
   (p07b2-lt ctx (p07b2-zero ctx) x)))

(defun p07b2-in-closed-unit-interval-p (ctx x)
  (and
   (p07b2-real-p ctx x)
   (p07b2-le ctx (p07b2-zero ctx) x)
   (p07b2-le ctx x (p07b2-one ctx))))

(defun p07b2-in-open-unit-interval-p (ctx x)
  (and
   (p07b2-real-p ctx x)
   (p07b2-lt ctx (p07b2-zero ctx) x)
   (p07b2-lt ctx x (p07b2-one ctx))))

;; The scalar carrier is a complete Archimedean ordered field, characterizing
;; the real numbers up to ordered-field isomorphism.

(defun-sk p07b2-operation-closure-p (ctx)
  (forall (x y)
    (and
     (p07b2-real-p ctx (p07b2-zero ctx))
     (p07b2-real-p ctx (p07b2-one ctx))
     (implies
      (p07b2-real-p ctx x)
      (and
       (p07b2-real-p ctx (p07b2-neg ctx x))
       (p07b2-real-p ctx (p07b2-inv ctx x))))
     (implies
      (and (p07b2-real-p ctx x)
           (p07b2-real-p ctx y))
      (and
       (p07b2-real-p ctx (p07b2-add ctx x y))
       (p07b2-real-p ctx (p07b2-mul ctx x y)))))))

(defun-sk p07b2-unary-field-laws-p (ctx)
  (forall (x)
    (implies
     (p07b2-real-p ctx x)
     (let ((zero (p07b2-zero ctx))
           (one (p07b2-one ctx)))
       (and
        (equal (p07b2-add ctx zero x) x)
        (equal (p07b2-add ctx x zero) x)
        (equal (p07b2-add ctx x (p07b2-neg ctx x)) zero)
        (equal (p07b2-mul ctx one x) x)
        (equal (p07b2-mul ctx x one) x)
        (implies
         (equal x zero)
         (equal (p07b2-inv ctx x) zero))
        (implies
         (not (equal x zero))
         (equal (p07b2-mul ctx x (p07b2-inv ctx x)) one)))))))

(defun-sk p07b2-binary-field-laws-p (ctx)
  (forall (x y)
    (implies
     (and (p07b2-real-p ctx x)
          (p07b2-real-p ctx y))
     (and
      (equal (p07b2-add ctx x y)
             (p07b2-add ctx y x))
      (equal (p07b2-mul ctx x y)
             (p07b2-mul ctx y x))))))

(defun-sk p07b2-ternary-field-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (p07b2-real-p ctx x)
      (p07b2-real-p ctx y)
      (p07b2-real-p ctx z))
     (and
      (equal
       (p07b2-add ctx (p07b2-add ctx x y) z)
       (p07b2-add ctx x (p07b2-add ctx y z)))
      (equal
       (p07b2-mul ctx (p07b2-mul ctx x y) z)
       (p07b2-mul ctx x (p07b2-mul ctx y z)))
      (equal
       (p07b2-mul ctx x (p07b2-add ctx y z))
       (p07b2-add
        ctx
        (p07b2-mul ctx x y)
        (p07b2-mul ctx x z)))))))

(defun-sk p07b2-order-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (p07b2-real-p ctx x)
      (p07b2-real-p ctx y)
      (p07b2-real-p ctx z))
     (and
      (not (p07b2-lt ctx x x))
      (or (p07b2-lt ctx x y)
          (equal x y)
          (p07b2-lt ctx y x))
      (implies
       (and (p07b2-lt ctx x y)
            (p07b2-lt ctx y z))
       (p07b2-lt ctx x z))
      (implies
       (p07b2-lt ctx x y)
       (p07b2-lt
        ctx
        (p07b2-add ctx x z)
        (p07b2-add ctx y z)))
      (implies
       (and
        (p07b2-lt ctx (p07b2-zero ctx) x)
        (p07b2-lt ctx (p07b2-zero ctx) y))
       (p07b2-lt
        ctx
        (p07b2-zero ctx)
        (p07b2-mul ctx x y)))))))

(defun-sk p07b2-valid-real-set-p (ctx set)
  (forall (x)
    (implies
     (p07b2-set-member-p ctx set x)
     (p07b2-real-p ctx x))))

(defun-sk p07b2-set-nonempty-p (ctx set)
  (exists (x)
    (and
     (p07b2-real-p ctx x)
     (p07b2-set-member-p ctx set x))))

(defun-sk p07b2-upper-bound-p (ctx set bound)
  (forall (x)
    (implies
     (p07b2-set-member-p ctx set x)
     (p07b2-le ctx x bound))))

(defun-sk p07b2-bounded-above-p (ctx set)
  (exists (bound)
    (and
     (p07b2-real-p ctx bound)
     (p07b2-upper-bound-p ctx set bound))))

(defun-sk p07b2-least-upper-bound-p (ctx set supremum)
  (forall (bound)
    (and
     (p07b2-real-p ctx supremum)
     (p07b2-upper-bound-p ctx set supremum)
     (implies
      (and
       (p07b2-real-p ctx bound)
       (p07b2-upper-bound-p ctx set bound))
      (p07b2-le ctx supremum bound)))))

(defun-sk p07b2-supremum-exists-p (ctx set)
  (exists (supremum)
    (p07b2-least-upper-bound-p ctx set supremum)))

(defun-sk p07b2-dedekind-complete-p (ctx)
  (forall (set)
    (implies
     (and
      (p07b2-valid-real-set-p ctx set)
      (p07b2-set-nonempty-p ctx set)
      (p07b2-bounded-above-p ctx set))
     (p07b2-supremum-exists-p ctx set))))

(defun-sk p07b2-archimedean-witness-p (ctx x)
  (exists (n)
    (and
     (natp n)
     (p07b2-lt ctx x (p07b2-nat-value ctx n)))))

(defun-sk p07b2-archimedean-p (ctx)
  (forall (x)
    (implies
     (p07b2-real-p ctx x)
     (p07b2-archimedean-witness-p ctx x))))

(defun p07b2-real-structure-p (ctx)
  (and
   (p07b2-operation-closure-p ctx)
   (p07b2-unary-field-laws-p ctx)
   (p07b2-binary-field-laws-p ctx)
   (p07b2-ternary-field-laws-p ctx)
   (p07b2-order-laws-p ctx)
   (not (equal (p07b2-zero ctx) (p07b2-one ctx)))
   (p07b2-lt ctx (p07b2-zero ctx) (p07b2-one ctx))
   (p07b2-dedekind-complete-p ctx)
   (p07b2-archimedean-p ctx)))

(defun-sk p07b2-f-real-valued-p (ctx)
  (forall (x)
    (implies
     (p07b2-real-p ctx x)
     (p07b2-real-p ctx (p07b2-f ctx x)))))

;; Differentiability uses the epsilon-delta linear remainder definition over
;; the full real domain.  The derivative witness remains internal.

(defun p07b2-derivative-error (ctx x y derivative)
  (p07b2-abs
   ctx
   (p07b2-sub
    ctx
    (p07b2-sub
     ctx
     (p07b2-f ctx y)
     (p07b2-f ctx x))
    (p07b2-mul
     ctx
     derivative
     (p07b2-sub ctx y x)))))

(defun-sk p07b2-derivative-delta-p
    (ctx x derivative epsilon delta)
  (forall (y)
    (implies
     (and
      (p07b2-real-p ctx y)
      (p07b2-lt
       ctx
       (p07b2-zero ctx)
       (p07b2-abs ctx (p07b2-sub ctx y x)))
      (p07b2-lt
       ctx
       (p07b2-abs ctx (p07b2-sub ctx y x))
       delta))
     (p07b2-le
      ctx
      (p07b2-derivative-error ctx x y derivative)
      (p07b2-mul
       ctx
       epsilon
       (p07b2-abs ctx (p07b2-sub ctx y x)))))))

(defun-sk p07b2-derivative-epsilon-p
    (ctx x derivative epsilon)
  (exists (delta)
    (and
     (p07b2-positive-p ctx delta)
     (p07b2-derivative-delta-p
      ctx x derivative epsilon delta))))

(defun-sk p07b2-derivative-at-p (ctx x derivative)
  (forall (epsilon)
    (and
     (p07b2-real-p ctx derivative)
     (implies
      (p07b2-positive-p ctx epsilon)
      (p07b2-derivative-epsilon-p
       ctx x derivative epsilon)))))

(defun-sk p07b2-differentiable-at-p (ctx x)
  (exists (derivative)
    (p07b2-derivative-at-p ctx x derivative)))

(defchoose p07b2-chosen-derivative
    (derivative)
    (ctx x)
  (p07b2-derivative-at-p ctx x derivative))

(defun p07b2-derivative (ctx x)
  (if (p07b2-differentiable-at-p ctx x)
      (p07b2-chosen-derivative ctx x)
    (p07b2-zero ctx)))

(defun-sk p07b2-derivative-continuity-delta-p
    (ctx x epsilon delta)
  (forall (y)
    (implies
     (and
      (p07b2-in-closed-unit-interval-p ctx y)
      (p07b2-lt
       ctx
       (p07b2-abs ctx (p07b2-sub ctx y x))
       delta))
     (p07b2-lt
      ctx
      (p07b2-abs
       ctx
       (p07b2-sub
        ctx
        (p07b2-derivative ctx y)
        (p07b2-derivative ctx x)))
      epsilon))))

(defun-sk p07b2-derivative-continuous-at-p
    (ctx x epsilon)
  (exists (delta)
    (and
     (p07b2-positive-p ctx delta)
     (p07b2-derivative-continuity-delta-p
      ctx x epsilon delta))))

(defun-sk p07b2-c1-on-unit-interval-p (ctx)
  (forall (x epsilon)
    (implies
     (p07b2-in-closed-unit-interval-p ctx x)
     (and
      (p07b2-differentiable-at-p ctx x)
      (implies
       (p07b2-positive-p ctx epsilon)
       (p07b2-derivative-continuous-at-p
        ctx x epsilon))))))

;; Exact Riemann integration.  A finite tagged partition is a witness used in
;; the definition of the integral; it does not restrict the function or the
;; real interval to a finite representation.

(defun p07b2-tagged-chain-p (ctx points tags)
  (declare (xargs :measure (acl2-count tags)))
  (if (endp tags)
      (and
       (consp points)
       (endp (cdr points))
       (p07b2-real-p ctx (car points)))
    (and
     (consp points)
     (consp (cdr points))
     (p07b2-real-p ctx (car points))
     (p07b2-real-p ctx (cadr points))
     (p07b2-real-p ctx (car tags))
     (p07b2-lt ctx (car points) (cadr points))
     (p07b2-le ctx (car points) (car tags))
     (p07b2-le ctx (car tags) (cadr points))
     (p07b2-tagged-chain-p
      ctx (cdr points) (cdr tags)))))

(defun p07b2-tagged-partition-p (ctx a b points tags)
  (and
   (true-listp points)
   (true-listp tags)
   (consp points)
   (equal (car points) a)
   (equal (car (last points)) b)
   (p07b2-tagged-chain-p ctx points tags)))

(defun p07b2-mesh-less-than-p (ctx points delta)
  (declare (xargs :measure (acl2-count points)))
  (if (or (endp points) (endp (cdr points)))
      t
    (and
     (p07b2-lt
      ctx
      (p07b2-sub ctx (cadr points) (car points))
      delta)
     (p07b2-mesh-less-than-p ctx (cdr points) delta))))

(defun p07b2-riemann-sum (ctx points tags)
  (declare (xargs :measure (acl2-count tags)))
  (if (or (endp tags)
          (endp points)
          (endp (cdr points)))
      (p07b2-zero ctx)
    (p07b2-add
     ctx
     (p07b2-mul
      ctx
      (p07b2-f ctx (car tags))
      (p07b2-sub ctx (cadr points) (car points)))
     (p07b2-riemann-sum
      ctx (cdr points) (cdr tags)))))

(defun-sk p07b2-fine-partition-exists-p
    (ctx a b delta)
  (exists (points tags)
    (and
     (p07b2-tagged-partition-p ctx a b points tags)
     (p07b2-mesh-less-than-p ctx points delta))))

(defun-sk p07b2-riemann-accuracy-p
    (ctx a b integral epsilon delta)
  (forall (points tags)
    (implies
     (and
      (p07b2-tagged-partition-p ctx a b points tags)
      (p07b2-mesh-less-than-p ctx points delta))
     (p07b2-lt
      ctx
      (p07b2-abs
       ctx
       (p07b2-sub
        ctx
        (p07b2-riemann-sum ctx points tags)
        integral))
      epsilon))))

(defun-sk p07b2-integral-epsilon-p
    (ctx a b integral epsilon)
  (exists (delta)
    (and
     (p07b2-positive-p ctx delta)
     (p07b2-fine-partition-exists-p ctx a b delta)
     (p07b2-riemann-accuracy-p
      ctx a b integral epsilon delta))))

(defun-sk p07b2-has-integral-p (ctx a b integral)
  (forall (epsilon)
    (and
     (p07b2-real-p ctx integral)
     (implies
      (p07b2-positive-p ctx epsilon)
      (p07b2-integral-epsilon-p
       ctx a b integral epsilon)))))

(defun-sk p07b2-integrable-p (ctx a b)
  (exists (integral)
    (p07b2-has-integral-p ctx a b integral)))

(defchoose p07b2-chosen-integral
    (integral)
    (ctx a b)
  (p07b2-has-integral-p ctx a b integral))

(defun p07b2-integral (ctx a b)
  (if (p07b2-integrable-p ctx a b)
      (p07b2-chosen-integral ctx a b)
    (p07b2-zero ctx)))

;; The explicit maximum assumptions follow the Lean/Rocq ground truths:
;; MAXIMUM is both attained and an upper bound for |f'| on [0,1].

(defun-sk p07b2-maximum-attained-p (ctx maximum)
  (exists (x)
    (and
     (p07b2-in-closed-unit-interval-p ctx x)
     (equal
      (p07b2-abs ctx (p07b2-derivative ctx x))
      maximum))))

(defun-sk p07b2-maximum-upper-bound-p (ctx maximum)
  (forall (x)
    (implies
     (p07b2-in-closed-unit-interval-p ctx x)
     (p07b2-le
      ctx
      (p07b2-abs ctx (p07b2-derivative ctx x))
      maximum))))

(defun-sk p07b2-bound-for-all-alpha-p (ctx maximum)
  (forall (alpha)
    (implies
     (p07b2-in-open-unit-interval-p ctx alpha)
     (p07b2-le
      ctx
      (p07b2-abs
       ctx
       (p07b2-integral
        ctx (p07b2-zero ctx) alpha))
      (p07b2-mul
       ctx
       (p07b2-inv ctx (p07b2-nat-value ctx 8))
       maximum)))))

(defun-sk putnam-2007-b2-statement ()
  (forall (ctx maximum)
    (implies
     (and
      (p07b2-real-structure-p ctx)
      (p07b2-f-real-valued-p ctx)
      (p07b2-c1-on-unit-interval-p ctx)
      (p07b2-has-integral-p
       ctx
       (p07b2-zero ctx)
       (p07b2-one ctx)
       (p07b2-zero ctx))
      (p07b2-real-p ctx maximum)
      (p07b2-maximum-attained-p ctx maximum)
      (p07b2-maximum-upper-bound-p ctx maximum))
     (p07b2-bound-for-all-alpha-p ctx maximum))))

(value-triple :itpeval-statement-checked)
:q
