;; Statement-only formalization of thousand-theorems corpus artifact Q420714,
;; "Akra–Bazzi theorem": a finite-branch Akra–Bazzi recurrence is eventually
;; bounded above by its canonical power-and-sum asymptotic expression.
;; This file contains no proof.

(in-package "ACL2")

(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; A reified copy of the real numbers.  The laws below require it to be a
;; Dedekind-complete ordered field and characterize the analytic operations
;; used by the source statement.
(defstub q420714-real-p (real x) t)
(defstub q420714-zero (real) t)
(defstub q420714-one (real) t)
(defstub q420714-add (real x y) t)
(defstub q420714-mul (real x y) t)
(defstub q420714-neg (real x) t)
(defstub q420714-inv (real x) t)
(defstub q420714-less (real x y) t)
(defstub q420714-set-member-p (real-set x) t)
(defstub q420714-exp (real x) t)
(defstub q420714-log (real x) t)
(defstub q420714-rpow (real x y) t)

;; The recurrence data are arbitrary functions of the indicated source types.
(defstub q420714-t-at (t-function n) t)
(defstub q420714-g-at (g-function x) t)
(defstub q420714-a-at (a-function i) t)
(defstub q420714-b-at (b-function i) t)
(defstub q420714-r-at (r-function i n) t)

(defun q420714-sub (real x y)
  (q420714-add real x (q420714-neg real y)))

(defun q420714-div (real x y)
  (q420714-mul real x (q420714-inv real y)))

(defun q420714-leq (real x y)
  (or (equal x y)
      (q420714-less real x y)))

(defun q420714-positive-p (real x)
  (q420714-less real (q420714-zero real) x))

(defun q420714-nonnegative-p (real x)
  (q420714-leq real (q420714-zero real) x))

(defun q420714-abs (real x)
  (if (q420714-less real x (q420714-zero real))
      (q420714-neg real x)
    x))

(defun q420714-nat-cast (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q420714-zero real)
    (q420714-add
     real
     (q420714-one real)
     (q420714-nat-cast real (- (nfix n) 1)))))

(defun q420714-real-nat-power (real x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q420714-one real)
    (q420714-mul
     real
     x
     (q420714-real-nat-power real x (- (nfix n) 1)))))

(defun q420714-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (nfix n)
       (q420714-factorial (- (nfix n) 1)))))

(defun q420714-exp-prefix (real x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (q420714-zero real)
    (let* ((k (- (nfix terms) 1))
           (previous (q420714-exp-prefix real x k))
           (numerator (q420714-real-nat-power real x k))
           (denominator
            (q420714-nat-cast real (q420714-factorial k))))
      (q420714-add
       real
       previous
       (q420714-div real numerator denominator)))))

(defun-sk q420714-field-laws-p (real)
  (forall (x y z)
    (and
     (q420714-real-p real (q420714-zero real))
     (q420714-real-p real (q420714-one real))
     (not (equal (q420714-zero real) (q420714-one real)))
     (implies
      (q420714-real-p real x)
      (and
       (q420714-real-p real (q420714-neg real x))
       (q420714-real-p real (q420714-inv real x))
       (equal
        (q420714-add real x (q420714-zero real))
        x)
       (equal
        (q420714-add real x (q420714-neg real x))
        (q420714-zero real))
       (equal
        (q420714-mul real x (q420714-one real))
        x)
       (equal
        (q420714-inv real (q420714-zero real))
        (q420714-zero real))
       (implies
        (not (equal x (q420714-zero real)))
        (equal
         (q420714-mul real x (q420714-inv real x))
         (q420714-one real)))))
     (implies
      (and (q420714-real-p real x)
           (q420714-real-p real y))
      (and
       (q420714-real-p real (q420714-add real x y))
       (q420714-real-p real (q420714-mul real x y))
       (equal
        (q420714-add real x y)
        (q420714-add real y x))
       (equal
        (q420714-mul real x y)
        (q420714-mul real y x))))
     (implies
      (and (q420714-real-p real x)
           (q420714-real-p real y)
           (q420714-real-p real z))
      (and
       (equal
        (q420714-add real (q420714-add real x y) z)
        (q420714-add real x (q420714-add real y z)))
       (equal
        (q420714-mul real (q420714-mul real x y) z)
        (q420714-mul real x (q420714-mul real y z)))
       (equal
        (q420714-mul real x (q420714-add real y z))
        (q420714-add
         real
         (q420714-mul real x y)
         (q420714-mul real x z))))))))

(defun-sk q420714-order-laws-p (real)
  (forall (x y z)
    (and
     (implies
      (q420714-real-p real x)
      (not (q420714-less real x x)))
     (implies
      (and (q420714-real-p real x)
           (q420714-real-p real y))
      (or (q420714-less real x y)
          (equal x y)
          (q420714-less real y x)))
     (implies
      (and (q420714-real-p real x)
           (q420714-real-p real y)
           (q420714-real-p real z)
           (q420714-less real x y)
           (q420714-less real y z))
      (q420714-less real x z))
     (implies
      (and (q420714-real-p real x)
           (q420714-real-p real y)
           (q420714-real-p real z)
           (q420714-less real x y))
      (q420714-less
       real
       (q420714-add real x z)
       (q420714-add real y z)))
     (implies
      (and (q420714-real-p real x)
           (q420714-real-p real y)
           (q420714-less real (q420714-zero real) x)
           (q420714-less real (q420714-zero real) y))
      (q420714-less
       real
       (q420714-zero real)
       (q420714-mul real x y))))))

(defun-sk q420714-valid-real-set-p (real real-set)
  (forall (x)
    (implies
     (q420714-set-member-p real-set x)
     (q420714-real-p real x))))

(defun-sk q420714-real-set-nonempty-p (real-set)
  (exists (x)
    (q420714-set-member-p real-set x)))

(defun-sk q420714-is-upper-bound-p (real real-set upper)
  (forall (x)
    (implies
     (q420714-set-member-p real-set x)
     (q420714-leq real x upper))))

(defun-sk q420714-real-set-bounded-above-p (real real-set)
  (exists (upper)
    (and
     (q420714-real-p real upper)
     (q420714-is-upper-bound-p real real-set upper))))

(defun-sk q420714-is-least-upper-bound-p
  (real real-set supremum)
  (forall (upper)
    (implies
     (and
      (q420714-real-p real upper)
      (q420714-is-upper-bound-p real real-set upper))
     (q420714-leq real supremum upper))))

(defun q420714-is-supremum-p (real real-set supremum)
  (and
   (q420714-real-p real supremum)
   (q420714-is-upper-bound-p real real-set supremum)
   (q420714-is-least-upper-bound-p real real-set supremum)))

(defun-sk q420714-supremum-exists-p (real real-set)
  (exists (supremum)
    (q420714-is-supremum-p real real-set supremum)))

(defun-sk q420714-dedekind-complete-p (real)
  (forall (real-set)
    (implies
     (and
      (q420714-valid-real-set-p real real-set)
      (q420714-real-set-nonempty-p real-set)
      (q420714-real-set-bounded-above-p real real-set))
     (q420714-supremum-exists-p real real-set))))

(defun-sk q420714-exp-tail-p (real x epsilon cutoff)
  (forall (terms)
    (implies
     (and (natp terms)
          (<= cutoff terms))
     (q420714-less
      real
      (q420714-abs
       real
       (q420714-sub
        real
        (q420714-exp-prefix real x terms)
        (q420714-exp real x)))
      epsilon))))

(defun-sk q420714-exp-cutoff-exists-p (real x epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q420714-exp-tail-p real x epsilon cutoff))))

(defun-sk q420714-exp-converges-p (real x)
  (forall (epsilon)
    (implies
     (and
      (q420714-real-p real epsilon)
      (q420714-positive-p real epsilon))
     (q420714-exp-cutoff-exists-p real x epsilon))))

(defun-sk q420714-analytic-laws-p (real)
  (forall (x y)
    (and
     (implies
      (q420714-real-p real x)
      (and
       (q420714-real-p real (q420714-exp real x))
       (q420714-real-p real (q420714-log real x))
       (q420714-positive-p real (q420714-exp real x))
       (q420714-exp-converges-p real x)
       (equal
        (q420714-log real (q420714-exp real x))
        x)
       (if (equal x (q420714-zero real))
           (equal
            (q420714-log real x)
            (q420714-zero real))
         (equal
          (q420714-exp real (q420714-log real x))
          (q420714-abs real x)))))
     (implies
      (and
       (q420714-real-p real x)
       (q420714-real-p real y))
      (and
       (q420714-real-p real (q420714-rpow real x y))
       (implies
        (q420714-nonnegative-p real x)
        (equal
         (q420714-rpow real x y)
         (if (equal x (q420714-zero real))
             (if (equal y (q420714-zero real))
                 (q420714-one real)
               (q420714-zero real))
           (q420714-exp
            real
            (q420714-mul real (q420714-log real x) y))))))))))

(defun q420714-real-model-p (real)
  (and
   (q420714-field-laws-p real)
   (q420714-order-laws-p real)
   (q420714-dedekind-complete-p real)
   (q420714-analytic-laws-p real)))

;; The duplicate-free nonempty list alpha is a concrete presentation of the
;; arbitrary nonempty finite branch type from the Lean statement.
(defun q420714-finite-nonempty-carrier-p (alpha)
  (and
   (true-listp alpha)
   (consp alpha)
   (no-duplicatesp-equal alpha)))

(defun-sk q420714-functions-typed-p
  (real alpha t-function g-function a-function b-function r-function)
  (forall (i n x)
    (and
     (implies
      (natp n)
      (q420714-real-p real (q420714-t-at t-function n)))
     (implies
      (q420714-real-p real x)
      (q420714-real-p real (q420714-g-at g-function x)))
     (implies
      (member-equal i alpha)
      (and
       (q420714-real-p real (q420714-a-at a-function i))
       (q420714-real-p real (q420714-b-at b-function i))))
     (implies
      (and (member-equal i alpha)
           (natp n))
      (natp (q420714-r-at r-function i n))))))

(defun-sk q420714-coefficients-p (real alpha a-function b-function)
  (forall (i)
    (implies
     (member-equal i alpha)
     (and
      (q420714-positive-p real (q420714-a-at a-function i))
      (q420714-positive-p real (q420714-b-at b-function i))
      (q420714-less
       real
       (q420714-b-at b-function i)
       (q420714-one real))))))

(defun-sk q420714-g-nonnegative-p (real g-function)
  (forall (x)
    (implies
     (and
      (q420714-real-p real x)
      (q420714-nonnegative-p real x))
     (q420714-nonnegative-p
      real
      (q420714-g-at g-function x)))))

(defun-sk q420714-growth-tail-p
  (real g-function beta c1 c2 cutoff)
  (forall (x u)
    (implies
     (and
      (q420714-real-p real x)
      (q420714-real-p real u)
      (q420714-leq real cutoff x)
      (q420714-leq
       real
       (q420714-mul real beta x)
       u)
      (q420714-leq real u x))
     (and
      (q420714-leq
       real
       (q420714-mul
        real
        c1
        (q420714-g-at g-function x))
       (q420714-g-at g-function u))
      (q420714-leq
       real
       (q420714-g-at g-function u)
       (q420714-mul
        real
        c2
        (q420714-g-at g-function x)))))))

(defun-sk q420714-growth-cutoff-exists-p
  (real g-function beta c1 c2)
  (exists (cutoff)
    (and
     (q420714-real-p real cutoff)
     (q420714-growth-tail-p
      real g-function beta c1 c2 cutoff))))

(defun-sk q420714-growth-constants-exist-p
  (real g-function beta)
  (exists (c1 c2)
    (and
     (q420714-real-p real c1)
     (q420714-real-p real c2)
     (q420714-positive-p real c1)
     (q420714-positive-p real c2)
     (q420714-growth-cutoff-exists-p
      real g-function beta c1 c2))))

(defun-sk q420714-grows-polynomially-p (real g-function)
  (forall (beta)
    (implies
     (and
      (q420714-real-p real beta)
      (q420714-positive-p real beta)
      (q420714-less real beta (q420714-one real)))
     (q420714-growth-constants-exist-p
      real g-function beta))))

(defun q420714-branch-sum
  (real alpha t-function a-function r-function n)
  (if (endp alpha)
      (q420714-zero real)
    (q420714-add
     real
     (q420714-mul
      real
      (q420714-a-at a-function (car alpha))
      (q420714-t-at
       t-function
       (q420714-r-at r-function (car alpha) n)))
     (q420714-branch-sum
      real
      (cdr alpha)
      t-function
      a-function
      r-function
      n))))

(defun-sk q420714-recurrence-equation-p
  (real alpha t-function g-function a-function r-function n0)
  (forall (n)
    (implies
     (and (natp n)
          (<= n0 n))
     (equal
      (q420714-t-at t-function n)
      (q420714-add
       real
       (q420714-branch-sum
        real alpha t-function a-function r-function n)
       (q420714-g-at
        g-function
        (q420714-nat-cast real n)))))))

(defun-sk q420714-base-positive-p (real t-function n0)
  (forall (n)
    (implies
     (and (natp n)
          (< n n0))
     (q420714-positive-p
      real
      (q420714-t-at t-function n)))))

(defun-sk q420714-recursive-arguments-smaller-p
  (alpha r-function n0)
  (forall (i n)
    (implies
     (and
      (member-equal i alpha)
      (natp n)
      (<= n0 n))
     (< (q420714-r-at r-function i n) n))))

(defun-sk q420714-little-o-tail-p
  (real b-function r-function i epsilon cutoff)
  (forall (n)
    (implies
     (and (natp n)
          (<= cutoff n))
     (q420714-leq
      real
      (q420714-abs
       real
       (q420714-sub
        real
        (q420714-nat-cast
         real
         (q420714-r-at r-function i n))
        (q420714-mul
         real
         (q420714-b-at b-function i)
         (q420714-nat-cast real n))))
      (q420714-mul
       real
       epsilon
       (q420714-abs
        real
        (q420714-div
         real
         (q420714-nat-cast real n)
         (q420714-real-nat-power
          real
          (q420714-log
           real
           (q420714-nat-cast real n))
          2))))))))

(defun-sk q420714-little-o-cutoff-exists-p
  (real b-function r-function i epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q420714-little-o-tail-p
      real b-function r-function i epsilon cutoff))))

(defun-sk q420714-branch-approximation-p
  (real b-function r-function i)
  (forall (epsilon)
    (implies
     (and
      (q420714-real-p real epsilon)
      (q420714-positive-p real epsilon))
     (q420714-little-o-cutoff-exists-p
      real b-function r-function i epsilon))))

(defun-sk q420714-all-branch-approximations-p
  (real alpha b-function r-function)
  (forall (i)
    (implies
     (member-equal i alpha)
     (q420714-branch-approximation-p
      real b-function r-function i))))

(defun q420714-akra-bazzi-recurrence-p
  (real alpha t-function g-function a-function b-function r-function n0)
  (and
   (natp n0)
   (< 0 n0)
   (q420714-finite-nonempty-carrier-p alpha)
   (q420714-functions-typed-p
    real alpha t-function g-function a-function b-function r-function)
   (q420714-coefficients-p real alpha a-function b-function)
   (q420714-g-nonnegative-p real g-function)
   (q420714-grows-polynomially-p real g-function)
   (q420714-recurrence-equation-p
    real alpha t-function g-function a-function r-function n0)
   (q420714-base-positive-p real t-function n0)
   (q420714-recursive-arguments-smaller-p alpha r-function n0)
   (q420714-all-branch-approximations-p
    real alpha b-function r-function)))

(defun q420714-coefficient-power-sum
  (real alpha a-function b-function p)
  (if (endp alpha)
      (q420714-zero real)
    (q420714-add
     real
     (q420714-mul
      real
      (q420714-a-at a-function (car alpha))
      (q420714-rpow
       real
       (q420714-b-at b-function (car alpha))
       p))
     (q420714-coefficient-power-sum
      real
      (cdr alpha)
      a-function
      b-function
      p))))

(defun q420714-p-equation-p
  (real alpha a-function b-function p)
  (equal
   (q420714-coefficient-power-sum
    real alpha a-function b-function p)
   (q420714-one real)))

(defun q420714-asymp-series-sum (real g-function p n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q420714-zero real)
    (let* ((u (- (nfix n) 1))
           (u-real (q420714-nat-cast real u))
           (p-plus-one
            (q420714-add real p (q420714-one real)))
           (term
            (q420714-div
             real
             (q420714-g-at g-function u-real)
             (q420714-rpow real u-real p-plus-one))))
      (q420714-add
       real
       (q420714-asymp-series-sum real g-function p u)
       term))))

(defun q420714-asymp-bound (real g-function p n)
  (q420714-mul
   real
   (q420714-rpow
    real
    (q420714-nat-cast real n)
    p)
   (q420714-add
    real
    (q420714-one real)
    (q420714-asymp-series-sum
     real g-function p n))))

(defun-sk q420714-big-o-tail-p
  (real t-function g-function p constant cutoff)
  (forall (n)
    (implies
     (and (natp n)
          (<= cutoff n))
     (q420714-leq
      real
      (q420714-abs
       real
       (q420714-t-at t-function n))
      (q420714-mul
       real
       constant
       (q420714-abs
        real
        (q420714-asymp-bound
         real g-function p n)))))))

(defun-sk q420714-big-o-cutoff-exists-p
  (real t-function g-function p constant)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q420714-big-o-tail-p
      real t-function g-function p constant cutoff))))

(defun-sk q420714-is-big-o-p
  (real t-function g-function p)
  (exists (constant)
    (and
     (q420714-real-p real constant)
     (q420714-positive-p real constant)
     (q420714-big-o-cutoff-exists-p
      real t-function g-function p constant))))

;; Keeping p under this existential mirrors the fact that Mathlib defines it
;; internally as the unique solution of sum_i a_i * b_i^p = 1.
(defun-sk q420714-asymptotic-upper-bound-p
  (real alpha t-function g-function a-function b-function)
  (exists (p)
    (and
     (q420714-real-p real p)
     (q420714-p-equation-p
      real alpha a-function b-function p)
     (q420714-is-big-o-p
      real t-function g-function p))))

(defun thousand-theorems-q420714-akra-bazzi-theorem
  (real alpha t-function g-function a-function b-function r-function n0)
  (implies
   (and
    (q420714-real-model-p real)
    (q420714-akra-bazzi-recurrence-p
     real
     alpha
     t-function
     g-function
     a-function
     b-function
     r-function
     n0))
   (q420714-asymptotic-upper-bound-p
    real
    alpha
    t-function
    g-function
    a-function
    b-function)))

(value-triple :itpeval-statement-checked)
:q
