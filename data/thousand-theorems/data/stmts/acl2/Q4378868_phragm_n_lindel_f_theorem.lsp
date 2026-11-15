;; Statement-only formalization of thousand-theorems corpus artifact Q4378868,
;; "Phragmén–Lindelöf theorem": a complex-differentiable function on a
;; horizontal strip, with subcritical double-exponential growth and a common
;; norm bound on both boundary lines, obeys that bound throughout the closed
;; strip. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Conservative interfaces present the real field, arbitrary subsets of it,
;; an arbitrary complex normed space, and the arbitrary source function.
;; Every field, norm, analytic, typing, and growth condition used below is an
;; explicit hypothesis of the final statement predicate.

;; A Dedekind-complete ordered-field presentation of the real numbers.

(defstub q4378868-r-member-p (real value) t)
(defstub q4378868-r-zero (real) t)
(defstub q4378868-r-one (real) t)
(defstub q4378868-r-add (real left right) t)
(defstub q4378868-r-multiply (real left right) t)
(defstub q4378868-r-negate (real value) t)
(defstub q4378868-r-inverse (real value) t)
(defstub q4378868-r-less (real left right) t)
(defstub q4378868-r-supremum (real set) t)
(defstub q4378868-r-set-member-p (real set value) t)

(defun q4378868-r-leq (real left right)
  (not (q4378868-r-less real right left)))

(defun q4378868-r-subtract (real left right)
  (q4378868-r-add
   real left (q4378868-r-negate real right)))

(defun q4378868-r-divide (real numerator denominator)
  (q4378868-r-multiply
   real numerator (q4378868-r-inverse real denominator)))

(defun q4378868-r-absolute-value (real value)
  (if (q4378868-r-less
       real value (q4378868-r-zero real))
      (q4378868-r-negate real value)
    value))

(defun q4378868-r-positive-p (real value)
  (and
   (q4378868-r-member-p real value)
   (q4378868-r-less
    real (q4378868-r-zero real) value)))

(defun-sk q4378868-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q4378868-r-member-p real x)
      (q4378868-r-member-p real y)
      (q4378868-r-member-p real z))
     (let* ((zero (q4378868-r-zero real))
            (one (q4378868-r-one real))
            (xy-add (q4378868-r-add real x y))
            (yz-add (q4378868-r-add real y z))
            (xy-mul (q4378868-r-multiply real x y))
            (yz-mul (q4378868-r-multiply real y z))
            (neg-x (q4378868-r-negate real x))
            (inv-x (q4378868-r-inverse real x)))
       (and
        (q4378868-r-member-p real xy-add)
        (q4378868-r-member-p real xy-mul)
        (q4378868-r-member-p real neg-x)
        (q4378868-r-member-p real inv-x)
        (equal
         (q4378868-r-add real xy-add z)
         (q4378868-r-add real x yz-add))
        (equal xy-add (q4378868-r-add real y x))
        (equal (q4378868-r-add real x zero) x)
        (equal (q4378868-r-add real x neg-x) zero)
        (equal
         (q4378868-r-multiply real xy-mul z)
         (q4378868-r-multiply real x yz-mul))
        (equal xy-mul (q4378868-r-multiply real y x))
        (equal (q4378868-r-multiply real x one) x)
        (equal (q4378868-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q4378868-r-multiply real x inv-x)
          one))
        (equal
         (q4378868-r-multiply real x yz-add)
         (q4378868-r-add
          real
          (q4378868-r-multiply real x y)
          (q4378868-r-multiply real x z))))))))

(defun-sk q4378868-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q4378868-r-member-p real x)
      (q4378868-r-member-p real y)
      (q4378868-r-member-p real z))
     (let ((zero (q4378868-r-zero real)))
       (and
        (not (q4378868-r-less real x x))
        (or
         (equal x y)
         (q4378868-r-less real x y)
         (q4378868-r-less real y x))
        (implies
         (and
          (q4378868-r-less real x y)
          (q4378868-r-less real y z))
         (q4378868-r-less real x z))
        (implies
         (q4378868-r-less real x y)
         (q4378868-r-less
          real
          (q4378868-r-add real x z)
          (q4378868-r-add real y z)))
        (implies
         (and
          (q4378868-r-less real zero x)
          (q4378868-r-less real zero y))
         (q4378868-r-less
          real zero
          (q4378868-r-multiply real x y))))))))

(defun-sk q4378868-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q4378868-r-member-p real x)
     (q4378868-r-set-member-p real set x))))

(defun-sk q4378868-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q4378868-r-member-p real x)
      (q4378868-r-set-member-p real set x))
     (q4378868-r-leq real x bound))))

(defun-sk q4378868-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q4378868-r-member-p real bound)
     (q4378868-r-upper-bound-p real set bound))))

(defun-sk q4378868-r-least-upper-bound-p
    (real set supremum)
  (forall (bound)
    (implies
     (and
      (q4378868-r-member-p real bound)
      (q4378868-r-upper-bound-p real set bound))
     (q4378868-r-leq real supremum bound))))

(defun q4378868-r-supremum-p (real set supremum)
  (and
   (q4378868-r-member-p real supremum)
   (q4378868-r-upper-bound-p real set supremum)
   (q4378868-r-least-upper-bound-p
    real set supremum)))

(defun-sk q4378868-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q4378868-r-set-nonempty-p real set)
      (q4378868-r-bounded-above-p real set))
     (q4378868-r-supremum-p
      real set (q4378868-r-supremum real set)))))

(defun q4378868-real-field-p (real)
  (let ((zero (q4378868-r-zero real))
        (one (q4378868-r-one real)))
    (and
     (q4378868-r-member-p real zero)
     (q4378868-r-member-p real one)
     (not (equal zero one))
     (q4378868-r-field-laws-p real)
     (q4378868-r-order-laws-p real)
     (q4378868-r-less real zero one)
     (q4378868-r-dedekind-complete-p real))))

;; Principal square root and arbitrary real-valued functions.

(defstub q4378868-r-square-root (real square-root value) t)
(defstub q4378868-r-function-value (real function value) t)

(defun-sk q4378868-r-square-root-laws-p
    (real square-root)
  (forall (x)
    (implies
     (q4378868-r-member-p real x)
     (let ((zero (q4378868-r-zero real))
           (root
            (q4378868-r-square-root
             real square-root x)))
       (if (q4378868-r-less real x zero)
           (equal root zero)
         (and
          (q4378868-r-member-p real root)
          (q4378868-r-leq real zero root)
          (equal
           (q4378868-r-multiply real root root)
           x)))))))

(defun-sk q4378868-r-function-typed-p
    (real function)
  (forall (x)
    (implies
     (q4378868-r-member-p real x)
     (q4378868-r-member-p
      real
      (q4378868-r-function-value
       real function x)))))

;; Complex numbers are pairs (real-part . imaginary-part).

(defun q4378868-complex-p (real value)
  (and
   (consp value)
   (q4378868-r-member-p real (car value))
   (q4378868-r-member-p real (cdr value))))

(defun q4378868-c-zero (real)
  (cons
   (q4378868-r-zero real)
   (q4378868-r-zero real)))

(defun q4378868-c-one (real)
  (cons
   (q4378868-r-one real)
   (q4378868-r-zero real)))

(defun q4378868-c-add (real left right)
  (cons
   (q4378868-r-add real (car left) (car right))
   (q4378868-r-add real (cdr left) (cdr right))))

(defun q4378868-c-negate (real value)
  (cons
   (q4378868-r-negate real (car value))
   (q4378868-r-negate real (cdr value))))

(defun q4378868-c-subtract (real left right)
  (q4378868-c-add
   real left (q4378868-c-negate real right)))

(defun q4378868-c-multiply (real left right)
  (cons
   (q4378868-r-subtract
    real
    (q4378868-r-multiply
     real (car left) (car right))
    (q4378868-r-multiply
     real (cdr left) (cdr right)))
   (q4378868-r-add
    real
    (q4378868-r-multiply
     real (car left) (cdr right))
    (q4378868-r-multiply
     real (cdr left) (car right)))))

(defun q4378868-c-norm-square (real value)
  (q4378868-r-add
   real
   (q4378868-r-multiply
    real (car value) (car value))
   (q4378868-r-multiply
    real (cdr value) (cdr value))))

(defun q4378868-c-norm (real square-root value)
  (q4378868-r-square-root
   real square-root
   (q4378868-c-norm-square real value)))

;; An arbitrary normed vector space over the represented complex field.

(defstub q4378868-e-member-p (space value) t)
(defstub q4378868-e-zero (space) t)
(defstub q4378868-e-add (space left right) t)
(defstub q4378868-e-negate (space value) t)
(defstub q4378868-e-smul (space scalar value) t)
(defstub q4378868-e-norm (real space value) t)
(defstub q4378868-function-value (function complex-value) t)

(defun q4378868-e-subtract (space left right)
  (q4378868-e-add
   space left (q4378868-e-negate space right)))

(defun-sk q4378868-e-vector-laws-p
    (real space)
  (forall (a b x y z)
    (implies
     (and
      (q4378868-complex-p real a)
      (q4378868-complex-p real b)
      (q4378868-e-member-p space x)
      (q4378868-e-member-p space y)
      (q4378868-e-member-p space z))
     (let* ((zero (q4378868-e-zero space))
            (xy (q4378868-e-add space x y))
            (yz (q4378868-e-add space y z))
            (neg-x (q4378868-e-negate space x))
            (a-x (q4378868-e-smul space a x)))
       (and
        (q4378868-e-member-p space xy)
        (q4378868-e-member-p space neg-x)
        (q4378868-e-member-p space a-x)
        (equal
         (q4378868-e-add space xy z)
         (q4378868-e-add space x yz))
        (equal xy (q4378868-e-add space y x))
        (equal (q4378868-e-add space x zero) x)
        (equal (q4378868-e-add space x neg-x) zero)
        (equal
         (q4378868-e-smul
          space (q4378868-c-one real) x)
         x)
        (equal
         (q4378868-e-smul
          space
          (q4378868-c-multiply real a b)
          x)
         (q4378868-e-smul space a
          (q4378868-e-smul space b x)))
        (equal
         (q4378868-e-smul
          space (q4378868-c-add real a b) x)
         (q4378868-e-add
          space
          (q4378868-e-smul space a x)
          (q4378868-e-smul space b x)))
        (equal
         (q4378868-e-smul space a xy)
         (q4378868-e-add
          space
          (q4378868-e-smul space a x)
          (q4378868-e-smul space a y)))
        (equal
         (q4378868-e-smul
          space (q4378868-c-zero real) x)
         zero))))))

(defun-sk q4378868-e-norm-laws-p
    (real square-root space)
  (forall (a x y)
    (implies
     (and
      (q4378868-complex-p real a)
      (q4378868-e-member-p space x)
      (q4378868-e-member-p space y))
     (let* ((zero-r (q4378868-r-zero real))
            (zero-e (q4378868-e-zero space))
            (norm-x (q4378868-e-norm real space x))
            (norm-y (q4378868-e-norm real space y)))
       (and
        (q4378868-r-member-p real norm-x)
        (q4378868-r-member-p real norm-y)
        (q4378868-r-leq real zero-r norm-x)
        (iff (equal norm-x zero-r)
             (equal x zero-e))
        (equal
         (q4378868-e-norm
          real space (q4378868-e-negate space x))
         norm-x)
        (equal
         (q4378868-e-norm
          real space
          (q4378868-e-smul space a x))
         (q4378868-r-multiply
          real
          (q4378868-c-norm real square-root a)
          norm-x))
        (q4378868-r-leq
         real
         (q4378868-e-norm
          real space (q4378868-e-add space x y))
         (q4378868-r-add real norm-x norm-y)))))))

(defun q4378868-complex-normed-space-p
    (real square-root space)
  (and
   (q4378868-e-member-p
    space (q4378868-e-zero space))
   (q4378868-e-vector-laws-p real space)
   (q4378868-e-norm-laws-p
    real square-root space)))

(defun-sk q4378868-function-typed-p
    (real space function)
  (forall (z)
    (implies
     (q4378868-complex-p real z)
     (q4378868-e-member-p
      space
      (q4378868-function-value function z)))))

;; Open and closed horizontal strips.

(defun q4378868-open-strip-p
    (real lower upper z)
  (and
   (q4378868-complex-p real z)
   (q4378868-r-less real lower (cdr z))
   (q4378868-r-less real (cdr z) upper)))

(defun q4378868-closed-strip-p
    (real lower upper z)
  (and
   (q4378868-complex-p real z)
   (q4378868-r-leq real lower (cdr z))
   (q4378868-r-leq real (cdr z) upper)))

;; The closure of an empty open strip is empty.

(defun q4378868-strip-closure-p
    (real lower upper z)
  (and
   (q4378868-r-less real lower upper)
   (q4378868-closed-strip-p
    real lower upper z)))

;; Continuity on the closure of the open strip.

(defun-sk q4378868-continuity-radius-p
    (real square-root space function lower upper
     point epsilon radius)
  (forall (y)
    (implies
     (and
      (q4378868-strip-closure-p
       real lower upper y)
      (q4378868-r-less
       real
       (q4378868-c-norm
        real square-root
        (q4378868-c-subtract real y point))
       radius))
     (q4378868-r-less
      real
      (q4378868-e-norm
       real space
       (q4378868-e-subtract
        space
        (q4378868-function-value function y)
        (q4378868-function-value function point)))
      epsilon))))

(defun-sk q4378868-continuity-radius-exists-p
    (real square-root space function lower upper
     point epsilon)
  (exists (radius)
    (and
     (q4378868-r-positive-p real radius)
     (q4378868-continuity-radius-p
      real square-root space function lower upper
      point epsilon radius))))

(defun-sk q4378868-continuous-within-at-p
    (real square-root space function lower upper point)
  (forall (epsilon)
    (implies
     (q4378868-r-positive-p real epsilon)
     (q4378868-continuity-radius-exists-p
      real square-root space function lower upper
      point epsilon))))

(defun-sk q4378868-continuous-on-closure-p
    (real square-root space function lower upper)
  (forall (point)
    (implies
     (q4378868-strip-closure-p
      real lower upper point)
     (q4378868-continuous-within-at-p
      real square-root space function lower upper
      point))))

;; Complex differentiability within the open strip. A complex-linear map
;; from C to E is determined by the image of 1, represented by DERIVATIVE.

(defun-sk q4378868-derivative-radius-p
    (real square-root space function lower upper
     point derivative epsilon radius)
  (forall (y)
    (implies
     (and
      (q4378868-open-strip-p
       real lower upper y)
      (q4378868-r-less
       real
       (q4378868-c-norm
        real square-root
        (q4378868-c-subtract real y point))
       radius))
     (q4378868-r-leq
      real
      (q4378868-e-norm
       real space
       (q4378868-e-subtract
        space
        (q4378868-e-subtract
         space
         (q4378868-function-value function y)
         (q4378868-function-value function point))
        (q4378868-e-smul
         space
         (q4378868-c-subtract real y point)
         derivative)))
      (q4378868-r-multiply
       real epsilon
       (q4378868-c-norm
        real square-root
        (q4378868-c-subtract real y point)))))))

(defun-sk q4378868-derivative-radius-exists-p
    (real square-root space function lower upper
     point derivative epsilon)
  (exists (radius)
    (and
     (q4378868-r-positive-p real radius)
     (q4378868-derivative-radius-p
      real square-root space function lower upper
      point derivative epsilon radius))))

(defun-sk q4378868-has-derivative-within-at-p
    (real square-root space function lower upper
     point derivative)
  (forall (epsilon)
    (implies
     (q4378868-r-positive-p real epsilon)
     (q4378868-derivative-radius-exists-p
      real square-root space function lower upper
      point derivative epsilon))))

(defun-sk q4378868-derivative-exists-p
    (real square-root space function lower upper point)
  (exists (derivative)
    (and
     (q4378868-e-member-p space derivative)
     (q4378868-has-derivative-within-at-p
      real square-root space function lower upper
      point derivative))))

(defun-sk q4378868-differentiable-on-open-strip-p
    (real square-root space function lower upper)
  (forall (point)
    (implies
     (q4378868-open-strip-p
      real lower upper point)
     (q4378868-derivative-exists-p
      real square-root space function lower upper
      point))))

(defun q4378868-diff-cont-on-closure-p
    (real square-root space function lower upper)
  (and
   (q4378868-differentiable-on-open-strip-p
    real square-root space function lower upper)
   (q4378868-continuous-on-closure-p
    real square-root space function lower upper)))

;; Real differentiability, used to characterize exp, sin, and cos.

(defun-sk q4378868-real-derivative-radius-p
    (real function point derivative epsilon radius)
  (forall (y)
    (implies
     (and
      (q4378868-r-member-p real y)
      (q4378868-r-less
       real
       (q4378868-r-absolute-value
        real
        (q4378868-r-subtract real y point))
       radius))
     (q4378868-r-leq
      real
      (q4378868-r-absolute-value
       real
       (q4378868-r-subtract
        real
        (q4378868-r-subtract
         real
         (q4378868-r-function-value
          real function y)
         (q4378868-r-function-value
          real function point))
        (q4378868-r-multiply
         real derivative
         (q4378868-r-subtract real y point))))
      (q4378868-r-multiply
       real epsilon
       (q4378868-r-absolute-value
        real
        (q4378868-r-subtract real y point)))))))

(defun-sk q4378868-real-derivative-radius-exists-p
    (real function point derivative epsilon)
  (exists (radius)
    (and
     (q4378868-r-positive-p real radius)
     (q4378868-real-derivative-radius-p
      real function point derivative epsilon radius))))

(defun-sk q4378868-real-has-derivative-at-p
    (real function point derivative)
  (forall (epsilon)
    (implies
     (q4378868-r-positive-p real epsilon)
     (q4378868-real-derivative-radius-exists-p
      real function point derivative epsilon))))

;; The standard exponential is the positive solution of exp' = exp with
;; exp(0) = 1. Sine and cosine satisfy their standard initial-value system.

(defun-sk q4378868-exponential-derivative-laws-p
    (real exponential)
  (forall (x)
    (implies
     (q4378868-r-member-p real x)
     (let ((exp-x
            (q4378868-r-function-value
             real exponential x)))
       (and
        (q4378868-r-positive-p real exp-x)
        (q4378868-real-has-derivative-at-p
         real exponential x exp-x))))))

(defun q4378868-exponential-operation-p
    (real exponential)
  (and
   (q4378868-r-function-typed-p real exponential)
   (equal
    (q4378868-r-function-value
     real exponential (q4378868-r-zero real))
    (q4378868-r-one real))
   (q4378868-exponential-derivative-laws-p
    real exponential)))

(defun-sk q4378868-trigonometric-derivative-laws-p
    (real sine cosine)
  (forall (x)
    (implies
     (q4378868-r-member-p real x)
     (and
      (q4378868-real-has-derivative-at-p
       real sine x
       (q4378868-r-function-value real cosine x))
      (q4378868-real-has-derivative-at-p
       real cosine x
       (q4378868-r-negate
        real
        (q4378868-r-function-value
         real sine x)))))))

(defun q4378868-trigonometric-operations-p
    (real sine cosine)
  (and
   (q4378868-r-function-typed-p real sine)
   (q4378868-r-function-typed-p real cosine)
   (equal
    (q4378868-r-function-value
     real sine (q4378868-r-zero real))
    (q4378868-r-zero real))
   (equal
    (q4378868-r-function-value
     real cosine (q4378868-r-zero real))
    (q4378868-r-one real))
   (q4378868-trigonometric-derivative-laws-p
    real sine cosine)))

(defun-sk q4378868-no-positive-sine-zero-below-p
    (real sine pi-value)
  (forall (x)
    (implies
     (and
      (q4378868-r-member-p real x)
      (q4378868-r-less
       real (q4378868-r-zero real) x)
      (q4378868-r-less real x pi-value))
     (not
      (equal
       (q4378868-r-function-value real sine x)
       (q4378868-r-zero real))))))

(defun q4378868-pi-value-p
    (real sine cosine pi-value)
  (and
   (q4378868-trigonometric-operations-p
    real sine cosine)
   (q4378868-r-positive-p real pi-value)
   (equal
    (q4378868-r-function-value
     real sine pi-value)
    (q4378868-r-zero real))
   (q4378868-no-positive-sine-zero-below-p
    real sine pi-value)))

;; The source big-O filter is
;; comap (abs o re) atTop inf principal(open strip). Its eventual inequality
;; is a cutoff in |Re z| restricted to the open strip. The growth exponent,
;; scale, big-O constant, and cutoff are internal existential witnesses.

(defun-sk q4378868-growth-bound-p
    (real space function exponential lower upper
     growth-rate growth-scale big-o-constant cutoff)
  (forall (w)
    (implies
     (and
      (q4378868-open-strip-p
       real lower upper w)
      (q4378868-r-leq
       real cutoff
       (q4378868-r-absolute-value
        real (car w))))
     (q4378868-r-leq
      real
      (q4378868-e-norm
       real space
       (q4378868-function-value function w))
      (q4378868-r-multiply
       real
       big-o-constant
       (q4378868-r-function-value
        real exponential
        (q4378868-r-multiply
         real
         growth-scale
         (q4378868-r-function-value
          real exponential
          (q4378868-r-multiply
           real
           growth-rate
           (q4378868-r-absolute-value
            real (car w)))))))))))

(defun-sk q4378868-subcritical-growth-p
    (real space function exponential pi-value lower upper)
  (exists
   (growth-rate growth-scale big-o-constant cutoff)
   (and
    (q4378868-r-member-p real growth-rate)
    (q4378868-r-member-p real growth-scale)
    (q4378868-r-positive-p real big-o-constant)
    (q4378868-r-member-p real cutoff)
    (q4378868-r-less
     real
     growth-rate
     (q4378868-r-divide
      real pi-value
      (q4378868-r-subtract real upper lower)))
    (q4378868-growth-bound-p
     real space function exponential lower upper
     growth-rate growth-scale big-o-constant cutoff))))

;; Uniform norm bounds on the two complete boundary lines.

(defun-sk q4378868-boundary-bound-p
    (real space function boundary bound)
  (forall (w)
    (implies
     (and
      (q4378868-complex-p real w)
      (equal (cdr w) boundary))
     (q4378868-r-leq
      real
      (q4378868-e-norm
       real space
       (q4378868-function-value function w))
      bound))))

(defun thousand-theorems-q4378868-phragmen-lindelof-theorem-statement
    (real square-root exponential sine cosine pi-value
     space function lower upper bound z)
  (implies
   (and
    (q4378868-real-field-p real)
    (q4378868-r-square-root-laws-p
     real square-root)
    (q4378868-exponential-operation-p
     real exponential)
    (q4378868-pi-value-p
     real sine cosine pi-value)
    (q4378868-complex-normed-space-p
     real square-root space)
    (q4378868-function-typed-p
     real space function)
    (q4378868-r-member-p real lower)
    (q4378868-r-member-p real upper)
    (q4378868-r-member-p real bound)
    (q4378868-complex-p real z)
    (q4378868-diff-cont-on-closure-p
     real square-root space function lower upper)
    (q4378868-subcritical-growth-p
     real space function exponential pi-value lower upper)
    (q4378868-boundary-bound-p
     real space function lower bound)
    (q4378868-boundary-bound-p
     real space function upper bound)
    (q4378868-closed-strip-p
     real lower upper z))
   (q4378868-r-leq
    real
    (q4378868-e-norm
     real space
     (q4378868-function-value function z))
    bound)))

(value-triple :itpeval-statement-checked)
:q
