;; Statement-only formalization of thousand-theorems corpus artifact Q3527250,
;; "Hadamard three-lines theorem": a bounded complex-differentiable function
;; into an arbitrary complex normed space is bounded inside a vertical strip
;; by the geometric interpolation of its boundary-line suprema.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Conservative interfaces present arbitrary real and normed-space carriers,
;; operations, functions, and subsets.  The assumptions below explicitly
;; present a Dedekind-complete ordered field, hence the real numbers; complex
;; numbers are real-coordinate pairs.  Continuity and complex
;; differentiability are expanded by epsilon-delta definitions.
;; Real subsets are first-order set objects with an arbitrary generic
;; membership interface and interpreted comprehension constructors.  In
;; particular, each boundary norm image below has membership definitionally
;; equal to its existential image condition.  The real supremum operation is
;; constrained by completeness to return its uniquely characterized least
;; upper bound.
;;
;; For positive real a and complex w, ‖a^w‖ = exp(Re(w) log(a)).  The final
;; bound uses this identity in both factors.  This is definitionally
;; equivalent to the norm of INTERPSTRIP' in the source, while its explicit
;; zero-boundary branch is preserved.

;; A Dedekind-complete ordered-field presentation of the real numbers.

(defstub q3527250-r-member-p (real value) t)
(defstub q3527250-r-zero (real) t)
(defstub q3527250-r-one (real) t)
(defstub q3527250-r-add (real left right) t)
(defstub q3527250-r-multiply (real left right) t)
(defstub q3527250-r-negate (real value) t)
(defstub q3527250-r-inverse (real value) t)
(defstub q3527250-r-less (real left right) t)
(defstub q3527250-r-generic-set-member-p (real set value) t)
(defstub q3527250-r-supremum (real set) t)
(defstub q3527250-r-square-root (real value) t)
(defstub q3527250-r-exponential (real value) t)
(defstub q3527250-r-logarithm (real value) t)

(defun q3527250-r-subtract (real left right)
  (q3527250-r-add
   real left (q3527250-r-negate real right)))

(defun q3527250-r-divide (real numerator denominator)
  (q3527250-r-multiply
   real numerator (q3527250-r-inverse real denominator)))

(defun q3527250-r-leq (real left right)
  (not (q3527250-r-less real right left)))

(defun q3527250-r-absolute-value (real value)
  (if (q3527250-r-less
       real value (q3527250-r-zero real))
      (q3527250-r-negate real value)
    value))

(defun q3527250-r-positive-p (real value)
  (and
   (q3527250-r-member-p real value)
   (q3527250-r-less
    real (q3527250-r-zero real) value)))

(defun-sk q3527250-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q3527250-r-member-p real x)
      (q3527250-r-member-p real y)
      (q3527250-r-member-p real z))
     (let* ((zero (q3527250-r-zero real))
            (one (q3527250-r-one real))
            (xy-add (q3527250-r-add real x y))
            (yz-add (q3527250-r-add real y z))
            (xy-mul (q3527250-r-multiply real x y))
            (yz-mul (q3527250-r-multiply real y z))
            (neg-x (q3527250-r-negate real x))
            (inv-x (q3527250-r-inverse real x)))
       (and
        (q3527250-r-member-p real zero)
        (q3527250-r-member-p real one)
        (q3527250-r-member-p real xy-add)
        (q3527250-r-member-p real xy-mul)
        (q3527250-r-member-p real neg-x)
        (q3527250-r-member-p real inv-x)
        (equal
         (q3527250-r-add real xy-add z)
         (q3527250-r-add real x yz-add))
        (equal xy-add (q3527250-r-add real y x))
        (equal (q3527250-r-add real x zero) x)
        (equal (q3527250-r-add real x neg-x) zero)
        (equal
         (q3527250-r-multiply real xy-mul z)
         (q3527250-r-multiply real x yz-mul))
        (equal xy-mul (q3527250-r-multiply real y x))
        (equal (q3527250-r-multiply real x one) x)
        (equal (q3527250-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q3527250-r-multiply real x inv-x)
          one))
        (equal
         (q3527250-r-multiply
          real x (q3527250-r-add real y z))
         (q3527250-r-add
          real
          (q3527250-r-multiply real x y)
          (q3527250-r-multiply real x z))))))))

(defun-sk q3527250-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q3527250-r-member-p real x)
      (q3527250-r-member-p real y)
      (q3527250-r-member-p real z))
     (let ((zero (q3527250-r-zero real)))
       (and
        (not (q3527250-r-less real x x))
        (or
         (equal x y)
         (q3527250-r-less real x y)
         (q3527250-r-less real y x))
        (implies
         (and
          (q3527250-r-less real x y)
          (q3527250-r-less real y z))
         (q3527250-r-less real x z))
        (implies
         (q3527250-r-less real x y)
         (q3527250-r-less
          real
          (q3527250-r-add real x z)
          (q3527250-r-add real y z)))
        (implies
         (and
          (q3527250-r-less real zero x)
          (q3527250-r-less real zero y))
         (q3527250-r-less
          real zero
          (q3527250-r-multiply real x y))))))))

;; Square root and the standard real exponential and logarithm.

(defun-sk q3527250-square-root-laws-p (real)
  (forall (x)
    (implies
     (q3527250-r-member-p real x)
     (let ((root (q3527250-r-square-root real x))
           (zero (q3527250-r-zero real)))
       (and
        (q3527250-r-member-p real root)
        (implies
         (q3527250-r-less real x zero)
         (equal root zero))
        (implies
         (not (q3527250-r-less real x zero))
         (and
          (q3527250-r-leq real zero root)
          (equal
           (q3527250-r-multiply real root root)
           x))))))))

(defun-sk q3527250-real-derivative-nearby-p
    (real function point derivative epsilon radius)
  (forall (y)
    (implies
     (and
      (q3527250-r-member-p real y)
      (q3527250-r-less
       real
       (q3527250-r-absolute-value
        real
        (q3527250-r-subtract real y point))
       radius))
     (q3527250-r-leq
      real
      (q3527250-r-absolute-value
       real
       (q3527250-r-subtract
        real
        (q3527250-r-subtract
         real
         (q3527250-r-exponential real y)
         (q3527250-r-exponential real point))
        (q3527250-r-multiply
         real derivative
         (q3527250-r-subtract real y point))))
      (q3527250-r-multiply
       real epsilon
       (q3527250-r-absolute-value
        real
        (q3527250-r-subtract real y point)))))))

(defun-sk q3527250-real-derivative-radius-exists-p
    (real function point derivative epsilon)
  (exists (radius)
    (and
     (q3527250-r-positive-p real radius)
     (q3527250-real-derivative-nearby-p
      real function point derivative epsilon radius))))

(defun-sk q3527250-real-has-derivative-at-p
    (real function point derivative)
  (forall (epsilon)
    (implies
     (q3527250-r-positive-p real epsilon)
     (q3527250-real-derivative-radius-exists-p
      real function point derivative epsilon))))

(defun-sk q3527250-exponential-laws-p (real)
  (forall (x)
    (implies
     (q3527250-r-member-p real x)
     (and
      (q3527250-r-positive-p
       real (q3527250-r-exponential real x))
      (q3527250-real-has-derivative-at-p
       real
       'q3527250-r-exponential
       x
       (q3527250-r-exponential real x))))))

(defun q3527250-exponential-operation-p (real)
  (and
   (equal
    (q3527250-r-exponential
     real (q3527250-r-zero real))
    (q3527250-r-one real))
   (q3527250-exponential-laws-p real)))

(defun-sk q3527250-logarithm-laws-p (real)
  (forall (x)
    (and
     (implies
      (q3527250-r-member-p real x)
      (equal
       (q3527250-r-logarithm
        real (q3527250-r-exponential real x))
       x))
     (implies
      (q3527250-r-positive-p real x)
      (and
       (q3527250-r-member-p
        real (q3527250-r-logarithm real x))
       (equal
        (q3527250-r-exponential
         real (q3527250-r-logarithm real x))
        x))))))

;; Complex numbers are pairs (real-part . imaginary-part).

(defun q3527250-complex-p (real value)
  (and
   (consp value)
   (q3527250-r-member-p real (car value))
   (q3527250-r-member-p real (cdr value))))

(defun q3527250-c-zero (real)
  (cons
   (q3527250-r-zero real)
   (q3527250-r-zero real)))

(defun q3527250-c-one (real)
  (cons
   (q3527250-r-one real)
   (q3527250-r-zero real)))

(defun q3527250-c-of-real (real value)
  (cons value (q3527250-r-zero real)))

(defun q3527250-c-add (real left right)
  (cons
   (q3527250-r-add real (car left) (car right))
   (q3527250-r-add real (cdr left) (cdr right))))

(defun q3527250-c-negate (real value)
  (cons
   (q3527250-r-negate real (car value))
   (q3527250-r-negate real (cdr value))))

(defun q3527250-c-subtract (real left right)
  (q3527250-c-add
   real left (q3527250-c-negate real right)))

(defun q3527250-c-multiply (real left right)
  (cons
   (q3527250-r-subtract
    real
    (q3527250-r-multiply real (car left) (car right))
    (q3527250-r-multiply real (cdr left) (cdr right)))
   (q3527250-r-add
    real
    (q3527250-r-multiply real (car left) (cdr right))
    (q3527250-r-multiply real (cdr left) (car right)))))

(defun q3527250-c-norm (real value)
  (q3527250-r-square-root
   real
   (q3527250-r-add
    real
    (q3527250-r-multiply real (car value) (car value))
    (q3527250-r-multiply real (cdr value) (cdr value)))))

;; An arbitrary normed vector space over the represented complex numbers.

(defstub q3527250-e-member-p (space value) t)
(defstub q3527250-e-zero (space) t)
(defstub q3527250-e-add (space left right) t)
(defstub q3527250-e-negate (space value) t)
(defstub q3527250-e-smul (real space scalar vector) t)
(defstub q3527250-e-norm (real space value) t)

(defun q3527250-e-subtract (space left right)
  (q3527250-e-add
   space left (q3527250-e-negate space right)))

(defun-sk q3527250-normed-space-laws-p
    (real space)
  (forall (x y z a b)
    (and
     (implies
      (and
       (q3527250-e-member-p space x)
       (q3527250-e-member-p space y)
       (q3527250-e-member-p space z))
      (let* ((zero-e (q3527250-e-zero space))
             (zero-r (q3527250-r-zero real))
             (xy-add (q3527250-e-add space x y))
             (yz-add (q3527250-e-add space y z))
             (neg-x (q3527250-e-negate space x))
             (norm-x (q3527250-e-norm real space x))
             (norm-y (q3527250-e-norm real space y)))
        (and
         (q3527250-e-member-p space xy-add)
         (q3527250-e-member-p space neg-x)
         (q3527250-r-member-p real norm-x)
         (q3527250-r-member-p real norm-y)
         (equal
          (q3527250-e-add space xy-add z)
          (q3527250-e-add space x yz-add))
         (equal xy-add (q3527250-e-add space y x))
         (equal (q3527250-e-add space x zero-e) x)
         (equal (q3527250-e-add space x neg-x) zero-e)
         (q3527250-r-leq real zero-r norm-x)
         (iff (equal norm-x zero-r)
              (equal x zero-e))
         (equal
          (q3527250-e-norm real space neg-x)
          norm-x)
         (q3527250-r-leq
          real
          (q3527250-e-norm real space xy-add)
          (q3527250-r-add real norm-x norm-y)))))
     (implies
      (and
       (q3527250-complex-p real a)
       (q3527250-complex-p real b)
       (q3527250-e-member-p space x)
       (q3527250-e-member-p space y))
      (let ((zero-c (q3527250-c-zero real))
            (one-c (q3527250-c-one real))
            (zero-e (q3527250-e-zero space)))
        (and
         (q3527250-e-member-p
          space (q3527250-e-smul real space a x))
         (equal
          (q3527250-e-smul real space one-c x)
          x)
         (equal
          (q3527250-e-smul
           real space
           (q3527250-c-multiply real a b) x)
          (q3527250-e-smul
           real space a
           (q3527250-e-smul real space b x)))
         (equal
          (q3527250-e-smul
           real space
           (q3527250-c-add real a b) x)
          (q3527250-e-add
           space
           (q3527250-e-smul real space a x)
           (q3527250-e-smul real space b x)))
         (equal
          (q3527250-e-smul
           real space a
           (q3527250-e-add space x y))
          (q3527250-e-add
           space
           (q3527250-e-smul real space a x)
           (q3527250-e-smul real space a y)))
         (equal
          (q3527250-e-smul real space zero-c x)
          zero-e)
         (equal
          (q3527250-e-smul real space a zero-e)
          zero-e)
         (equal
          (q3527250-e-norm
           real space
           (q3527250-e-smul real space a x))
          (q3527250-r-multiply
           real
           (q3527250-c-norm real a)
           (q3527250-e-norm real space x)))))))))

(defun q3527250-normed-complex-space-p
    (real space)
  (and
   (q3527250-e-member-p
    space (q3527250-e-zero space))
   (q3527250-normed-space-laws-p real space)))

;; Arbitrary functions C -> E and the two vertical strips.

(defstub q3527250-function-value (function argument) t)

(defun-sk q3527250-function-typed-p
    (real space function)
  (forall (z)
    (implies
     (q3527250-complex-p real z)
     (q3527250-e-member-p
      space (q3527250-function-value function z)))))

(defun q3527250-open-strip-p
    (real lower upper z)
  (and
   (q3527250-complex-p real z)
   (q3527250-r-less real lower (car z))
   (q3527250-r-less real (car z) upper)))

(defun q3527250-closed-strip-p
    (real lower upper z)
  (and
   (q3527250-complex-p real z)
   (q3527250-r-leq real lower (car z))
   (q3527250-r-leq real (car z) upper)))

;; Boundedness of ‖f‖ on the full closed strip.

(defun-sk q3527250-closed-strip-bound-p
    (real space function lower upper bound)
  (forall (w)
    (implies
     (q3527250-closed-strip-p real lower upper w)
     (q3527250-r-leq
      real
      (q3527250-e-norm
       real space (q3527250-function-value function w))
      bound))))

(defun-sk q3527250-bounded-on-closed-strip-p
    (real space function lower upper)
  (exists (bound)
    (and
     (q3527250-r-member-p real bound)
     (q3527250-closed-strip-bound-p
      real space function lower upper bound))))

;; Continuity on the closed strip.

(defun-sk q3527250-continuity-nearby-p
    (real space function lower upper point epsilon radius)
  (forall (w)
    (implies
     (and
      (q3527250-closed-strip-p real lower upper w)
      (q3527250-r-less
       real
       (q3527250-c-norm
        real (q3527250-c-subtract real w point))
       radius))
     (q3527250-r-less
      real
      (q3527250-e-norm
       real space
       (q3527250-e-subtract
        space
        (q3527250-function-value function w)
        (q3527250-function-value function point)))
      epsilon))))

(defun-sk q3527250-continuity-radius-exists-p
    (real space function lower upper point epsilon)
  (exists (radius)
    (and
     (q3527250-r-positive-p real radius)
     (q3527250-continuity-nearby-p
      real space function lower upper point epsilon radius))))

(defun-sk q3527250-continuous-within-closed-at-p
    (real space function lower upper point)
  (forall (epsilon)
    (implies
     (q3527250-r-positive-p real epsilon)
     (q3527250-continuity-radius-exists-p
      real space function lower upper point epsilon))))

(defun-sk q3527250-continuous-on-closed-strip-p
    (real space function lower upper)
  (forall (point)
    (implies
     (q3527250-closed-strip-p
      real lower upper point)
     (q3527250-continuous-within-closed-at-p
      real space function lower upper point))))

;; Complex differentiability within the open strip.  A complex-linear map
;; C -> E is represented by its value at 1, so its value at h is h • derivative.

(defun-sk q3527250-derivative-nearby-p
    (real space function lower upper point derivative epsilon radius)
  (forall (w)
    (implies
     (and
      (q3527250-open-strip-p real lower upper w)
      (q3527250-r-less
       real
       (q3527250-c-norm
        real (q3527250-c-subtract real w point))
       radius))
     (q3527250-r-leq
      real
      (q3527250-e-norm
       real space
       (q3527250-e-subtract
        space
        (q3527250-e-subtract
         space
         (q3527250-function-value function w)
         (q3527250-function-value function point))
        (q3527250-e-smul
         real space
         (q3527250-c-subtract real w point)
         derivative)))
      (q3527250-r-multiply
       real epsilon
       (q3527250-c-norm
        real (q3527250-c-subtract real w point)))))))

(defun-sk q3527250-derivative-radius-exists-p
    (real space function lower upper point derivative epsilon)
  (exists (radius)
    (and
     (q3527250-r-positive-p real radius)
     (q3527250-derivative-nearby-p
      real space function lower upper point derivative epsilon radius))))

(defun-sk q3527250-has-complex-derivative-within-p
    (real space function lower upper point derivative)
  (forall (epsilon)
    (implies
     (q3527250-r-positive-p real epsilon)
     (q3527250-derivative-radius-exists-p
      real space function lower upper point derivative epsilon))))

(defun-sk q3527250-differentiable-within-open-at-p
    (real space function lower upper point)
  (exists (derivative)
    (and
     (q3527250-e-member-p space derivative)
     (q3527250-has-complex-derivative-within-p
      real space function lower upper point derivative))))

(defun-sk q3527250-differentiable-on-open-strip-p
    (real space function lower upper)
  (forall (point)
    (implies
     (q3527250-open-strip-p real lower upper point)
     (q3527250-differentiable-within-open-at-p
      real space function lower upper point))))

(defun q3527250-diff-cont-on-closed-p
    (real space function lower upper)
  (and
   (q3527250-differentiable-on-open-strip-p
    real space function lower upper)
   (q3527250-continuous-on-closed-strip-p
    real space function lower upper)))

;; The set {‖f(w)‖ : Re(w) = boundary} is represented by an interpreted
;; first-order constructor.  Its membership is exactly the following
;; existential image condition.

(defun-sk q3527250-line-norm-image-member-p
    (real space function boundary value)
  (exists (w)
    (and
     (q3527250-r-member-p real value)
     (q3527250-complex-p real w)
     (equal (car w) boundary)
     (equal
      (q3527250-e-norm
       real space (q3527250-function-value function w))
      value))))

(defun q3527250-line-norm-image-set
    (real space function boundary)
  (list
   :q3527250-line-norm-image
   real space function boundary))

(defun q3527250-r-singleton-set (real value)
  (list :q3527250-r-singleton real value))

(defun q3527250-r-set-member-p (real set value)
  (and
   (q3527250-r-member-p real value)
   (cond
    ((and
      (consp set)
      (equal (car set) :q3527250-line-norm-image))
     (and
      (true-listp set)
      (equal (len set) 5)
      (equal real (cadr set))
      (q3527250-line-norm-image-member-p
       real
       (caddr set)
       (cadddr set)
       (car (cddddr set))
       value)))
    ((and
      (consp set)
      (equal (car set) :q3527250-r-singleton))
     (and
      (true-listp set)
      (equal (len set) 3)
      (equal real (cadr set))
      (equal value (caddr set))))
    (t
     (q3527250-r-generic-set-member-p
      real set value)))))

(defun-sk q3527250-r-set-contained-in-reals-p (real set)
  (forall (x)
    (implies
     (q3527250-r-set-member-p real set x)
     (q3527250-r-member-p real x))))

(defun q3527250-r-valid-set-p (real set)
  (q3527250-r-set-contained-in-reals-p real set))

(defun-sk q3527250-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q3527250-r-member-p real x)
     (q3527250-r-set-member-p real set x))))

(defun-sk q3527250-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q3527250-r-member-p real x)
      (q3527250-r-set-member-p real set x))
     (q3527250-r-leq real x bound))))

(defun-sk q3527250-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q3527250-r-member-p real bound)
     (q3527250-r-upper-bound-p real set bound))))

(defun-sk q3527250-r-supremum-p
    (real set supremum)
  (forall (bound)
    (and
     (q3527250-r-member-p real supremum)
     (q3527250-r-upper-bound-p real set supremum)
     (implies
      (and
       (q3527250-r-member-p real bound)
       (q3527250-r-upper-bound-p real set bound))
      (q3527250-r-leq real supremum bound)))))

(defun-sk q3527250-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q3527250-r-valid-set-p real set)
      (q3527250-r-set-nonempty-p real set)
      (q3527250-r-bounded-above-p real set))
     (q3527250-r-supremum-p
      real set (q3527250-r-supremum real set)))))

(defun q3527250-real-field-p (real)
  (let ((zero (q3527250-r-zero real))
        (one (q3527250-r-one real)))
    (and
     (q3527250-r-member-p real zero)
     (q3527250-r-member-p real one)
     (not (equal zero one))
     (q3527250-r-field-laws-p real)
     (q3527250-r-order-laws-p real)
     (q3527250-r-less real zero one)
     ;; The interpreted singleton gives the represented-set universe an
     ;; unconditional nonempty member, so completeness cannot be vacuous
     ;; merely because the generic membership interface is empty.
     (q3527250-r-set-nonempty-p
      real (q3527250-r-singleton-set real zero))
     (q3527250-r-dedekind-complete-p real))))

(defun q3527250-line-supremum
    (real space function boundary)
  (q3527250-r-supremum
   real
   (q3527250-line-norm-image-set
    real space function boundary)))

;; The norm of the source interpolation.  In the nonzero branch the two
;; least upper bounds are positive, so complex power reduces exactly to
;; exp(real-exponent * log(base)) after taking norms.

(defun q3527250-interpolation-bound
    (real left-supremum right-supremum parameter)
  (if
      (or
       (equal left-supremum (q3527250-r-zero real))
       (equal right-supremum (q3527250-r-zero real)))
      (q3527250-r-zero real)
    (q3527250-r-multiply
     real
     (q3527250-r-exponential
      real
      (q3527250-r-multiply
       real
       (q3527250-r-subtract
        real (q3527250-r-one real) parameter)
       (q3527250-r-logarithm real left-supremum)))
     (q3527250-r-exponential
      real
      (q3527250-r-multiply
       real
       parameter
       (q3527250-r-logarithm real right-supremum))))))

(defun q3527250-hadamard-conclusion-p
    (real space function lower upper z)
  (let ((left-supremum
         (q3527250-line-supremum
          real space function lower))
        (right-supremum
         (q3527250-line-supremum
          real space function upper))
        (parameter
         (q3527250-r-divide
          real
          (q3527250-r-subtract real (car z) lower)
          (q3527250-r-subtract real upper lower))))
    (q3527250-r-leq
     real
     (q3527250-e-norm
      real space (q3527250-function-value function z))
     (q3527250-interpolation-bound
      real left-supremum right-supremum parameter))))

(defun-sk
    thousand-theorems-q3527250-hadamard-three-lines-theorem-statement
    ()
  (forall (real space function lower upper z)
    (implies
     (and
      (q3527250-real-field-p real)
      (q3527250-square-root-laws-p real)
      (q3527250-exponential-operation-p real)
      (q3527250-logarithm-laws-p real)
      (q3527250-normed-complex-space-p real space)
      (q3527250-function-typed-p real space function)
      (q3527250-r-member-p real lower)
      (q3527250-r-member-p real upper)
      (q3527250-r-less real lower upper)
      (q3527250-complex-p real z)
      (q3527250-closed-strip-p real lower upper z)
      (q3527250-diff-cont-on-closed-p
       real space function lower upper)
      (q3527250-bounded-on-closed-strip-p
       real space function lower upper))
     (q3527250-hadamard-conclusion-p
      real space function lower upper z))))

(value-triple :itpeval-statement-checked)
:q
