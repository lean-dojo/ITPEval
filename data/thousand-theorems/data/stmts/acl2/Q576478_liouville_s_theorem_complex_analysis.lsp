;; Statement-only formalization of thousand-theorems corpus artifact Q576478,
;; "Liouville's theorem (complex analysis)": every bounded, everywhere
;; complex-Frechet-differentiable map between arbitrary complex normed vector
;; spaces takes the same value at every pair of points. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; A Dedekind-complete ordered-field presentation of the real numbers.

(defstub q576478-r-member-p (real value) t)
(defstub q576478-r-zero (real) t)
(defstub q576478-r-one (real) t)
(defstub q576478-r-add (real left right) t)
(defstub q576478-r-multiply (real left right) t)
(defstub q576478-r-negate (real value) t)
(defstub q576478-r-inverse (real value) t)
(defstub q576478-r-less (real left right) t)
(defstub q576478-r-set-member-p (real set value) t)

(defun q576478-r-leq (real left right)
  (not (q576478-r-less real right left)))

(defun q576478-r-positive-p (real value)
  (and
   (q576478-r-member-p real value)
   (q576478-r-less
    real (q576478-r-zero real) value)))

(defun-sk q576478-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q576478-r-member-p real x)
      (q576478-r-member-p real y)
      (q576478-r-member-p real z))
     (let* ((zero (q576478-r-zero real))
            (one (q576478-r-one real))
            (xy-add (q576478-r-add real x y))
            (yz-add (q576478-r-add real y z))
            (xy-mul (q576478-r-multiply real x y))
            (yz-mul (q576478-r-multiply real y z))
            (neg-x (q576478-r-negate real x))
            (inv-x (q576478-r-inverse real x)))
       (and
        (q576478-r-member-p real xy-add)
        (q576478-r-member-p real xy-mul)
        (q576478-r-member-p real neg-x)
        (q576478-r-member-p real inv-x)
        (equal
         (q576478-r-add real xy-add z)
         (q576478-r-add real x yz-add))
        (equal xy-add (q576478-r-add real y x))
        (equal (q576478-r-add real x zero) x)
        (equal (q576478-r-add real x neg-x) zero)
        (equal
         (q576478-r-multiply real xy-mul z)
         (q576478-r-multiply real x yz-mul))
        (equal xy-mul (q576478-r-multiply real y x))
        (equal (q576478-r-multiply real x one) x)
        (equal (q576478-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q576478-r-multiply real x inv-x)
          one))
        (equal
         (q576478-r-multiply
          real x (q576478-r-add real y z))
         (q576478-r-add
          real
          (q576478-r-multiply real x y)
          (q576478-r-multiply real x z))))))))

(defun-sk q576478-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q576478-r-member-p real x)
      (q576478-r-member-p real y)
      (q576478-r-member-p real z))
     (let ((zero (q576478-r-zero real)))
       (and
        (not (q576478-r-less real x x))
        (or
         (equal x y)
         (q576478-r-less real x y)
         (q576478-r-less real y x))
        (implies
         (and
          (q576478-r-less real x y)
          (q576478-r-less real y z))
         (q576478-r-less real x z))
        (implies
         (q576478-r-less real x y)
         (q576478-r-less
          real
          (q576478-r-add real x z)
          (q576478-r-add real y z)))
        (implies
         (and
          (q576478-r-less real zero x)
          (q576478-r-less real zero y))
         (q576478-r-less
          real zero
          (q576478-r-multiply real x y))))))))

(defun-sk q576478-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q576478-r-member-p real x)
     (q576478-r-set-member-p real set x))))

(defun-sk q576478-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q576478-r-member-p real x)
      (q576478-r-set-member-p real set x))
     (q576478-r-leq real x bound))))

(defun-sk q576478-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q576478-r-member-p real bound)
     (q576478-r-upper-bound-p real set bound))))

(defun-sk q576478-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q576478-r-member-p real supremum)
     (q576478-r-upper-bound-p real set supremum)
     (implies
      (and
       (q576478-r-member-p real bound)
       (q576478-r-upper-bound-p real set bound))
      (q576478-r-leq real supremum bound)))))

(defun-sk q576478-r-has-supremum-p (real set)
  (exists (supremum)
    (q576478-r-supremum-p real set supremum)))

(defun-sk q576478-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q576478-r-set-nonempty-p real set)
      (q576478-r-bounded-above-p real set))
     (q576478-r-has-supremum-p real set))))

(defun q576478-real-field-p (real)
  (let ((zero (q576478-r-zero real))
        (one (q576478-r-one real)))
    (and
     (q576478-r-member-p real zero)
     (q576478-r-member-p real one)
     (not (equal zero one))
     (q576478-r-field-laws-p real)
     (q576478-r-order-laws-p real)
     (q576478-r-less real zero one)
     (q576478-r-dedekind-complete-p real))))

;; The nonnegative square root and the usual complex field represented by
;; real/imaginary coordinate pairs.

(defstub q576478-r-square-root (real square-root value) t)

(defun-sk q576478-r-square-root-laws-p
    (real square-root)
  (forall (x)
    (implies
     (and
      (q576478-r-member-p real x)
      (q576478-r-leq
       real (q576478-r-zero real) x))
     (let ((root
            (q576478-r-square-root
             real square-root x)))
       (and
        (q576478-r-member-p real root)
        (q576478-r-leq
         real (q576478-r-zero real) root)
        (equal
         (q576478-r-multiply real root root)
         x))))))

(defun q576478-complex-p (real value)
  (and
   (consp value)
   (q576478-r-member-p real (car value))
   (q576478-r-member-p real (cdr value))))

(defun q576478-c-zero (real)
  (cons
   (q576478-r-zero real)
   (q576478-r-zero real)))

(defun q576478-c-one (real)
  (cons
   (q576478-r-one real)
   (q576478-r-zero real)))

(defun q576478-c-add (real left right)
  (cons
   (q576478-r-add real (car left) (car right))
   (q576478-r-add real (cdr left) (cdr right))))

(defun q576478-c-negate (real value)
  (cons
   (q576478-r-negate real (car value))
   (q576478-r-negate real (cdr value))))

(defun q576478-c-multiply (real left right)
  (cons
   (q576478-r-add
    real
    (q576478-r-multiply
     real (car left) (car right))
    (q576478-r-negate
     real
     (q576478-r-multiply
      real (cdr left) (cdr right))))
   (q576478-r-add
    real
    (q576478-r-multiply
     real (car left) (cdr right))
    (q576478-r-multiply
     real (cdr left) (car right)))))

(defun q576478-c-norm-square (real value)
  (q576478-r-add
   real
   (q576478-r-multiply
    real (car value) (car value))
   (q576478-r-multiply
    real (cdr value) (cdr value))))

(defun q576478-c-norm (real square-root value)
  (q576478-r-square-root
   real square-root
   (q576478-c-norm-square real value)))

;; Arbitrary normed vector spaces over the represented complex field. The
;; SPACE argument distinguishes the source and codomain carriers.

(defstub q576478-v-member-p (space value) t)
(defstub q576478-v-zero (space) t)
(defstub q576478-v-add (space left right) t)
(defstub q576478-v-negate (space value) t)
(defstub q576478-v-smul (space scalar vector) t)
(defstub q576478-v-norm (real space value) t)

(defun q576478-v-subtract (space left right)
  (q576478-v-add
   space left (q576478-v-negate space right)))

(defun-sk q576478-v-additive-module-laws-p
    (real space)
  (forall (a b x y z)
    (implies
     (and
      (q576478-complex-p real a)
      (q576478-complex-p real b)
      (q576478-v-member-p space x)
      (q576478-v-member-p space y)
      (q576478-v-member-p space z))
     (let* ((zero (q576478-v-zero space))
            (xy (q576478-v-add space x y))
            (yz (q576478-v-add space y z))
            (neg-x (q576478-v-negate space x))
            (a-x (q576478-v-smul space a x)))
       (and
        (q576478-v-member-p space xy)
        (q576478-v-member-p space neg-x)
        (q576478-v-member-p space a-x)
        (equal
         (q576478-v-add space xy z)
         (q576478-v-add space x yz))
        (equal xy (q576478-v-add space y x))
        (equal (q576478-v-add space x zero) x)
        (equal (q576478-v-add space x neg-x) zero)
        (equal
         (q576478-v-smul
          space (q576478-c-one real) x)
         x)
        (equal
         (q576478-v-smul
          space
          (q576478-c-multiply real a b)
          x)
         (q576478-v-smul
          space a
          (q576478-v-smul space b x)))
        (equal
         (q576478-v-smul
          space (q576478-c-add real a b) x)
         (q576478-v-add
          space
          (q576478-v-smul space a x)
          (q576478-v-smul space b x)))
        (equal
         (q576478-v-smul space a xy)
         (q576478-v-add
          space
          (q576478-v-smul space a x)
          (q576478-v-smul space a y)))
        (equal
         (q576478-v-smul
          space (q576478-c-zero real) x)
         zero)
        (equal
         (q576478-v-smul space a zero)
         zero))))))

(defun-sk q576478-v-norm-laws-p
    (real square-root space)
  (forall (a x y)
    (implies
     (and
      (q576478-complex-p real a)
      (q576478-v-member-p space x)
      (q576478-v-member-p space y))
     (let* ((zero-r (q576478-r-zero real))
            (zero-v (q576478-v-zero space))
            (norm-x (q576478-v-norm real space x))
            (norm-y (q576478-v-norm real space y)))
       (and
        (q576478-r-member-p real norm-x)
        (q576478-r-member-p real norm-y)
        (q576478-r-leq real zero-r norm-x)
        (iff (equal norm-x zero-r)
             (equal x zero-v))
        (equal
         (q576478-v-norm
          real space (q576478-v-negate space x))
         norm-x)
        (equal
         (q576478-v-norm
          real space
          (q576478-v-smul space a x))
         (q576478-r-multiply
          real
          (q576478-c-norm real square-root a)
          norm-x))
        (q576478-r-leq
         real
         (q576478-v-norm
          real space (q576478-v-add space x y))
         (q576478-r-add real norm-x norm-y)))))))

(defun q576478-complex-normed-space-p
    (real square-root space)
  (and
   (q576478-v-member-p
    space (q576478-v-zero space))
   (q576478-v-additive-module-laws-p real space)
   (q576478-v-norm-laws-p
    real square-root space)))

;; An arbitrary function from the source space to the codomain space.

(defstub q576478-function-value (function argument) t)

(defun-sk q576478-function-typed-p
    (domain codomain function)
  (forall (x)
    (implies
     (q576478-v-member-p domain x)
     (q576478-v-member-p
      codomain
      (q576478-function-value function x)))))

;; Continuous complex-linear maps from the source space to the codomain.

(defstub q576478-linear-value (linear-map argument) t)

(defun-sk q576478-linear-laws-p
    (real domain codomain linear-map)
  (forall (a x y)
    (implies
     (and
      (q576478-complex-p real a)
      (q576478-v-member-p domain x)
      (q576478-v-member-p domain y))
     (and
      (q576478-v-member-p
       codomain
       (q576478-linear-value linear-map x))
      (equal
       (q576478-linear-value
        linear-map
        (q576478-v-add domain x y))
       (q576478-v-add
        codomain
        (q576478-linear-value linear-map x)
        (q576478-linear-value linear-map y)))
      (equal
       (q576478-linear-value
        linear-map
        (q576478-v-smul domain a x))
       (q576478-v-smul
        codomain a
        (q576478-linear-value linear-map x)))))))

(defun-sk q576478-linear-bound-p
    (real domain codomain linear-map bound)
  (forall (x)
    (implies
     (q576478-v-member-p domain x)
     (q576478-r-leq
      real
      (q576478-v-norm
       real codomain
       (q576478-linear-value linear-map x))
      (q576478-r-multiply
       real bound
       (q576478-v-norm real domain x))))))

(defun-sk q576478-linear-bound-exists-p
    (real domain codomain linear-map)
  (exists (bound)
    (and
     (q576478-r-member-p real bound)
     (q576478-r-leq
      real (q576478-r-zero real) bound)
     (q576478-linear-bound-p
      real domain codomain linear-map bound))))

(defun q576478-continuous-linear-map-p
    (real domain codomain linear-map)
  (and
   (q576478-linear-laws-p
    real domain codomain linear-map)
   (q576478-linear-bound-exists-p
    real domain codomain linear-map)))

;; Frechet differentiability over C, using its equivalent epsilon-delta
;; remainder estimate.

(defun-sk q576478-derivative-nearby-p
    (real domain codomain function center linear-map epsilon radius)
  (forall (y)
    (implies
     (and
      (q576478-v-member-p domain y)
      (q576478-r-less
       real
       (q576478-v-norm
        real domain
        (q576478-v-subtract domain y center))
       radius))
     (q576478-r-leq
      real
      (q576478-v-norm
       real codomain
       (q576478-v-subtract
        codomain
        (q576478-v-subtract
         codomain
         (q576478-function-value function y)
         (q576478-function-value function center))
        (q576478-linear-value
         linear-map
         (q576478-v-subtract domain y center))))
      (q576478-r-multiply
       real epsilon
       (q576478-v-norm
        real domain
        (q576478-v-subtract domain y center)))))))

(defun-sk q576478-derivative-radius-exists-p
    (real domain codomain function center linear-map epsilon)
  (exists (radius)
    (and
     (q576478-r-positive-p real radius)
     (q576478-derivative-nearby-p
      real domain codomain function center
      linear-map epsilon radius))))

(defun-sk q576478-has-derivative-at-p
    (real domain codomain function center linear-map)
  (forall (epsilon)
    (implies
     (q576478-r-positive-p real epsilon)
     (q576478-derivative-radius-exists-p
      real domain codomain function center
      linear-map epsilon))))

(defun-sk q576478-differentiable-at-p
    (real domain codomain function center)
  (exists (linear-map)
    (and
     (q576478-continuous-linear-map-p
      real domain codomain linear-map)
     (q576478-has-derivative-at-p
      real domain codomain function center linear-map))))

(defun-sk q576478-differentiable-everywhere-p
    (real domain codomain function)
  (forall (center)
    (implies
     (q576478-v-member-p domain center)
     (q576478-differentiable-at-p
      real domain codomain function center))))

;; Boundedness of the function range in the codomain norm.

(defun-sk q576478-range-bounded-by-p
    (real domain codomain function bound)
  (forall (x)
    (implies
     (q576478-v-member-p domain x)
     (q576478-r-leq
      real
      (q576478-v-norm
       real codomain
       (q576478-function-value function x))
      bound))))

(defun-sk q576478-bounded-range-p
    (real domain codomain function)
  (exists (bound)
    (and
     (q576478-r-member-p real bound)
     (q576478-r-leq
      real (q576478-r-zero real) bound)
     (q576478-range-bounded-by-p
      real domain codomain function bound))))

(defun-sk
    thousand-theorems-q576478-liouville-theorem-complex-analysis-statement
    ()
  (forall
    (real square-root domain codomain function z w)
    (implies
     (and
      (q576478-real-field-p real)
      (q576478-r-square-root-laws-p
       real square-root)
      (q576478-complex-normed-space-p
       real square-root domain)
      (q576478-complex-normed-space-p
       real square-root codomain)
      (q576478-function-typed-p
       domain codomain function)
      (q576478-v-member-p domain z)
      (q576478-v-member-p domain w)
      (q576478-differentiable-everywhere-p
       real domain codomain function)
      (q576478-bounded-range-p
       real domain codomain function))
     (equal
      (q576478-function-value function z)
      (q576478-function-value function w)))))

(value-triple :itpeval-statement-checked)
:q
