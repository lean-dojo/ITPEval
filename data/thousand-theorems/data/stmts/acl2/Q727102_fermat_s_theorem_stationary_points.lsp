;; Statement-only formalization of thousand-theorems corpus artifact Q727102,
;; "Fermat's theorem (stationary points)": the totalized Frechet derivative
;; on a real normed space, and the totalized scalar derivative on the real
;; line, vanish at a local extremum. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces represent the real field, arbitrary real normed
;; spaces, functions, and continuous linear maps. The explicit laws below
;; present the real numbers as a Dedekind-complete ordered field. Local extrema
;; and derivatives are expanded by equivalent metric epsilon-delta conditions.

(defstub q727102-real-p (real value) t)
(defstub q727102-real-set-member-p (real set value) t)
(defstub q727102-r-zero (real) t)
(defstub q727102-r-one (real) t)
(defstub q727102-r-add (real left right) t)
(defstub q727102-r-mul (real left right) t)
(defstub q727102-r-neg (real value) t)
(defstub q727102-r-inv (real value) t)
(defstub q727102-r-lt (real left right) t)

(defstub q727102-vector-p (space value) t)
(defstub q727102-v-zero (space) t)
(defstub q727102-v-add (space left right) t)
(defstub q727102-v-neg (space value) t)
(defstub q727102-v-smul (real space scalar vector) t)
(defstub q727102-v-norm (real space vector) t)

(defstub q727102-function-value (function argument) t)
(defstub q727102-linear-value (linear-map argument) t)

(defun q727102-r-sub (real left right)
  (q727102-r-add real left (q727102-r-neg real right)))

(defun q727102-r-le (real left right)
  (not (q727102-r-lt real right left)))

(defun q727102-r-abs (real value)
  (if (q727102-r-lt real value (q727102-r-zero real))
      (q727102-r-neg real value)
    value))

(defun q727102-positive-real-p (real value)
  (and
   (q727102-real-p real value)
   (q727102-r-lt
    real (q727102-r-zero real) value)))

(defun q727102-v-sub (space left right)
  (q727102-v-add space left (q727102-v-neg space right)))

;; A Dedekind-complete ordered field, hence a presentation of the real field.

(defun-sk q727102-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q727102-real-p real x)
      (q727102-real-p real y)
      (q727102-real-p real z))
     (let* ((zero (q727102-r-zero real))
            (one (q727102-r-one real))
            (xy-add (q727102-r-add real x y))
            (yz-add (q727102-r-add real y z))
            (xy-mul (q727102-r-mul real x y))
            (yz-mul (q727102-r-mul real y z))
            (neg-x (q727102-r-neg real x))
            (inv-x (q727102-r-inv real x)))
       (and
        (q727102-real-p real xy-add)
        (q727102-real-p real xy-mul)
        (q727102-real-p real neg-x)
        (q727102-real-p real inv-x)
        (equal
         (q727102-r-add real xy-add z)
         (q727102-r-add real x yz-add))
        (equal xy-add (q727102-r-add real y x))
        (equal (q727102-r-add real x zero) x)
        (equal (q727102-r-add real x neg-x) zero)
        (equal
         (q727102-r-mul real xy-mul z)
         (q727102-r-mul real x yz-mul))
        (equal xy-mul (q727102-r-mul real y x))
        (equal (q727102-r-mul real x one) x)
        (equal (q727102-r-inv real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q727102-r-mul real x inv-x)
          one))
        (equal
         (q727102-r-mul real x yz-add)
         (q727102-r-add
          real
          (q727102-r-mul real x y)
          (q727102-r-mul real x z))))))))

(defun-sk q727102-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q727102-real-p real x)
      (q727102-real-p real y)
      (q727102-real-p real z))
     (and
      (not (q727102-r-lt real x x))
      (or
       (q727102-r-lt real x y)
       (equal x y)
       (q727102-r-lt real y x))
      (implies
       (and
        (q727102-r-lt real x y)
        (q727102-r-lt real y z))
       (q727102-r-lt real x z))
      (implies
       (q727102-r-lt real x y)
       (q727102-r-lt
        real
        (q727102-r-add real x z)
        (q727102-r-add real y z)))
      (implies
       (and
        (q727102-r-lt
         real (q727102-r-zero real) x)
        (q727102-r-lt
         real (q727102-r-zero real) y))
       (q727102-r-lt
        real
        (q727102-r-zero real)
        (q727102-r-mul real x y)))))))

(defun-sk q727102-valid-real-set-p (real set)
  (forall (x)
    (implies
     (q727102-real-set-member-p real set x)
     (q727102-real-p real x))))

(defun-sk q727102-real-set-nonempty-p (real set)
  (exists (x)
    (and
     (q727102-real-p real x)
     (q727102-real-set-member-p real set x))))

(defun-sk q727102-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (q727102-real-set-member-p real set x)
     (q727102-r-le real x bound))))

(defun-sk q727102-bounded-above-p (real set)
  (exists (bound)
    (and
     (q727102-real-p real bound)
     (q727102-upper-bound-p real set bound))))

(defun-sk q727102-least-upper-bound-p
    (real set supremum)
  (forall (bound)
    (implies
     (and
      (q727102-real-p real bound)
      (q727102-upper-bound-p real set bound))
     (q727102-r-le real supremum bound))))

(defun q727102-supremum-p (real set supremum)
  (and
   (q727102-real-p real supremum)
   (q727102-upper-bound-p real set supremum)
   (q727102-least-upper-bound-p real set supremum)))

(defun-sk q727102-supremum-exists-p (real set)
  (exists (supremum)
    (q727102-supremum-p real set supremum)))

(defun-sk q727102-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q727102-valid-real-set-p real set)
      (q727102-real-set-nonempty-p real set)
      (q727102-bounded-above-p real set))
     (q727102-supremum-exists-p real set))))

(defun q727102-real-structure-p (real)
  (and
   (q727102-real-p real (q727102-r-zero real))
   (q727102-real-p real (q727102-r-one real))
   (not
    (equal
     (q727102-r-zero real)
     (q727102-r-one real)))
   (q727102-r-lt
    real
    (q727102-r-zero real)
    (q727102-r-one real))
   (q727102-field-laws-p real)
   (q727102-order-laws-p real)
   (q727102-dedekind-complete-p real)))

;; Arbitrary real normed vector spaces.

(defun-sk q727102-additive-group-laws-p (space)
  (forall (x y z)
    (implies
     (and
      (q727102-vector-p space x)
      (q727102-vector-p space y)
      (q727102-vector-p space z))
     (let* ((zero (q727102-v-zero space))
            (xy (q727102-v-add space x y))
            (yz (q727102-v-add space y z))
            (neg-x (q727102-v-neg space x)))
       (and
        (q727102-vector-p space zero)
        (q727102-vector-p space xy)
        (q727102-vector-p space neg-x)
        (equal
         (q727102-v-add space xy z)
         (q727102-v-add space x yz))
        (equal xy (q727102-v-add space y x))
        (equal (q727102-v-add space x zero) x)
        (equal (q727102-v-add space x neg-x) zero))))))

(defun-sk q727102-scalar-action-laws-p (real space)
  (forall (a b x y)
    (implies
     (and
      (q727102-real-p real a)
      (q727102-real-p real b)
      (q727102-vector-p space x)
      (q727102-vector-p space y))
     (let ((ax (q727102-v-smul real space a x))
           (bx (q727102-v-smul real space b x)))
       (and
        (q727102-vector-p space ax)
        (equal
         (q727102-v-smul
          real space (q727102-r-one real) x)
         x)
        (equal
         (q727102-v-smul
          real space
          (q727102-r-mul real a b)
          x)
         (q727102-v-smul real space a bx))
        (equal
         (q727102-v-smul
          real space
          (q727102-r-add real a b)
          x)
         (q727102-v-add space ax bx))
        (equal
         (q727102-v-smul
          real space a
          (q727102-v-add space x y))
         (q727102-v-add
          space
          ax
          (q727102-v-smul real space a y))))))))

(defun-sk q727102-norm-laws-p (real space)
  (forall (a x y)
    (implies
     (and
      (q727102-real-p real a)
      (q727102-vector-p space x)
      (q727102-vector-p space y))
     (let ((nx (q727102-v-norm real space x))
           (ny (q727102-v-norm real space y)))
       (and
        (q727102-real-p real nx)
        (q727102-r-le
         real (q727102-r-zero real) nx)
        (iff
         (equal nx (q727102-r-zero real))
         (equal x (q727102-v-zero space)))
        (equal
         (q727102-v-norm
          real space
          (q727102-v-smul real space a x))
         (q727102-r-mul
          real (q727102-r-abs real a) nx))
        (q727102-r-le
         real
         (q727102-v-norm
          real space
          (q727102-v-add space x y))
         (q727102-r-add real nx ny)))))))

(defun q727102-real-normed-space-p (real space)
  (and
   (q727102-vector-p space (q727102-v-zero space))
   (q727102-additive-group-laws-p space)
   (q727102-scalar-action-laws-p real space)
   (q727102-norm-laws-p real space)))

;; Arbitrary functions E -> R and continuous real-linear maps E -> R.

(defun-sk q727102-vector-function-p (real space function)
  (forall (x)
    (implies
     (q727102-vector-p space x)
     (q727102-real-p
      real
      (q727102-function-value function x)))))

(defun-sk q727102-linear-laws-p
    (real space linear-map)
  (forall (a x y)
    (implies
     (and
      (q727102-real-p real a)
      (q727102-vector-p space x)
      (q727102-vector-p space y))
     (and
      (q727102-real-p
       real
       (q727102-linear-value linear-map x))
      (equal
       (q727102-linear-value
        linear-map
        (q727102-v-add space x y))
       (q727102-r-add
        real
        (q727102-linear-value linear-map x)
        (q727102-linear-value linear-map y)))
      (equal
       (q727102-linear-value
        linear-map
        (q727102-v-smul real space a x))
       (q727102-r-mul
        real a
        (q727102-linear-value linear-map x)))))))

(defun-sk q727102-linear-bound-p
    (real space linear-map bound)
  (forall (x)
    (implies
     (q727102-vector-p space x)
     (q727102-r-le
      real
      (q727102-r-abs
       real
       (q727102-linear-value linear-map x))
      (q727102-r-mul
       real
       bound
       (q727102-v-norm real space x))))))

(defun-sk q727102-linear-bound-exists-p
    (real space linear-map)
  (exists (bound)
    (and
     (q727102-real-p real bound)
     (q727102-r-le
      real (q727102-r-zero real) bound)
     (q727102-linear-bound-p
      real space linear-map bound))))

(defun q727102-continuous-linear-map-p
    (real space linear-map)
  (and
   (q727102-linear-laws-p real space linear-map)
   (q727102-linear-bound-exists-p
    real space linear-map)))

;; Local minima and maxima use open metric balls, a neighborhood basis for
;; the norm topology. Their disjunction is mathlib's IsLocalExtr.

(defun-sk q727102-vector-local-min-neighborhood-p
    (real space function point radius)
  (forall (x)
    (implies
     (and
      (q727102-vector-p space x)
      (q727102-r-lt
       real
       (q727102-v-norm
        real space
        (q727102-v-sub space x point))
       radius))
     (q727102-r-le
      real
      (q727102-function-value function point)
      (q727102-function-value function x)))))

(defun-sk q727102-vector-local-min-p
    (real space function point)
  (exists (radius)
    (and
     (q727102-positive-real-p real radius)
     (q727102-vector-local-min-neighborhood-p
      real space function point radius))))

(defun-sk q727102-vector-local-max-neighborhood-p
    (real space function point radius)
  (forall (x)
    (implies
     (and
      (q727102-vector-p space x)
      (q727102-r-lt
       real
       (q727102-v-norm
        real space
        (q727102-v-sub space x point))
       radius))
     (q727102-r-le
      real
      (q727102-function-value function x)
      (q727102-function-value function point)))))

(defun-sk q727102-vector-local-max-p
    (real space function point)
  (exists (radius)
    (and
     (q727102-positive-real-p real radius)
     (q727102-vector-local-max-neighborhood-p
      real space function point radius))))

(defun q727102-vector-local-extr-p
    (real space function point)
  (or
   (q727102-vector-local-min-p
    real space function point)
   (q727102-vector-local-max-p
    real space function point)))

;; Frechet differentiability E -> R, expanded by the epsilon-delta remainder
;; estimate. DEFCHOOSE retains a derivative internally when one exists.

(defun q727102-fderiv-remainder
    (real space function point linear-map x)
  (q727102-r-sub
   real
   (q727102-r-sub
    real
    (q727102-function-value function x)
    (q727102-function-value function point))
   (q727102-linear-value
    linear-map
    (q727102-v-sub space x point))))

(defun-sk q727102-fderiv-neighborhood-p
    (real space function point linear-map epsilon radius)
  (forall (x)
    (implies
     (and
      (q727102-vector-p space x)
      (q727102-r-lt
       real
       (q727102-v-norm
        real space
        (q727102-v-sub space x point))
       radius))
     (q727102-r-le
      real
      (q727102-r-abs
       real
       (q727102-fderiv-remainder
        real space function point linear-map x))
      (q727102-r-mul
       real
       epsilon
       (q727102-v-norm
        real space
        (q727102-v-sub space x point)))))))

(defun-sk q727102-fderiv-radius-exists-p
    (real space function point linear-map epsilon)
  (exists (radius)
    (and
     (q727102-positive-real-p real radius)
     (q727102-fderiv-neighborhood-p
      real space function point linear-map
      epsilon radius))))

(defun-sk q727102-fderiv-limit-p
    (real space function point linear-map)
  (forall (epsilon)
    (implies
     (q727102-positive-real-p real epsilon)
     (q727102-fderiv-radius-exists-p
      real space function point linear-map epsilon))))

(defun q727102-has-fderiv-at-p
    (real space function point linear-map)
  (and
   (q727102-vector-p space point)
   (q727102-continuous-linear-map-p
    real space linear-map)
   (q727102-fderiv-limit-p
    real space function point linear-map)))

(defun-sk q727102-differentiable-at-p
    (real space function point)
  (exists (linear-map)
    (q727102-has-fderiv-at-p
     real space function point linear-map)))

(defchoose q727102-fderiv-choice
    (linear-map)
    (real space function point)
  (q727102-has-fderiv-at-p
   real space function point linear-map))

(defun q727102-fderiv-apply
    (real space function point direction)
  (if
      (q727102-differentiable-at-p
       real space function point)
      (q727102-linear-value
       (q727102-fderiv-choice
        real space function point)
       direction)
    (q727102-r-zero real)))

(defun-sk q727102-fderiv-eq-zero-p
    (real space function point)
  (forall (direction)
    (implies
     (q727102-vector-p space direction)
     (equal
      (q727102-fderiv-apply
       real space function point direction)
      (q727102-r-zero real)))))

;; The scalar specialization R -> R, including mathlib's totalized deriv.

(defun-sk q727102-real-function-p (real function)
  (forall (x)
    (implies
     (q727102-real-p real x)
     (q727102-real-p
      real
      (q727102-function-value function x)))))

(defun-sk q727102-real-local-min-neighborhood-p
    (real function point radius)
  (forall (x)
    (implies
     (and
      (q727102-real-p real x)
      (q727102-r-lt
       real
       (q727102-r-abs
        real
        (q727102-r-sub real x point))
       radius))
     (q727102-r-le
      real
      (q727102-function-value function point)
      (q727102-function-value function x)))))

(defun-sk q727102-real-local-min-p
    (real function point)
  (exists (radius)
    (and
     (q727102-positive-real-p real radius)
     (q727102-real-local-min-neighborhood-p
      real function point radius))))

(defun-sk q727102-real-local-max-neighborhood-p
    (real function point radius)
  (forall (x)
    (implies
     (and
      (q727102-real-p real x)
      (q727102-r-lt
       real
       (q727102-r-abs
        real
        (q727102-r-sub real x point))
       radius))
     (q727102-r-le
      real
      (q727102-function-value function x)
      (q727102-function-value function point)))))

(defun-sk q727102-real-local-max-p
    (real function point)
  (exists (radius)
    (and
     (q727102-positive-real-p real radius)
     (q727102-real-local-max-neighborhood-p
      real function point radius))))

(defun q727102-real-local-extr-p
    (real function point)
  (or
   (q727102-real-local-min-p real function point)
   (q727102-real-local-max-p real function point)))

(defun q727102-deriv-remainder
    (real function point derivative x)
  (q727102-r-sub
   real
   (q727102-r-sub
    real
    (q727102-function-value function x)
    (q727102-function-value function point))
   (q727102-r-mul
    real derivative
    (q727102-r-sub real x point))))

(defun-sk q727102-deriv-neighborhood-p
    (real function point derivative epsilon radius)
  (forall (x)
    (implies
     (and
      (q727102-real-p real x)
      (q727102-r-lt
       real
       (q727102-r-abs
        real
        (q727102-r-sub real x point))
       radius))
     (q727102-r-le
      real
      (q727102-r-abs
       real
       (q727102-deriv-remainder
        real function point derivative x))
      (q727102-r-mul
       real
       epsilon
       (q727102-r-abs
        real
        (q727102-r-sub real x point)))))))

(defun-sk q727102-deriv-radius-exists-p
    (real function point derivative epsilon)
  (exists (radius)
    (and
     (q727102-positive-real-p real radius)
     (q727102-deriv-neighborhood-p
      real function point derivative epsilon radius))))

(defun-sk q727102-has-deriv-at-p
    (real function point derivative)
  (forall (epsilon)
    (implies
     (q727102-positive-real-p real epsilon)
     (and
      (q727102-real-p real point)
      (q727102-real-p real derivative)
      (q727102-deriv-radius-exists-p
       real function point derivative epsilon)))))

(defun-sk q727102-scalar-differentiable-at-p
    (real function point)
  (exists (derivative)
    (and
     (q727102-real-p real derivative)
     (q727102-has-deriv-at-p
      real function point derivative))))

(defchoose q727102-deriv-choice
    (derivative)
    (real function point)
  (and
   (q727102-real-p real derivative)
   (q727102-has-deriv-at-p
    real function point derivative)))

(defun q727102-deriv-value
    (real function point)
  (if
      (q727102-scalar-differentiable-at-p
       real function point)
      (q727102-deriv-choice real function point)
    (q727102-r-zero real)))

;; The two indexed mathlib declarations have independent universal scopes.

(defun-sk q727102-fderiv-eq-zero-statement-p ()
  (forall (real space function point)
    (implies
     (and
      (q727102-real-structure-p real)
      (q727102-real-normed-space-p real space)
      (q727102-vector-function-p real space function)
      (q727102-vector-p space point)
      (q727102-vector-local-extr-p
       real space function point))
     (q727102-fderiv-eq-zero-p
      real space function point))))

(defun-sk q727102-deriv-eq-zero-statement-p ()
  (forall (real function point)
    (implies
     (and
      (q727102-real-structure-p real)
      (q727102-real-function-p real function)
      (q727102-real-p real point)
      (q727102-real-local-extr-p
       real function point))
     (equal
      (q727102-deriv-value real function point)
      (q727102-r-zero real)))))

(defun thousand-theorems-q727102-fermat-stationary-points-statement ()
  (and
   (q727102-fderiv-eq-zero-statement-p)
   (q727102-deriv-eq-zero-statement-p)))

(value-triple :itpeval-statement-checked)
:q
