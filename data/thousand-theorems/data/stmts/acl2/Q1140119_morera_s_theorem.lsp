;; Statement-only formalization of thousand-theorems corpus artifact Q1140119,
;; "Morera's theorem": on an open subset of the complex plane, a function into
;; an arbitrary complex Banach space is differentiable exactly when it is
;; continuous and its integrals around all contained rectangles vanish.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; A Dedekind-complete ordered field presents the real numbers. Complex
;; numbers are explicit real-coordinate pairs. The codomain is an arbitrary
;; complete normed complex vector space.

(defstub q1140119-r-member-p (real value) t)
(defstub q1140119-r-zero (real) t)
(defstub q1140119-r-one (real) t)
(defstub q1140119-r-add (real left right) t)
(defstub q1140119-r-multiply (real left right) t)
(defstub q1140119-r-negate (real value) t)
(defstub q1140119-r-inverse (real value) t)
(defstub q1140119-r-less (real left right) t)
(defstub q1140119-r-set-member-p (real set value) t)

(defun q1140119-r-subtract (real left right)
  (q1140119-r-add
   real left (q1140119-r-negate real right)))

(defun q1140119-r-leq (real left right)
  (not (q1140119-r-less real right left)))

(defun q1140119-r-positive-p (real value)
  (and
   (q1140119-r-member-p real value)
   (q1140119-r-less
    real (q1140119-r-zero real) value)))

(defun q1140119-r-square (real value)
  (q1140119-r-multiply real value value))

(defun-sk q1140119-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q1140119-r-member-p real x)
      (q1140119-r-member-p real y)
      (q1140119-r-member-p real z))
     (let* ((zero (q1140119-r-zero real))
            (one (q1140119-r-one real))
            (xy-add (q1140119-r-add real x y))
            (yz-add (q1140119-r-add real y z))
            (xy-mul (q1140119-r-multiply real x y))
            (yz-mul (q1140119-r-multiply real y z))
            (neg-x (q1140119-r-negate real x))
            (inv-x (q1140119-r-inverse real x)))
       (and
        (q1140119-r-member-p real zero)
        (q1140119-r-member-p real one)
        (q1140119-r-member-p real xy-add)
        (q1140119-r-member-p real xy-mul)
        (q1140119-r-member-p real neg-x)
        (q1140119-r-member-p real inv-x)
        (equal
         (q1140119-r-add real xy-add z)
         (q1140119-r-add real x yz-add))
        (equal xy-add (q1140119-r-add real y x))
        (equal (q1140119-r-add real x zero) x)
        (equal (q1140119-r-add real x neg-x) zero)
        (equal
         (q1140119-r-multiply real xy-mul z)
         (q1140119-r-multiply real x yz-mul))
        (equal xy-mul (q1140119-r-multiply real y x))
        (equal (q1140119-r-multiply real x one) x)
        (equal (q1140119-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q1140119-r-multiply real x inv-x)
          one))
        (equal
         (q1140119-r-multiply
          real x (q1140119-r-add real y z))
         (q1140119-r-add
          real
          (q1140119-r-multiply real x y)
          (q1140119-r-multiply real x z))))))))

(defun-sk q1140119-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q1140119-r-member-p real x)
      (q1140119-r-member-p real y)
      (q1140119-r-member-p real z))
     (let ((zero (q1140119-r-zero real)))
       (and
        (not (q1140119-r-less real x x))
        (or
         (equal x y)
         (q1140119-r-less real x y)
         (q1140119-r-less real y x))
        (implies
         (and
          (q1140119-r-less real x y)
          (q1140119-r-less real y z))
         (q1140119-r-less real x z))
        (implies
         (q1140119-r-less real x y)
         (q1140119-r-less
          real
          (q1140119-r-add real x z)
          (q1140119-r-add real y z)))
        (implies
         (and
          (q1140119-r-less real zero x)
          (q1140119-r-less real zero y))
         (q1140119-r-less
          real zero
          (q1140119-r-multiply real x y))))))))

(defun-sk q1140119-r-valid-set-p (real set)
  (forall (x)
    (implies
     (q1140119-r-set-member-p real set x)
     (q1140119-r-member-p real x))))

(defun-sk q1140119-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q1140119-r-member-p real x)
     (q1140119-r-set-member-p real set x))))

(defun-sk q1140119-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q1140119-r-member-p real x)
      (q1140119-r-set-member-p real set x))
     (q1140119-r-leq real x bound))))

(defun-sk q1140119-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q1140119-r-member-p real bound)
     (q1140119-r-upper-bound-p real set bound))))

(defun-sk q1140119-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q1140119-r-member-p real supremum)
     (q1140119-r-upper-bound-p real set supremum)
     (implies
      (and
       (q1140119-r-member-p real bound)
       (q1140119-r-upper-bound-p real set bound))
      (q1140119-r-leq real supremum bound)))))

(defun-sk q1140119-r-has-supremum-p (real set)
  (exists (supremum)
    (q1140119-r-supremum-p real set supremum)))

(defun-sk q1140119-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q1140119-r-valid-set-p real set)
      (q1140119-r-set-nonempty-p real set)
      (q1140119-r-bounded-above-p real set))
     (q1140119-r-has-supremum-p real set))))

(defun q1140119-real-field-p (real)
  (let ((zero (q1140119-r-zero real))
        (one (q1140119-r-one real)))
    (and
     (q1140119-r-member-p real zero)
     (q1140119-r-member-p real one)
     (not (equal zero one))
     (q1140119-r-field-laws-p real)
     (q1140119-r-order-laws-p real)
     (q1140119-r-less real zero one)
     (q1140119-r-dedekind-complete-p real))))

;; Complex arithmetic in real coordinates.

(defun q1140119-c-member-p (real value)
  (and
   (consp value)
   (q1140119-r-member-p real (car value))
   (q1140119-r-member-p real (cdr value))))

(defun q1140119-c-make (real-part imaginary-part)
  (cons real-part imaginary-part))

(defun q1140119-c-re (value)
  (car value))

(defun q1140119-c-im (value)
  (cdr value))

(defun q1140119-c-zero (real)
  (q1140119-c-make
   (q1140119-r-zero real)
   (q1140119-r-zero real)))

(defun q1140119-c-one (real)
  (q1140119-c-make
   (q1140119-r-one real)
   (q1140119-r-zero real)))

(defun q1140119-c-I (real)
  (q1140119-c-make
   (q1140119-r-zero real)
   (q1140119-r-one real)))

(defun q1140119-c-of-real (real value)
  (q1140119-c-make value (q1140119-r-zero real)))

(defun q1140119-c-add (real left right)
  (q1140119-c-make
   (q1140119-r-add
    real
    (q1140119-c-re left)
    (q1140119-c-re right))
   (q1140119-r-add
    real
    (q1140119-c-im left)
    (q1140119-c-im right))))

(defun q1140119-c-negate (real value)
  (q1140119-c-make
   (q1140119-r-negate real (q1140119-c-re value))
   (q1140119-r-negate real (q1140119-c-im value))))

(defun q1140119-c-subtract (real left right)
  (q1140119-c-add
   real left (q1140119-c-negate real right)))

(defun q1140119-c-multiply (real left right)
  (let ((a (q1140119-c-re left))
        (b (q1140119-c-im left))
        (c (q1140119-c-re right))
        (d (q1140119-c-im right)))
    (q1140119-c-make
     (q1140119-r-subtract
      real
      (q1140119-r-multiply real a c)
      (q1140119-r-multiply real b d))
     (q1140119-r-add
      real
      (q1140119-r-multiply real a d)
      (q1140119-r-multiply real b c)))))

(defun q1140119-c-modulus-square (real value)
  (q1140119-r-add
   real
   (q1140119-r-square real (q1140119-c-re value))
   (q1140119-r-square real (q1140119-c-im value))))

(defun q1140119-c-distance-square (real left right)
  (q1140119-c-modulus-square
   real (q1140119-c-subtract real left right)))

;; Arbitrary complex normed vector spaces and functions C -> E.

(defstub q1140119-e-member-p (space value) t)
(defstub q1140119-e-zero (space) t)
(defstub q1140119-e-add (space left right) t)
(defstub q1140119-e-negate (space value) t)
(defstub q1140119-e-smul (real space scalar vector) t)
(defstub q1140119-e-norm (real space value) t)
(defstub q1140119-set-member-p (set value) t)
(defstub q1140119-function-value (function argument) t)
(defstub q1140119-sequence-value (sequence index) t)

(defun q1140119-e-subtract (space left right)
  (q1140119-e-add
   space left (q1140119-e-negate space right)))

(defun-sk q1140119-e-additive-laws-p (real space)
  (forall (x y z)
    (implies
     (and
      (q1140119-e-member-p space x)
      (q1140119-e-member-p space y)
      (q1140119-e-member-p space z))
     (let* ((zero (q1140119-e-zero space))
            (xy (q1140119-e-add space x y))
            (yz (q1140119-e-add space y z))
            (neg-x (q1140119-e-negate space x))
            (norm-x (q1140119-e-norm real space x))
            (norm-y (q1140119-e-norm real space y)))
       (and
        (q1140119-e-member-p space zero)
        (q1140119-e-member-p space xy)
        (q1140119-e-member-p space neg-x)
        (q1140119-r-member-p real norm-x)
        (q1140119-r-member-p real norm-y)
        (equal
         (q1140119-e-add space xy z)
         (q1140119-e-add space x yz))
        (equal xy (q1140119-e-add space y x))
        (equal (q1140119-e-add space x zero) x)
        (equal (q1140119-e-add space x neg-x) zero)
        (q1140119-r-leq
         real (q1140119-r-zero real) norm-x)
        (iff
         (equal norm-x (q1140119-r-zero real))
         (equal x zero))
        (equal
         (q1140119-e-norm real space neg-x)
         norm-x)
        (q1140119-r-leq
         real
         (q1140119-e-norm real space xy)
         (q1140119-r-add real norm-x norm-y)))))))

(defun-sk q1140119-e-scalar-laws-p (real space)
  (forall (a b x y)
    (implies
     (and
      (q1140119-c-member-p real a)
      (q1140119-c-member-p real b)
      (q1140119-e-member-p space x)
      (q1140119-e-member-p space y))
     (let ((zero-e (q1140119-e-zero space))
           (ax (q1140119-e-smul real space a x)))
       (and
        (q1140119-e-member-p space ax)
        (equal
         (q1140119-e-smul
          real space (q1140119-c-one real) x)
         x)
        (equal
         (q1140119-e-smul
          real space
          (q1140119-c-multiply real a b)
          x)
         (q1140119-e-smul
          real space a
          (q1140119-e-smul real space b x)))
        (equal
         (q1140119-e-smul
          real space
          (q1140119-c-add real a b)
          x)
         (q1140119-e-add
          space
          (q1140119-e-smul real space a x)
          (q1140119-e-smul real space b x)))
        (equal
         (q1140119-e-smul
          real space a
          (q1140119-e-add space x y))
         (q1140119-e-add
          space
          (q1140119-e-smul real space a x)
          (q1140119-e-smul real space a y)))
        (equal
         (q1140119-e-smul
          real space (q1140119-c-zero real) x)
         zero-e)
        (equal
         (q1140119-e-smul real space a zero-e)
         zero-e)
        (equal
         (q1140119-r-square
          real (q1140119-e-norm real space ax))
         (q1140119-r-multiply
          real
          (q1140119-c-modulus-square real a)
          (q1140119-r-square
           real (q1140119-e-norm real space x)))))))))

(defun q1140119-complex-normed-space-p (real space)
  (and
   (q1140119-e-member-p space (q1140119-e-zero space))
   (q1140119-e-additive-laws-p real space)
   (q1140119-e-scalar-laws-p real space)))

(defun-sk q1140119-sequence-in-space-p (space sequence)
  (forall (index)
    (implies
     (natp index)
     (q1140119-e-member-p
      space (q1140119-sequence-value sequence index)))))

(defun-sk q1140119-cauchy-tail-p
    (real space sequence epsilon cutoff)
  (forall (left-index right-index)
    (implies
     (and
      (natp left-index)
      (natp right-index)
      (natp cutoff)
      (<= cutoff left-index)
      (<= cutoff right-index))
     (q1140119-r-less
      real
      (q1140119-e-norm
       real space
       (q1140119-e-subtract
        space
        (q1140119-sequence-value sequence left-index)
        (q1140119-sequence-value sequence right-index)))
      epsilon))))

(defun-sk q1140119-cauchy-cutoff-exists-p
    (real space sequence epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q1140119-cauchy-tail-p
      real space sequence epsilon cutoff))))

(defun-sk q1140119-cauchy-sequence-p
    (real space sequence)
  (forall (epsilon)
    (implies
     (q1140119-r-positive-p real epsilon)
     (q1140119-cauchy-cutoff-exists-p
      real space sequence epsilon))))

(defun-sk q1140119-convergence-tail-p
    (real space sequence limit epsilon cutoff)
  (forall (index)
    (implies
     (and
      (natp index)
      (natp cutoff)
      (<= cutoff index))
     (q1140119-r-less
      real
      (q1140119-e-norm
       real space
       (q1140119-e-subtract
        space
        (q1140119-sequence-value sequence index)
        limit))
      epsilon))))

(defun-sk q1140119-convergence-cutoff-exists-p
    (real space sequence limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q1140119-convergence-tail-p
      real space sequence limit epsilon cutoff))))

(defun-sk q1140119-sequence-converges-p
    (real space sequence limit)
  (forall (epsilon)
    (implies
     (q1140119-r-positive-p real epsilon)
     (q1140119-convergence-cutoff-exists-p
      real space sequence limit epsilon))))

(defun-sk q1140119-sequence-limit-exists-p
    (real space sequence)
  (exists (limit)
    (and
     (q1140119-e-member-p space limit)
     (q1140119-sequence-converges-p
      real space sequence limit))))

(defun-sk q1140119-complete-space-p (real space)
  (forall (sequence)
    (implies
     (and
      (q1140119-sequence-in-space-p space sequence)
      (q1140119-cauchy-sequence-p real space sequence))
     (q1140119-sequence-limit-exists-p
      real space sequence))))

(defun q1140119-complex-banach-space-p (real space)
  (and
   (q1140119-complex-normed-space-p real space)
   (q1140119-complete-space-p real space)))

(defun-sk q1140119-valid-complex-set-p (real set)
  (forall (z)
    (implies
     (q1140119-set-member-p set z)
     (q1140119-c-member-p real z))))

(defun-sk q1140119-function-into-space-p
    (real space function)
  (forall (z)
    (implies
     (q1140119-c-member-p real z)
     (q1140119-e-member-p
      space (q1140119-function-value function z)))))

;; Squared complex distances generate the ordinary complex norm topology.

(defun-sk q1140119-ball-contained-p
    (real set center radius-square)
  (forall (point)
    (implies
     (and
      (q1140119-c-member-p real point)
      (q1140119-r-less
       real
       (q1140119-c-distance-square real point center)
       radius-square))
     (q1140119-set-member-p set point))))

(defun-sk q1140119-open-radius-exists-p
    (real set center)
  (exists (radius-square)
    (and
     (q1140119-r-positive-p real radius-square)
     (q1140119-ball-contained-p
      real set center radius-square))))

(defun-sk q1140119-open-set-p (real set)
  (forall (center)
    (implies
     (q1140119-set-member-p set center)
     (q1140119-open-radius-exists-p
      real set center))))

(defun-sk q1140119-continuity-neighborhood-p
    (real space set function center epsilon radius-square)
  (forall (point)
    (implies
     (and
      (q1140119-c-member-p real point)
      (q1140119-set-member-p set point)
      (q1140119-r-less
       real
       (q1140119-c-distance-square real point center)
       radius-square))
     (q1140119-r-less
      real
      (q1140119-e-norm
       real space
       (q1140119-e-subtract
        space
        (q1140119-function-value function point)
        (q1140119-function-value function center)))
      epsilon))))

(defun-sk q1140119-continuity-radius-exists-p
    (real space set function center epsilon)
  (exists (radius-square)
    (and
     (q1140119-r-positive-p real radius-square)
     (q1140119-continuity-neighborhood-p
      real space set function center epsilon radius-square))))

(defun-sk q1140119-continuous-within-at-p
    (real space set function center)
  (forall (epsilon)
    (implies
     (q1140119-r-positive-p real epsilon)
     (q1140119-continuity-radius-exists-p
      real space set function center epsilon))))

(defun-sk q1140119-continuous-on-p
    (real space set function)
  (forall (center)
    (implies
     (q1140119-set-member-p set center)
     (q1140119-continuous-within-at-p
      real space set function center))))

;; Complex Frechet differentiability C -> E. A complex-linear map from C is
;; uniquely determined by its value at one, so its action is h |-> h * d.
;; Squaring the standard norm estimate gives an equivalent epsilon-delta
;; condition without introducing a square-root operation on the real field.

(defun q1140119-derivative-remainder
    (real space function center point derivative)
  (q1140119-e-subtract
   space
   (q1140119-e-subtract
    space
    (q1140119-function-value function point)
    (q1140119-function-value function center))
   (q1140119-e-smul
    real space
    (q1140119-c-subtract real point center)
    derivative)))

(defun-sk q1140119-derivative-neighborhood-p
    (real space set function center derivative
          epsilon radius-square)
  (forall (point)
    (implies
     (and
      (q1140119-c-member-p real point)
      (q1140119-set-member-p set point)
      (q1140119-r-less
       real
       (q1140119-c-distance-square real point center)
       radius-square))
     (q1140119-r-leq
      real
      (q1140119-r-square
       real
       (q1140119-e-norm
        real space
        (q1140119-derivative-remainder
         real space function center point derivative)))
      (q1140119-r-multiply
       real
       (q1140119-r-square real epsilon)
       (q1140119-c-distance-square
        real point center))))))

(defun-sk q1140119-derivative-radius-exists-p
    (real space set function center derivative epsilon)
  (exists (radius-square)
    (and
     (q1140119-r-positive-p real radius-square)
     (q1140119-derivative-neighborhood-p
      real space set function center derivative
      epsilon radius-square))))

(defun-sk q1140119-has-derivative-within-at-p
    (real space set function center derivative)
  (forall (epsilon)
    (implies
     (q1140119-r-positive-p real epsilon)
     (q1140119-derivative-radius-exists-p
      real space set function center derivative epsilon))))

(defun-sk q1140119-differentiable-within-at-p
    (real space set function center)
  (exists (derivative)
    (and
     (q1140119-e-member-p space derivative)
     (q1140119-has-derivative-within-at-p
      real space set function center derivative))))

(defun-sk q1140119-differentiable-on-p
    (real space set function)
  (forall (center)
    (implies
     (q1140119-set-member-p set center)
     (q1140119-differentiable-within-at-p
      real space set function center))))

;; Uniform right-endpoint Riemann sums characterize each vector-valued
;; interval integral along a rectangle edge. For continuous edge restrictions
;; these are the source Bochner interval integrals. If no E-valued limit
;; exists, the value is zero, matching Mathlib's totalized integral for a
;; nonintegrable function. Completeness is an explicit source assumption.

(defun q1140119-r-natural (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1140119-r-zero real)
    (q1140119-r-add
     real
     (q1140119-r-one real)
     (q1140119-r-natural real (- n 1)))))

(defun q1140119-horizontal-point
    (real z step index)
  (q1140119-c-make
   (q1140119-r-add
    real
    (q1140119-c-re z)
    (q1140119-r-multiply
     real
     (q1140119-r-natural real index)
     step))
   (q1140119-c-im z)))

(defun q1140119-vertical-point
    (real z step index)
  (q1140119-c-make
   (q1140119-c-re z)
   (q1140119-r-add
    real
    (q1140119-c-im z)
    (q1140119-r-multiply
     real
     (q1140119-r-natural real index)
     step))))

(defun q1140119-horizontal-sum
    (real space function z step remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (q1140119-e-zero space)
    (q1140119-e-add
     space
     (q1140119-function-value
      function
      (q1140119-horizontal-point
       real z step remaining))
     (q1140119-horizontal-sum
      real space function z step (- remaining 1)))))

(defun q1140119-vertical-sum
    (real space function z step remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (q1140119-e-zero space)
    (q1140119-e-add
     space
     (q1140119-function-value
      function
      (q1140119-vertical-point
       real z step remaining))
     (q1140119-vertical-sum
      real space function z step (- remaining 1)))))

(defun q1140119-horizontal-riemann-sum
    (real space function z w pieces)
  (if (posp pieces)
      (let* ((denominator
              (q1140119-r-natural real pieces))
             (step
              (q1140119-r-multiply
               real
               (q1140119-r-subtract
                real
                (q1140119-c-re w)
                (q1140119-c-re z))
               (q1140119-r-inverse real denominator))))
        (q1140119-e-smul
         real space
         (q1140119-c-of-real real step)
         (q1140119-horizontal-sum
          real space function z step pieces)))
    (q1140119-e-zero space)))

(defun q1140119-vertical-riemann-sum
    (real space function z w pieces)
  (if (posp pieces)
      (let* ((denominator
              (q1140119-r-natural real pieces))
             (step
              (q1140119-r-multiply
               real
               (q1140119-r-subtract
                real
                (q1140119-c-im w)
                (q1140119-c-im z))
               (q1140119-r-inverse real denominator))))
        (q1140119-e-smul
         real space
         (q1140119-c-of-real real step)
         (q1140119-vertical-sum
          real space function z step pieces)))
    (q1140119-e-zero space)))

(defun-sk q1140119-horizontal-limit-tail-p
    (real space function z w value epsilon cutoff)
  (forall (pieces)
    (implies
     (and
      (posp pieces)
      (natp cutoff)
      (<= cutoff pieces))
     (q1140119-r-less
      real
      (q1140119-e-norm
       real space
       (q1140119-e-subtract
        space
        (q1140119-horizontal-riemann-sum
         real space function z w pieces)
        value))
      epsilon))))

(defun-sk q1140119-horizontal-limit-cutoff-exists-p
    (real space function z w value epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (q1140119-horizontal-limit-tail-p
      real space function z w value epsilon cutoff))))

(defun-sk q1140119-horizontal-limit-p
    (real space function z w value)
  (forall (epsilon)
    (implies
     (q1140119-r-positive-p real epsilon)
     (q1140119-horizontal-limit-cutoff-exists-p
      real space function z w value epsilon))))

(defun-sk q1140119-horizontal-limit-exists-p
    (real space function z w)
  (exists (value)
    (and
     (q1140119-e-member-p space value)
     (q1140119-horizontal-limit-p
      real space function z w value))))

(defun q1140119-horizontal-integral-value-p
    (real space function z w value)
  (and
   (q1140119-e-member-p space value)
   (if
       (q1140119-horizontal-limit-exists-p
        real space function z w)
       (q1140119-horizontal-limit-p
        real space function z w value)
     (equal value (q1140119-e-zero space)))))

(defun-sk q1140119-vertical-limit-tail-p
    (real space function z w value epsilon cutoff)
  (forall (pieces)
    (implies
     (and
      (posp pieces)
      (natp cutoff)
      (<= cutoff pieces))
     (q1140119-r-less
      real
      (q1140119-e-norm
       real space
       (q1140119-e-subtract
        space
        (q1140119-vertical-riemann-sum
         real space function z w pieces)
        value))
      epsilon))))

(defun-sk q1140119-vertical-limit-cutoff-exists-p
    (real space function z w value epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (q1140119-vertical-limit-tail-p
      real space function z w value epsilon cutoff))))

(defun-sk q1140119-vertical-limit-p
    (real space function z w value)
  (forall (epsilon)
    (implies
     (q1140119-r-positive-p real epsilon)
     (q1140119-vertical-limit-cutoff-exists-p
      real space function z w value epsilon))))

(defun-sk q1140119-vertical-limit-exists-p
    (real space function z w)
  (exists (value)
    (and
     (q1140119-e-member-p space value)
     (q1140119-vertical-limit-p
      real space function z w value))))

(defun q1140119-vertical-integral-value-p
    (real space function z w value)
  (and
   (q1140119-e-member-p space value)
   (if
       (q1140119-vertical-limit-exists-p
        real space function z w)
       (q1140119-vertical-limit-p
        real space function z w value)
     (equal value (q1140119-e-zero space)))))

;; Rectangle z w is the product of the two unoriented closed coordinate
;; intervals. This is Mathlib's Complex.Rectangle z w.

(defun q1140119-r-between-p (real left value right)
  (or
   (and
    (q1140119-r-leq real left value)
    (q1140119-r-leq real value right))
   (and
    (q1140119-r-leq real right value)
    (q1140119-r-leq real value left))))

(defun q1140119-in-rectangle-p (real z w point)
  (and
   (q1140119-c-member-p real point)
   (q1140119-r-between-p
    real
    (q1140119-c-re z)
    (q1140119-c-re point)
    (q1140119-c-re w))
   (q1140119-r-between-p
    real
    (q1140119-c-im z)
    (q1140119-c-im point)
    (q1140119-c-im w))))

(defun-sk q1140119-rectangle-subset-p
    (real set z w)
  (forall (point)
    (implies
     (q1140119-in-rectangle-p real z w point)
     (q1140119-set-member-p set point))))

(defun q1140119-wedge-equality-for-values-p
    (real space horizontal-zw vertical-zw
          horizontal-wz vertical-wz)
  (equal
   (q1140119-e-add
    space
    horizontal-zw
    (q1140119-e-smul
     real space (q1140119-c-I real) vertical-zw))
   (q1140119-e-negate
    space
    (q1140119-e-add
     space
     horizontal-wz
     (q1140119-e-smul
      real space (q1140119-c-I real) vertical-wz)))))

(defun-sk q1140119-wedge-integrals-cancel-p
    (real space function z w)
  (exists
    (horizontal-zw vertical-zw horizontal-wz vertical-wz)
    (and
     (q1140119-horizontal-integral-value-p
      real space function z w horizontal-zw)
     (q1140119-vertical-integral-value-p
      real space function
      (q1140119-c-make
       (q1140119-c-re w)
       (q1140119-c-im z))
      w vertical-zw)
     (q1140119-horizontal-integral-value-p
      real space function w z horizontal-wz)
     (q1140119-vertical-integral-value-p
      real space function
      (q1140119-c-make
       (q1140119-c-re z)
       (q1140119-c-im w))
      z vertical-wz)
     (q1140119-wedge-equality-for-values-p
      real space
      horizontal-zw vertical-zw
      horizontal-wz vertical-wz))))

(defun-sk q1140119-is-conservative-on-p
    (real space set function)
  (forall (z w)
    (implies
     (and
      (q1140119-c-member-p real z)
      (q1140119-c-member-p real w)
      (q1140119-rectangle-subset-p real set z w))
     (q1140119-wedge-integrals-cancel-p
      real space function z w))))

;; On every continuous edge restriction, the Riemann-limit characterization
;; above is bidirectionally equivalent to the source intervalIntegral.
;; Consequently this conjunction is exactly
;; IsConservativeOn f U /\ ContinuousOn f U, not an approximation.

(defun-sk
    thousand-theorems-q1140119-morera-s-theorem-statement
    ()
  (forall (real space set function)
    (implies
     (and
      (q1140119-real-field-p real)
      (q1140119-complex-banach-space-p real space)
      (q1140119-valid-complex-set-p real set)
      (q1140119-function-into-space-p real space function)
      (q1140119-open-set-p real set))
     (iff
      (and
       (q1140119-is-conservative-on-p
        real space set function)
       (q1140119-continuous-on-p
        real space set function))
      (q1140119-differentiable-on-p
       real space set function)))))

(value-triple :itpeval-statement-checked)
:q
