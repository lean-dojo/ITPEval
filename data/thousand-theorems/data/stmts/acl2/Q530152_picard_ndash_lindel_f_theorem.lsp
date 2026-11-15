;; Statement-only formalization of thousand-theorems corpus artifact Q530152,
;; "Picard–Lindelöf theorem": a Lipschitz time-dependent vector field on a
;; closed ball in a real Banach space has a local integral curve with the
;; prescribed initial value. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces name the real and vector carriers, their
;; operations, arbitrary sets and sequences, the vector field, and arbitrary
;; curves. All ordered-field, normed-space, completeness, continuity,
;; Lipschitz, and derivative conditions are explicit below.

(defstub q530152-real-p (real value) t)
(defstub q530152-real-set-member-p (real set value) t)
(defstub q530152-r-zero (real) t)
(defstub q530152-r-one (real) t)
(defstub q530152-r-add (real left right) t)
(defstub q530152-r-mul (real left right) t)
(defstub q530152-r-neg (real value) t)
(defstub q530152-r-inv (real value) t)
(defstub q530152-r-lt (real left right) t)

(defstub q530152-vector-p (space value) t)
(defstub q530152-v-zero (space) t)
(defstub q530152-v-add (space left right) t)
(defstub q530152-v-neg (space value) t)
(defstub q530152-v-smul (real space scalar vector) t)
(defstub q530152-v-norm (real space vector) t)

(defstub q530152-sequence-value (sequence index) t)
(defstub q530152-field-value (field time point) t)
(defstub q530152-curve-value (curve time) t)

(defun q530152-r-sub (real left right)
  (q530152-r-add real left (q530152-r-neg real right)))

(defun q530152-r-le (real left right)
  (not (q530152-r-lt real right left)))

(defun q530152-r-abs (real value)
  (if (q530152-r-lt real value (q530152-r-zero real))
      (q530152-r-neg real value)
    value))

(defun q530152-r-max (real left right)
  (if (q530152-r-lt real left right)
      right
    left))

(defun q530152-positive-real-p (real value)
  (and
   (q530152-real-p real value)
   (q530152-r-lt
    real (q530152-r-zero real) value)))

(defun q530152-nonnegative-real-p (real value)
  (and
   (q530152-real-p real value)
   (q530152-r-le
    real (q530152-r-zero real) value)))

(defun q530152-v-sub (space left right)
  (q530152-v-add space left (q530152-v-neg space right)))

(defun q530152-distance (real space left right)
  (q530152-v-norm
   real space (q530152-v-sub space left right)))

;; A Dedekind-complete ordered field, hence a presentation of the real field.

(defun-sk q530152-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q530152-real-p real x)
      (q530152-real-p real y)
      (q530152-real-p real z))
     (let* ((zero (q530152-r-zero real))
            (one (q530152-r-one real))
            (xy-add (q530152-r-add real x y))
            (yz-add (q530152-r-add real y z))
            (xy-mul (q530152-r-mul real x y))
            (yz-mul (q530152-r-mul real y z))
            (neg-x (q530152-r-neg real x))
            (inv-x (q530152-r-inv real x)))
       (and
        (q530152-real-p real xy-add)
        (q530152-real-p real xy-mul)
        (q530152-real-p real neg-x)
        (q530152-real-p real inv-x)
        (equal
         (q530152-r-add real xy-add z)
         (q530152-r-add real x yz-add))
        (equal xy-add (q530152-r-add real y x))
        (equal (q530152-r-add real x zero) x)
        (equal (q530152-r-add real x neg-x) zero)
        (equal
         (q530152-r-mul real xy-mul z)
         (q530152-r-mul real x yz-mul))
        (equal xy-mul (q530152-r-mul real y x))
        (equal (q530152-r-mul real x one) x)
        (equal (q530152-r-inv real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q530152-r-mul real x inv-x)
          one))
        (equal
         (q530152-r-mul real x yz-add)
         (q530152-r-add
          real
          (q530152-r-mul real x y)
          (q530152-r-mul real x z))))))))

(defun-sk q530152-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q530152-real-p real x)
      (q530152-real-p real y)
      (q530152-real-p real z))
     (and
      (not (q530152-r-lt real x x))
      (or
       (q530152-r-lt real x y)
       (equal x y)
       (q530152-r-lt real y x))
      (implies
       (and
        (q530152-r-lt real x y)
        (q530152-r-lt real y z))
       (q530152-r-lt real x z))
      (implies
       (q530152-r-lt real x y)
       (q530152-r-lt
        real
        (q530152-r-add real x z)
        (q530152-r-add real y z)))
      (implies
       (and
        (q530152-r-lt
         real (q530152-r-zero real) x)
        (q530152-r-lt
         real (q530152-r-zero real) y))
       (q530152-r-lt
        real
        (q530152-r-zero real)
        (q530152-r-mul real x y)))))))

(defun-sk q530152-valid-real-set-p (real set)
  (forall (x)
    (implies
     (q530152-real-set-member-p real set x)
     (q530152-real-p real x))))

(defun-sk q530152-real-set-nonempty-p (real set)
  (exists (x)
    (and
     (q530152-real-p real x)
     (q530152-real-set-member-p real set x))))

(defun-sk q530152-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (q530152-real-set-member-p real set x)
     (q530152-r-le real x bound))))

(defun-sk q530152-bounded-above-p (real set)
  (exists (bound)
    (and
     (q530152-real-p real bound)
     (q530152-upper-bound-p real set bound))))

(defun-sk q530152-least-upper-bound-p
    (real set supremum)
  (forall (bound)
    (implies
     (and
      (q530152-real-p real bound)
      (q530152-upper-bound-p real set bound))
     (q530152-r-le real supremum bound))))

(defun q530152-supremum-p (real set supremum)
  (and
   (q530152-real-p real supremum)
   (q530152-upper-bound-p real set supremum)
   (q530152-least-upper-bound-p
    real set supremum)))

(defun-sk q530152-supremum-exists-p (real set)
  (exists (supremum)
    (q530152-supremum-p real set supremum)))

(defun-sk q530152-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q530152-valid-real-set-p real set)
      (q530152-real-set-nonempty-p real set)
      (q530152-bounded-above-p real set))
     (q530152-supremum-exists-p real set))))

(defun q530152-real-structure-p (real)
  (and
   (q530152-real-p real (q530152-r-zero real))
   (q530152-real-p real (q530152-r-one real))
   (not
    (equal
     (q530152-r-zero real)
     (q530152-r-one real)))
   (q530152-r-lt
    real
    (q530152-r-zero real)
    (q530152-r-one real))
   (q530152-field-laws-p real)
   (q530152-order-laws-p real)
   (q530152-dedekind-complete-p real)))

;; Real normed vector-space laws.

(defun-sk q530152-additive-group-laws-p (space)
  (forall (x y z)
    (implies
     (and
      (q530152-vector-p space x)
      (q530152-vector-p space y)
      (q530152-vector-p space z))
     (let* ((zero (q530152-v-zero space))
            (xy (q530152-v-add space x y))
            (yz (q530152-v-add space y z))
            (neg-x (q530152-v-neg space x)))
       (and
        (q530152-vector-p space zero)
        (q530152-vector-p space xy)
        (q530152-vector-p space neg-x)
        (equal
         (q530152-v-add space xy z)
         (q530152-v-add space x yz))
        (equal xy (q530152-v-add space y x))
        (equal (q530152-v-add space x zero) x)
        (equal (q530152-v-add space x neg-x) zero))))))

(defun-sk q530152-scalar-action-laws-p (real space)
  (forall (a b x y)
    (implies
     (and
      (q530152-real-p real a)
      (q530152-real-p real b)
      (q530152-vector-p space x)
      (q530152-vector-p space y))
     (let ((ax (q530152-v-smul real space a x))
           (bx (q530152-v-smul real space b x)))
       (and
        (q530152-vector-p space ax)
        (equal
         (q530152-v-smul
          real space (q530152-r-one real) x)
         x)
        (equal
         (q530152-v-smul
          real space
          (q530152-r-mul real a b)
          x)
         (q530152-v-smul real space a bx))
        (equal
         (q530152-v-smul
          real space
          (q530152-r-add real a b)
          x)
         (q530152-v-add space ax bx))
        (equal
         (q530152-v-smul
          real space a
          (q530152-v-add space x y))
         (q530152-v-add
          space
          ax
          (q530152-v-smul real space a y))))))))

(defun-sk q530152-norm-laws-p (real space)
  (forall (a x y)
    (implies
     (and
      (q530152-real-p real a)
      (q530152-vector-p space x)
      (q530152-vector-p space y))
     (let ((nx (q530152-v-norm real space x))
           (ny (q530152-v-norm real space y)))
       (and
        (q530152-real-p real nx)
        (q530152-r-le
         real (q530152-r-zero real) nx)
        (iff
         (equal nx (q530152-r-zero real))
         (equal x (q530152-v-zero space)))
        (equal
         (q530152-v-norm
          real space
          (q530152-v-smul real space a x))
         (q530152-r-mul
          real (q530152-r-abs real a) nx))
        (q530152-r-le
         real
         (q530152-v-norm
          real space
          (q530152-v-add space x y))
         (q530152-r-add real nx ny)))))))

;; Sequential completeness is equivalent to metric completeness for the norm
;; metric. Sequence objects are not finite tables.

(defun-sk q530152-vector-sequence-p (space sequence)
  (forall (n)
    (implies
     (natp n)
     (q530152-vector-p
      space
      (q530152-sequence-value sequence n)))))

(defun-sk q530152-cauchy-tail-p
    (real space sequence epsilon start)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (natp start)
      (<= start m)
      (<= start n))
     (q530152-r-lt
      real
      (q530152-distance
       real space
       (q530152-sequence-value sequence m)
       (q530152-sequence-value sequence n))
      epsilon))))

(defun-sk q530152-cauchy-start-exists-p
    (real space sequence epsilon)
  (exists (start)
    (and
     (natp start)
     (q530152-cauchy-tail-p
      real space sequence epsilon start))))

(defun-sk q530152-cauchy-sequence-p
    (real space sequence)
  (forall (epsilon)
    (implies
     (q530152-positive-real-p real epsilon)
     (q530152-cauchy-start-exists-p
      real space sequence epsilon))))

(defun-sk q530152-convergence-tail-p
    (real space sequence limit epsilon start)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp start)
      (<= start n))
     (q530152-r-lt
      real
      (q530152-distance
       real space
       (q530152-sequence-value sequence n)
       limit)
      epsilon))))

(defun-sk q530152-convergence-start-exists-p
    (real space sequence limit epsilon)
  (exists (start)
    (and
     (natp start)
     (q530152-convergence-tail-p
      real space sequence limit epsilon start))))

(defun-sk q530152-sequence-converges-p
    (real space sequence limit)
  (forall (epsilon)
    (implies
     (q530152-positive-real-p real epsilon)
     (q530152-convergence-start-exists-p
      real space sequence limit epsilon))))

(defun-sk q530152-sequence-limit-exists-p
    (real space sequence)
  (exists (limit)
    (and
     (q530152-vector-p space limit)
     (q530152-sequence-converges-p
      real space sequence limit))))

(defun-sk q530152-complete-space-p (real space)
  (forall (sequence)
    (implies
     (and
      (q530152-vector-sequence-p space sequence)
      (q530152-cauchy-sequence-p
       real space sequence))
     (q530152-sequence-limit-exists-p
      real space sequence))))

(defun q530152-real-banach-space-p (real space)
  (and
   (q530152-vector-p space (q530152-v-zero space))
   (q530152-additive-group-laws-p space)
   (q530152-scalar-action-laws-p real space)
   (q530152-norm-laws-p real space)
   (q530152-complete-space-p real space)))

;; Typed vector fields and curves.

(defun-sk q530152-vector-field-p
    (real space field)
  (forall (time point)
    (implies
     (and
      (q530152-real-p real time)
      (q530152-vector-p space point))
     (q530152-vector-p
      space
      (q530152-field-value field time point)))))

(defun-sk q530152-curve-p (real space curve)
  (forall (time)
    (implies
     (q530152-real-p real time)
     (q530152-vector-p
      space
      (q530152-curve-value curve time)))))

(defun q530152-in-interval-p
    (real tmin tmax time)
  (and
   (q530152-real-p real time)
   (q530152-r-le real tmin time)
   (q530152-r-le real time tmax)))

(defun q530152-in-closed-ball-p
    (real space center radius point)
  (and
   (q530152-vector-p space point)
   (q530152-r-le
    real
    (q530152-distance real space point center)
    radius)))

;; Lipschitz continuity in the space variable on the closed ball.

(defun-sk q530152-lipschitz-at-time-p
    (real space field center radius constant time)
  (forall (left right)
    (implies
     (and
      (q530152-in-closed-ball-p
       real space center radius left)
      (q530152-in-closed-ball-p
       real space center radius right))
     (q530152-r-le
      real
      (q530152-distance
       real space
       (q530152-field-value field time left)
       (q530152-field-value field time right))
      (q530152-r-mul
       real
       constant
       (q530152-distance
        real space left right))))))

(defun-sk q530152-lipschitz-on-cylinder-p
    (real space field tmin tmax center radius constant)
  (forall (time)
    (implies
     (q530152-in-interval-p
      real tmin tmax time)
     (q530152-lipschitz-at-time-p
      real space field center radius constant time))))

;; Continuity in time, within the closed interval, at a fixed space point.

(defun-sk q530152-continuity-neighborhood-p
    (real space field tmin tmax point time epsilon delta)
  (forall (other-time)
    (implies
     (and
      (q530152-in-interval-p
       real tmin tmax other-time)
      (q530152-r-lt
       real
       (q530152-r-abs
        real
        (q530152-r-sub real other-time time))
       delta))
     (q530152-r-lt
      real
      (q530152-distance
       real space
       (q530152-field-value field other-time point)
       (q530152-field-value field time point))
      epsilon))))

(defun-sk q530152-continuity-radius-exists-p
    (real space field tmin tmax point time epsilon)
  (exists (delta)
    (and
     (q530152-positive-real-p real delta)
     (q530152-continuity-neighborhood-p
      real space field tmin tmax point time epsilon delta))))

(defun-sk q530152-continuous-within-at-p
    (real space field tmin tmax point time)
  (forall (epsilon)
    (implies
     (q530152-positive-real-p real epsilon)
     (q530152-continuity-radius-exists-p
      real space field tmin tmax point time epsilon))))

(defun-sk q530152-continuous-on-cylinder-p
    (real space field tmin tmax center radius)
  (forall (point time)
    (implies
     (and
      (q530152-in-closed-ball-p
       real space center radius point)
      (q530152-in-interval-p
       real tmin tmax time))
     (q530152-continuous-within-at-p
      real space field tmin tmax point time))))

;; Uniform norm bound on the vector field over the cylinder.

(defun-sk q530152-field-norm-bounded-p
    (real space field tmin tmax center radius bound)
  (forall (time point)
    (implies
     (and
      (q530152-in-interval-p
       real tmin tmax time)
      (q530152-in-closed-ball-p
       real space center radius point))
     (q530152-r-le
      real
      (q530152-v-norm
       real space
       (q530152-field-value field time point))
      bound))))

(defun q530152-time-radius-bound-p
    (real tmin tmax initial outer-radius
          initial-radius norm-bound)
  (q530152-r-le
   real
   (q530152-r-mul
    real
    norm-bound
    (q530152-r-max
     real
     (q530152-r-sub real tmax initial)
     (q530152-r-sub real initial tmin)))
   (q530152-r-sub
    real outer-radius initial-radius)))

(defun q530152-is-picard-lindelof-p
    (real space field tmin tmax initial center
          outer-radius initial-radius norm-bound
          lipschitz-constant)
  (and
   (q530152-lipschitz-on-cylinder-p
    real space field tmin tmax center
    outer-radius lipschitz-constant)
   (q530152-continuous-on-cylinder-p
    real space field tmin tmax center outer-radius)
   (q530152-field-norm-bounded-p
    real space field tmin tmax center
    outer-radius norm-bound)
   (q530152-time-radius-bound-p
    real tmin tmax initial outer-radius
    initial-radius norm-bound)))

;; HasDerivWithinAt on [tmin,tmax], expanded by the normed-space
;; epsilon-delta remainder condition.

(defun q530152-derivative-remainder
    (real space field curve time other-time)
  (q530152-v-sub
   space
   (q530152-v-sub
    space
    (q530152-curve-value curve other-time)
    (q530152-curve-value curve time))
   (q530152-v-smul
    real space
    (q530152-r-sub real other-time time)
    (q530152-field-value
     field time
     (q530152-curve-value curve time)))))

(defun-sk q530152-derivative-neighborhood-p
    (real space field curve tmin tmax time epsilon delta)
  (forall (other-time)
    (implies
     (and
      (q530152-in-interval-p
       real tmin tmax other-time)
      (q530152-r-lt
       real
       (q530152-r-abs
        real
        (q530152-r-sub real other-time time))
       delta))
     (q530152-r-le
      real
      (q530152-v-norm
       real space
       (q530152-derivative-remainder
        real space field curve time other-time))
      (q530152-r-mul
       real
       epsilon
       (q530152-r-abs
        real
        (q530152-r-sub real other-time time)))))))

(defun-sk q530152-derivative-radius-exists-p
    (real space field curve tmin tmax time epsilon)
  (exists (delta)
    (and
     (q530152-positive-real-p real delta)
     (q530152-derivative-neighborhood-p
      real space field curve tmin tmax time epsilon delta))))

(defun-sk q530152-has-deriv-within-at-p
    (real space field curve tmin tmax time)
  (forall (epsilon)
    (implies
     (q530152-positive-real-p real epsilon)
     (q530152-derivative-radius-exists-p
      real space field curve tmin tmax time epsilon))))

(defun-sk q530152-curve-solves-on-interval-p
    (real space field curve tmin tmax)
  (forall (time)
    (implies
     (q530152-in-interval-p
      real tmin tmax time)
     (q530152-has-deriv-within-at-p
      real space field curve tmin tmax time))))

(defun q530152-solution-p
    (real space field tmin tmax initial point curve)
  (and
   (q530152-curve-p real space curve)
   (equal
    (q530152-curve-value curve initial)
    point)
   (q530152-curve-solves-on-interval-p
    real space field curve tmin tmax)))

(defun-sk q530152-solution-exists-p
    (real space field tmin tmax initial point)
  (exists (curve)
    (q530152-solution-p
     real space field tmin tmax initial point curve)))

(defun thousand-theorems-q530152-picard-lindelof-theorem-statement
    (real space field tmin tmax initial center point
          outer-radius initial-radius norm-bound
          lipschitz-constant)
  (implies
   (and
    (q530152-real-structure-p real)
    (q530152-real-banach-space-p real space)
    (q530152-vector-field-p real space field)
    (q530152-real-p real tmin)
    (q530152-real-p real tmax)
    (q530152-in-interval-p
     real tmin tmax initial)
    (q530152-vector-p space center)
    (q530152-vector-p space point)
    (q530152-nonnegative-real-p real outer-radius)
    (q530152-nonnegative-real-p real initial-radius)
    (q530152-nonnegative-real-p real norm-bound)
    (q530152-nonnegative-real-p
     real lipschitz-constant)
    (q530152-is-picard-lindelof-p
     real space field tmin tmax initial center
     outer-radius initial-radius norm-bound
     lipschitz-constant)
    (q530152-in-closed-ball-p
     real space center initial-radius point))
   (q530152-solution-exists-p
    real space field tmin tmax initial point)))

(value-triple :itpeval-statement-checked)
:q
