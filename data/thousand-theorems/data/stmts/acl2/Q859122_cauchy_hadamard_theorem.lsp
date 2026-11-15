;; Statement-only formalization of thousand-theorems corpus artifact Q859122,
;; "Cauchy–Hadamard theorem": the inverse bounded-growth radius of the
;; coefficient norms of a formal multilinear series equals the extended-real
;; limsup of their nth roots. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source theorem observes a formal multilinear series only through the
;; nonnegative real sequence n |-> ||p_n||.  This file uses that norm profile
;; as the series representation.  The representation is bidirectionally
;; faithful: every source series supplies such a profile, and every
;; nonnegative real sequence (a_n) is realized over R by the scalar
;; n-multilinear maps (x_1,...,x_n) |-> a_n * product_i x_i (with the
;; corresponding constant map at n = 0).
;;
;; Ordinary ACL2 has no primitive real or extended-nonnegative-real sorts.
;; A Dedekind-complete ordered field presents R, arbitrary sequences and sets
;; are APPLY$ function objects, and extended nonnegative reals are represented
;; exactly by either a tagged nonnegative real or a distinguished top value.

(defstub q859122-real-p (real-type value) t)
(defstub q859122-zero (real-type) t)
(defstub q859122-one (real-type) t)
(defstub q859122-add (real-type left right) t)
(defstub q859122-multiply (real-type left right) t)
(defstub q859122-negate (real-type value) t)
(defstub q859122-inverse (real-type value) t)
(defstub q859122-less (real-type left right) t)

(defun q859122-leq (real-type left right)
  (not (q859122-less real-type right left)))

(defun q859122-nonnegative-p (real-type value)
  (and
   (q859122-real-p real-type value)
   (q859122-leq real-type (q859122-zero real-type) value)))

(defun q859122-positive-p (real-type value)
  (and
   (q859122-real-p real-type value)
   (q859122-less real-type (q859122-zero real-type) value)))

(defun q859122-real-power (real-type base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (q859122-one real-type)
    (q859122-multiply
     real-type
     base
     (q859122-real-power real-type base (1- exponent)))))

(defun-sk q859122-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q859122-real-p real-type x)
      (q859122-real-p real-type y)
      (q859122-real-p real-type z))
     (let* ((zero (q859122-zero real-type))
            (one (q859122-one real-type))
            (x-plus-y (q859122-add real-type x y))
            (y-plus-z (q859122-add real-type y z))
            (x-times-y (q859122-multiply real-type x y))
            (y-times-z (q859122-multiply real-type y z))
            (minus-x (q859122-negate real-type x))
            (inverse-x (q859122-inverse real-type x)))
       (and
        (q859122-real-p real-type x-plus-y)
        (q859122-real-p real-type x-times-y)
        (q859122-real-p real-type minus-x)
        (q859122-real-p real-type inverse-x)
        (equal
         (q859122-add real-type x-plus-y z)
         (q859122-add real-type x y-plus-z))
        (equal x-plus-y (q859122-add real-type y x))
        (equal (q859122-add real-type x zero) x)
        (equal (q859122-add real-type x minus-x) zero)
        (equal
         (q859122-multiply real-type x-times-y z)
         (q859122-multiply real-type x y-times-z))
        (equal x-times-y (q859122-multiply real-type y x))
        (equal (q859122-multiply real-type x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (q859122-multiply real-type x inverse-x)
          one))
        (equal
         (q859122-multiply real-type x y-plus-z)
         (q859122-add
          real-type
          (q859122-multiply real-type x y)
          (q859122-multiply real-type x z))))))))

(defun-sk q859122-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q859122-real-p real-type x)
      (q859122-real-p real-type y)
      (q859122-real-p real-type z))
     (let ((zero (q859122-zero real-type)))
       (and
        (not (q859122-less real-type x x))
        (or
         (q859122-less real-type x y)
         (equal x y)
         (q859122-less real-type y x))
        (implies
         (and
          (q859122-less real-type x y)
          (q859122-less real-type y z))
         (q859122-less real-type x z))
        (implies
         (q859122-less real-type x y)
         (q859122-less
          real-type
          (q859122-add real-type x z)
          (q859122-add real-type y z)))
        (implies
         (and
          (q859122-less real-type zero x)
          (q859122-less real-type zero y))
         (q859122-less
          real-type
          zero
          (q859122-multiply real-type x y))))))))

(defun q859122-set-member-p (set value)
  (if (apply$ set (list value)) t nil))

(defun-sk q859122-set-nonempty-p (real-type set)
  (exists (value)
    (and
     (q859122-real-p real-type value)
     (q859122-set-member-p set value))))

(defun-sk q859122-upper-bound-p
    (real-type set bound)
  (forall (value)
    (implies
     (and
      (q859122-real-p real-type value)
      (q859122-set-member-p set value))
     (q859122-leq real-type value bound))))

(defun-sk q859122-bounded-above-p (real-type set)
  (exists (bound)
    (and
     (q859122-real-p real-type bound)
     (q859122-upper-bound-p real-type set bound))))

(defun-sk q859122-supremum-p
    (real-type set supremum)
  (forall (bound)
    (implies
     (and
      (q859122-real-p real-type bound)
      (q859122-upper-bound-p real-type set bound))
     (q859122-leq real-type supremum bound))))

(defun q859122-is-supremum-p
    (real-type set supremum)
  (and
   (q859122-real-p real-type supremum)
   (q859122-upper-bound-p real-type set supremum)
   (q859122-supremum-p real-type set supremum)))

(defun-sk q859122-supremum-exists-p
    (real-type set)
  (exists (supremum)
    (q859122-is-supremum-p real-type set supremum)))

(defun-sk q859122-dedekind-complete-p (real-type)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (q859122-set-nonempty-p real-type set)
      (q859122-bounded-above-p real-type set))
     (q859122-supremum-exists-p real-type set))))

(defun q859122-real-structure-p (real-type)
  (let ((zero (q859122-zero real-type))
        (one (q859122-one real-type)))
    (and
     (q859122-real-p real-type zero)
     (q859122-real-p real-type one)
     (not (equal zero one))
     (q859122-field-laws-p real-type)
     (q859122-order-laws-p real-type)
     (q859122-less real-type zero one)
     (q859122-dedekind-complete-p real-type))))

;; Arbitrary coefficient-norm profiles.

(defun q859122-sequence-value (sequence n)
  (apply$ sequence (list n)))

(defun-sk q859122-nonnegative-sequence-values-p
    (real-type sequence)
  (forall (n)
    (implies
     (natp n)
     (q859122-nonnegative-p
      real-type
      (q859122-sequence-value sequence n)))))

(defun q859122-nonnegative-sequence-p
    (real-type sequence)
  (and
   (tamep-functionp sequence)
   (q859122-nonnegative-sequence-values-p
    real-type sequence)))

;; Extended nonnegative reals.

(defun q859122-top ()
  :q859122-top)

(defun q859122-finite (value)
  (cons :q859122-finite value))

(defun q859122-finite-p (value)
  (and
   (consp value)
   (equal (car value) :q859122-finite)))

(defun q859122-finite-value (value)
  (cdr value))

(defun q859122-ennreal-p (real-type value)
  (or
   (equal value (q859122-top))
   (and
    (q859122-finite-p value)
    (q859122-nonnegative-p
     real-type
     (q859122-finite-value value)))))

(defun q859122-ennreal-less
    (real-type left right)
  (cond
   ((equal right (q859122-top))
    (not (equal left (q859122-top))))
   ((equal left (q859122-top))
    nil)
   (t
    (q859122-less
     real-type
     (q859122-finite-value left)
     (q859122-finite-value right)))))

(defun q859122-ennreal-leq
    (real-type left right)
  (not (q859122-ennreal-less real-type right left)))

(defun q859122-ennreal-inverse
    (real-type value)
  (cond
   ((equal value (q859122-top))
    (q859122-finite (q859122-zero real-type)))
   ((equal
     (q859122-finite-value value)
     (q859122-zero real-type))
    (q859122-top))
   (t
    (q859122-finite
     (q859122-inverse
      real-type
      (q859122-finite-value value))))))

;; The source radius is
;;
;;   sup {r >= 0 | exists C in R, forall n, a_n * r^n <= C},
;;
;; embedded in the extended nonnegative reals.

(defun-sk q859122-growth-bounded-p
    (real-type sequence radius bound)
  (forall (n)
    (implies
     (natp n)
     (q859122-leq
      real-type
      (q859122-multiply
       real-type
       (q859122-sequence-value sequence n)
       (q859122-real-power real-type radius n))
      bound))))

(defun-sk q859122-growth-bound-exists-p
    (real-type sequence radius)
  (exists (bound)
    (and
     (q859122-real-p real-type bound)
     (q859122-growth-bounded-p
      real-type sequence radius bound))))

(defun q859122-admissible-radius-p
    (real-type sequence radius)
  (and
   (q859122-nonnegative-p real-type radius)
   (q859122-growth-bound-exists-p
    real-type sequence radius)))

(defun-sk q859122-radius-upper-bound-p
    (real-type sequence upper)
  (forall (radius)
    (implies
     (q859122-admissible-radius-p
      real-type sequence radius)
     (q859122-ennreal-leq
      real-type
      (q859122-finite radius)
      upper))))

(defun-sk q859122-radius-least-upper-bound-p
    (real-type sequence radius)
  (forall (upper)
    (implies
     (and
      (q859122-ennreal-p real-type upper)
      (q859122-radius-upper-bound-p
       real-type sequence upper))
     (q859122-ennreal-leq
      real-type radius upper))))

(defun q859122-is-radius-p
    (real-type sequence radius)
  (and
   (q859122-ennreal-p real-type radius)
   (q859122-radius-upper-bound-p
    real-type sequence radius)
   (q859122-radius-least-upper-bound-p
    real-type sequence radius)))

;; For n > 0, NNReal.rpow a (1/n) is the unique nonnegative nth root of a.
;; At n = 0, Lean's exponent is 1/0 = 0, so the value is one.

(defun q859122-root-value-p
    (real-type sequence n value)
  (and
   (natp n)
   (q859122-nonnegative-p real-type value)
   (if (zp n)
       (equal value (q859122-one real-type))
     (equal
      (q859122-real-power real-type value n)
      (q859122-sequence-value sequence n)))))

(defun-sk q859122-root-exists-p
    (real-type sequence n)
  (exists (value)
    (q859122-root-value-p
     real-type sequence n value)))

(defun-sk q859122-all-roots-exist-p
    (real-type sequence)
  (forall (n)
    (implies
     (natp n)
     (q859122-root-exists-p
      real-type sequence n))))

(defun-sk q859122-root-above-p
    (real-type sequence n lower)
  (exists (value)
    (and
     (q859122-root-value-p
      real-type sequence n value)
     (q859122-ennreal-less
      real-type lower (q859122-finite value)))))

(defun-sk q859122-root-below-p
    (real-type sequence n upper)
  (exists (value)
    (and
     (q859122-root-value-p
      real-type sequence n value)
     (q859122-ennreal-less
      real-type (q859122-finite value) upper))))

;; These two order conditions characterize the atTop limsup exactly:
;; every value below the limit is exceeded arbitrarily late, and every value
;; above the limit is eventually an upper bound.  They include both finite
;; and +infinity cases without a bounded or finite approximation.

(defun-sk q859122-late-root-exceedance-exists-p
    (real-type sequence lower cutoff)
  (exists (n)
    (and
     (natp n)
     (<= cutoff n)
     (q859122-root-above-p
      real-type sequence n lower))))

(defun-sk q859122-limsup-lower-p
    (real-type sequence limit)
  (forall (lower cutoff)
    (implies
     (and
      (q859122-ennreal-p real-type lower)
      (q859122-ennreal-less real-type lower limit)
      (natp cutoff))
     (q859122-late-root-exceedance-exists-p
      real-type sequence lower cutoff))))

(defun-sk q859122-eventual-root-upper-tail-p
    (real-type sequence upper cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (q859122-root-below-p
      real-type sequence n upper))))

(defun-sk q859122-eventual-root-upper-exists-p
    (real-type sequence upper)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q859122-eventual-root-upper-tail-p
      real-type sequence upper cutoff))))

(defun-sk q859122-limsup-upper-p
    (real-type sequence limit)
  (forall (upper)
    (implies
     (and
      (q859122-ennreal-p real-type upper)
      (q859122-ennreal-less real-type limit upper))
     (q859122-eventual-root-upper-exists-p
      real-type sequence upper))))

(defun q859122-is-root-limsup-p
    (real-type sequence limit)
  (and
   (q859122-ennreal-p real-type limit)
   (q859122-all-roots-exist-p real-type sequence)
   (q859122-limsup-lower-p real-type sequence limit)
   (q859122-limsup-upper-p real-type sequence limit)))

(defun-sk q859122-cauchy-hadamard-value-exists-p
    (real-type sequence)
  (exists (radius)
    (and
     (q859122-is-radius-p real-type sequence radius)
     (q859122-is-root-limsup-p
      real-type
      sequence
      (q859122-ennreal-inverse real-type radius)))))

(defun-sk thousand-theorems-q859122-cauchy-hadamard-statement ()
  (forall (real-type sequence)
    (implies
     (and
      (q859122-real-structure-p real-type)
      (q859122-nonnegative-sequence-p
       real-type sequence))
     (q859122-cauchy-hadamard-value-exists-p
      real-type sequence))))

(value-triple :itpeval-statement-checked)
:q
