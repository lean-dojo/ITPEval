;; Statement-only formalization of thousand-theorems corpus artifact Q318767,
;; "Abel's theorem": convergence of a real or complex coefficient series at
;; one implies convergence of its power-series sum to the same value from the
;; real left or within any positive-slope complex Stolz cone. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; A Dedekind-complete ordered field presents the real numbers up to the
;; unique ordered-field isomorphism. Complex numbers below are definitionally
;; pairs of real elements with the standard operations. Arbitrary coefficient
;; sequences and arbitrary subsets used by completeness are interpreted by
;; conservative interfaces; every required field, order, completeness, and
;; typing law is explicit in the statement predicates.

(defstub q318767-member-p (type object) t)
(defstub q318767-zero (type) t)
(defstub q318767-one (type) t)
(defstub q318767-add (type left right) t)
(defstub q318767-multiply (type left right) t)
(defstub q318767-negate (type object) t)
(defstub q318767-inverse (type object) t)
(defstub q318767-less (type left right) t)
(defstub q318767-set-member-p (set object) t)
(defstub q318767-sequence-at (sequence index) t)

(defun q318767-real-subtract (real-type x y)
  (q318767-add
   real-type x (q318767-negate real-type y)))

(defun q318767-real-positive-p (real-type x)
  (and
   (q318767-member-p real-type x)
   (q318767-less
    real-type (q318767-zero real-type) x)))

(defun q318767-real-leq-p (real-type x y)
  (and
   (q318767-member-p real-type x)
   (q318767-member-p real-type y)
   (not (q318767-less real-type y x))))

(defun q318767-real-absolute (real-type x)
  (if (q318767-less
       real-type x (q318767-zero real-type))
      (q318767-negate real-type x)
    x))

(defun q318767-real-square (real-type x)
  (q318767-multiply real-type x x))

(defun-sk q318767-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q318767-member-p real-type x)
      (q318767-member-p real-type y)
      (q318767-member-p real-type z))
     (and
      (q318767-member-p
       real-type (q318767-add real-type x y))
      (q318767-member-p
       real-type (q318767-multiply real-type x y))
      (q318767-member-p
       real-type (q318767-negate real-type x))
      (implies
       (not (equal x (q318767-zero real-type)))
       (q318767-member-p
        real-type (q318767-inverse real-type x)))
      (equal
       (q318767-add
        real-type (q318767-add real-type x y) z)
       (q318767-add
        real-type x (q318767-add real-type y z)))
      (equal
       (q318767-add real-type x y)
       (q318767-add real-type y x))
      (equal
       (q318767-add
        real-type x (q318767-zero real-type))
       x)
      (equal
       (q318767-add
        real-type x (q318767-negate real-type x))
       (q318767-zero real-type))
      (equal
       (q318767-multiply
        real-type (q318767-multiply real-type x y) z)
       (q318767-multiply
        real-type x (q318767-multiply real-type y z)))
      (equal
       (q318767-multiply real-type x y)
       (q318767-multiply real-type y x))
      (equal
       (q318767-multiply
        real-type x (q318767-one real-type))
       x)
      (implies
       (equal x (q318767-zero real-type))
       (equal
        (q318767-inverse real-type x)
        (q318767-zero real-type)))
      (implies
       (not (equal x (q318767-zero real-type)))
       (equal
        (q318767-multiply
         real-type x (q318767-inverse real-type x))
        (q318767-one real-type)))
      (equal
       (q318767-multiply
        real-type x (q318767-add real-type y z))
       (q318767-add
        real-type
        (q318767-multiply real-type x y)
        (q318767-multiply real-type x z)))))))

(defun-sk q318767-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q318767-member-p real-type x)
      (q318767-member-p real-type y)
      (q318767-member-p real-type z))
     (and
      (not (q318767-less real-type x x))
      (or
       (q318767-less real-type x y)
       (equal x y)
       (q318767-less real-type y x))
      (implies
       (and
        (q318767-less real-type x y)
        (q318767-less real-type y z))
       (q318767-less real-type x z))
      (implies
       (q318767-less real-type x y)
       (q318767-less
        real-type
        (q318767-add real-type x z)
        (q318767-add real-type y z)))
      (implies
       (and
        (q318767-less
         real-type (q318767-zero real-type) x)
        (q318767-less
         real-type (q318767-zero real-type) y))
       (q318767-less
        real-type
        (q318767-zero real-type)
        (q318767-multiply real-type x y)))))))

(defun-sk q318767-valid-real-set-p (real-type set)
  (forall (x)
    (implies
     (q318767-set-member-p set x)
     (q318767-member-p real-type x))))

(defun-sk q318767-real-set-nonempty-p
    (real-type set)
  (exists (x)
    (and
     (q318767-member-p real-type x)
     (q318767-set-member-p set x))))

(defun-sk q318767-real-upper-bound-p
    (real-type set bound)
  (forall (x)
    (implies
     (and
      (q318767-member-p real-type x)
      (q318767-set-member-p set x))
     (q318767-real-leq-p real-type x bound))))

(defun-sk q318767-real-set-bounded-above-p
    (real-type set)
  (exists (bound)
    (and
     (q318767-member-p real-type bound)
     (q318767-real-upper-bound-p
      real-type set bound))))

(defun-sk q318767-real-least-upper-bound-p
    (real-type set supremum)
  (forall (bound)
    (implies
     (and
      (q318767-member-p real-type bound)
      (q318767-real-upper-bound-p
       real-type set bound))
     (q318767-real-leq-p
      real-type supremum bound))))

(defun q318767-real-supremum-p
    (real-type set supremum)
  (and
   (q318767-member-p real-type supremum)
   (q318767-real-upper-bound-p
    real-type set supremum)
   (q318767-real-least-upper-bound-p
    real-type set supremum)))

(defun-sk q318767-real-set-has-supremum-p
    (real-type set)
  (exists (supremum)
    (q318767-real-supremum-p
     real-type set supremum)))

(defun-sk q318767-dedekind-complete-p (real-type)
  (forall (set)
    (implies
     (and
      (q318767-valid-real-set-p real-type set)
      (q318767-real-set-nonempty-p real-type set)
      (q318767-real-set-bounded-above-p
       real-type set))
     (q318767-real-set-has-supremum-p
      real-type set))))

(defun q318767-real-model-p (real-type)
  (and
   (q318767-member-p
    real-type (q318767-zero real-type))
   (q318767-member-p
    real-type (q318767-one real-type))
   (not
    (equal
     (q318767-zero real-type)
     (q318767-one real-type)))
   (q318767-field-laws-p real-type)
   (q318767-order-laws-p real-type)
   (q318767-less
    real-type
    (q318767-zero real-type)
    (q318767-one real-type))
   (q318767-dedekind-complete-p real-type)))

;; Complex numbers are ordered pairs (real-part . imaginary-part).

(defun q318767-complex-p (real-type z)
  (and
   (consp z)
   (q318767-member-p real-type (car z))
   (q318767-member-p real-type (cdr z))))

(defun q318767-complex-zero (real-type)
  (cons
   (q318767-zero real-type)
   (q318767-zero real-type)))

(defun q318767-complex-one (real-type)
  (cons
   (q318767-one real-type)
   (q318767-zero real-type)))

(defun q318767-complex-add (real-type z w)
  (cons
   (q318767-add real-type (car z) (car w))
   (q318767-add real-type (cdr z) (cdr w))))

(defun q318767-complex-negate (real-type z)
  (cons
   (q318767-negate real-type (car z))
   (q318767-negate real-type (cdr z))))

(defun q318767-complex-subtract (real-type z w)
  (q318767-complex-add
   real-type z (q318767-complex-negate real-type w)))

(defun q318767-complex-multiply (real-type z w)
  (cons
   (q318767-real-subtract
    real-type
    (q318767-multiply real-type (car z) (car w))
    (q318767-multiply real-type (cdr z) (cdr w)))
   (q318767-add
    real-type
    (q318767-multiply real-type (car z) (cdr w))
    (q318767-multiply real-type (cdr z) (car w)))))

(defun q318767-complex-norm-square (real-type z)
  (q318767-add
   real-type
   (q318767-real-square real-type (car z))
   (q318767-real-square real-type (cdr z))))

(defun q318767-complex-distance-less-p
    (real-type z w epsilon)
  (and
   (q318767-complex-p real-type z)
   (q318767-complex-p real-type w)
   (q318767-real-positive-p real-type epsilon)
   (q318767-less
    real-type
    (q318767-complex-norm-square
     real-type
     (q318767-complex-subtract real-type z w))
    (q318767-real-square real-type epsilon))))

(defun q318767-complex-power
    (real-type z exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (q318767-complex-one real-type)
    (q318767-complex-multiply
     real-type
     z
     (q318767-complex-power
      real-type z (1- exponent)))))

(defun q318767-real-power
    (real-type x exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (q318767-one real-type)
    (q318767-multiply
     real-type
     x
     (q318767-real-power
      real-type x (1- exponent)))))

(defun-sk q318767-real-sequence-p
    (real-type sequence)
  (forall (n)
    (implies
     (natp n)
     (q318767-member-p
      real-type
      (q318767-sequence-at sequence n)))))

(defun-sk q318767-complex-sequence-p
    (real-type sequence)
  (forall (n)
    (implies
     (natp n)
     (q318767-complex-p
      real-type
      (q318767-sequence-at sequence n)))))

;; Prefix sums use exactly the indices 0,...,count-1.

(defun q318767-real-coefficient-prefix
    (real-type sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q318767-zero real-type)
    (let ((index (1- count)))
      (q318767-add
       real-type
       (q318767-real-coefficient-prefix
        real-type sequence index)
       (q318767-sequence-at sequence index)))))

(defun q318767-complex-coefficient-prefix
    (real-type sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q318767-complex-zero real-type)
    (let ((index (1- count)))
      (q318767-complex-add
       real-type
       (q318767-complex-coefficient-prefix
        real-type sequence index)
       (q318767-sequence-at sequence index)))))

(defun q318767-real-series-prefix
    (real-type sequence x count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q318767-zero real-type)
    (let ((index (1- count)))
      (q318767-add
       real-type
       (q318767-real-series-prefix
        real-type sequence x index)
       (q318767-multiply
        real-type
        (q318767-sequence-at sequence index)
        (q318767-real-power
         real-type x index))))))

(defun q318767-complex-series-prefix
    (real-type sequence z count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q318767-complex-zero real-type)
    (let ((index (1- count)))
      (q318767-complex-add
       real-type
       (q318767-complex-series-prefix
        real-type sequence z index)
       (q318767-complex-multiply
        real-type
        (q318767-sequence-at sequence index)
        (q318767-complex-power
         real-type z index))))))

;; Metric convergence of coefficient partial sums at the natural-number
;; filter ATTOP.

(defun-sk q318767-real-coefficient-tail-p
    (real-type sequence limit epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (natp cutoff)
      (<= cutoff count))
     (q318767-less
      real-type
      (q318767-real-absolute
       real-type
       (q318767-real-subtract
        real-type
        (q318767-real-coefficient-prefix
         real-type sequence count)
        limit))
      epsilon))))

(defun-sk q318767-real-coefficient-cutoff-p
    (real-type sequence limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q318767-real-coefficient-tail-p
      real-type sequence limit epsilon cutoff))))

(defun-sk q318767-real-coefficients-converge-p
    (real-type sequence limit)
  (forall (epsilon)
    (implies
     (q318767-real-positive-p real-type epsilon)
     (q318767-real-coefficient-cutoff-p
      real-type sequence limit epsilon))))

(defun-sk q318767-complex-coefficient-tail-p
    (real-type sequence limit epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (natp cutoff)
      (<= cutoff count))
     (q318767-complex-distance-less-p
      real-type
      (q318767-complex-coefficient-prefix
       real-type sequence count)
      limit
      epsilon))))

(defun-sk q318767-complex-coefficient-cutoff-p
    (real-type sequence limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q318767-complex-coefficient-tail-p
      real-type sequence limit epsilon cutoff))))

(defun-sk q318767-complex-coefficients-converge-p
    (real-type sequence limit)
  (forall (epsilon)
    (implies
     (q318767-real-positive-p real-type epsilon)
     (q318767-complex-coefficient-cutoff-p
      real-type sequence limit epsilon))))

;; Exact convergence and totalized TSUM for the power series at a point.

(defun-sk q318767-real-series-tail-p
    (real-type sequence x limit epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (natp cutoff)
      (<= cutoff count))
     (q318767-less
      real-type
      (q318767-real-absolute
       real-type
       (q318767-real-subtract
        real-type
        (q318767-real-series-prefix
         real-type sequence x count)
        limit))
      epsilon))))

(defun-sk q318767-real-series-cutoff-p
    (real-type sequence x limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q318767-real-series-tail-p
      real-type sequence x limit epsilon cutoff))))

(defun-sk q318767-real-series-sums-to-p
    (real-type sequence x limit)
  (forall (epsilon)
    (implies
     (q318767-real-positive-p real-type epsilon)
     (q318767-real-series-cutoff-p
      real-type sequence x limit epsilon))))

(defun-sk q318767-real-series-summable-p
    (real-type sequence x)
  (exists (limit)
    (and
     (q318767-member-p real-type limit)
     (q318767-real-series-sums-to-p
      real-type sequence x limit))))

(defun q318767-real-tsum-p
    (real-type sequence x value)
  (and
   (q318767-member-p real-type value)
   (if (q318767-real-series-summable-p
        real-type sequence x)
       (q318767-real-series-sums-to-p
        real-type sequence x value)
     (equal value (q318767-zero real-type)))))

(defchoose q318767-real-tsum-value (value)
  (real-type sequence x)
  (q318767-real-tsum-p
   real-type sequence x value))

(defun-sk q318767-complex-series-tail-p
    (real-type sequence z limit epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (natp cutoff)
      (<= cutoff count))
     (q318767-complex-distance-less-p
      real-type
      (q318767-complex-series-prefix
       real-type sequence z count)
      limit
      epsilon))))

(defun-sk q318767-complex-series-cutoff-p
    (real-type sequence z limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q318767-complex-series-tail-p
      real-type sequence z limit epsilon cutoff))))

(defun-sk q318767-complex-series-sums-to-p
    (real-type sequence z limit)
  (forall (epsilon)
    (implies
     (q318767-real-positive-p real-type epsilon)
     (q318767-complex-series-cutoff-p
      real-type sequence z limit epsilon))))

(defun-sk q318767-complex-series-summable-p
    (real-type sequence z)
  (exists (limit)
    (and
     (q318767-complex-p real-type limit)
     (q318767-complex-series-sums-to-p
      real-type sequence z limit))))

(defun q318767-complex-tsum-p
    (real-type sequence z value)
  (and
   (q318767-complex-p real-type value)
   (if (q318767-complex-series-summable-p
        real-type sequence z)
       (q318767-complex-series-sums-to-p
        real-type sequence z value)
     (equal
      value (q318767-complex-zero real-type)))))

(defchoose q318767-complex-tsum-value (value)
  (real-type sequence z)
  (q318767-complex-tsum-p
   real-type sequence z value))

;; The complex source set is exactly
;;   |Im z| < slope * (1 - Re z).

(defun q318767-stolz-cone-p
    (real-type slope z)
  (and
   (q318767-complex-p real-type z)
   (q318767-less
    real-type
    (q318767-real-absolute real-type (cdr z))
    (q318767-multiply
     real-type
     slope
     (q318767-real-subtract
      real-type
      (q318767-one real-type)
      (car z))))))

(defun-sk q318767-complex-abel-delta-p
    (real-type sequence limit slope epsilon delta)
  (forall (z)
    (implies
     (and
      (q318767-stolz-cone-p real-type slope z)
      (q318767-complex-distance-less-p
       real-type
       z
       (q318767-complex-one real-type)
       delta))
     (q318767-complex-distance-less-p
      real-type
      (q318767-complex-tsum-value
       real-type sequence z)
      limit
      epsilon))))

(defun-sk q318767-complex-abel-delta-exists-p
    (real-type sequence limit slope epsilon)
  (exists (delta)
    (and
     (q318767-real-positive-p real-type delta)
     (q318767-complex-abel-delta-p
      real-type sequence limit slope epsilon delta))))

(defun-sk q318767-complex-abel-conclusion-p
    (real-type sequence limit slope)
  (forall (epsilon)
    (implies
     (q318767-real-positive-p real-type epsilon)
     (q318767-complex-abel-delta-exists-p
      real-type sequence limit slope epsilon))))

;; The real source filter is the neighborhood of one restricted to x < 1.

(defun-sk q318767-real-abel-delta-p
    (real-type sequence limit epsilon delta)
  (forall (x)
    (implies
     (and
      (q318767-member-p real-type x)
      (q318767-less
       real-type x (q318767-one real-type))
      (q318767-less
       real-type
       (q318767-real-absolute
        real-type
        (q318767-real-subtract
         real-type x (q318767-one real-type)))
       delta))
     (q318767-less
      real-type
      (q318767-real-absolute
       real-type
       (q318767-real-subtract
        real-type
        (q318767-real-tsum-value
         real-type sequence x)
        limit))
      epsilon))))

(defun-sk q318767-real-abel-delta-exists-p
    (real-type sequence limit epsilon)
  (exists (delta)
    (and
     (q318767-real-positive-p real-type delta)
     (q318767-real-abel-delta-p
      real-type sequence limit epsilon delta))))

(defun-sk q318767-real-abel-conclusion-p
    (real-type sequence limit)
  (forall (epsilon)
    (implies
     (q318767-real-positive-p real-type epsilon)
     (q318767-real-abel-delta-exists-p
      real-type sequence limit epsilon))))

(defun thousand-theorems-q318767-abel-s-theorem-statement
    (real-type
     complex-coefficients complex-limit cone-slope
     real-coefficients real-limit)
  (implies
   (q318767-real-model-p real-type)
   (and
    (implies
     (and
      (q318767-complex-sequence-p
       real-type complex-coefficients)
      (q318767-complex-p real-type complex-limit)
      (q318767-real-positive-p
       real-type cone-slope)
      (q318767-complex-coefficients-converge-p
       real-type complex-coefficients complex-limit))
     (q318767-complex-abel-conclusion-p
      real-type complex-coefficients
      complex-limit cone-slope))
    (implies
     (and
      (q318767-real-sequence-p
       real-type real-coefficients)
      (q318767-member-p real-type real-limit)
      (q318767-real-coefficients-converge-p
       real-type real-coefficients real-limit))
     (q318767-real-abel-conclusion-p
      real-type real-coefficients real-limit)))))

(value-triple :itpeval-statement-checked)
:q
