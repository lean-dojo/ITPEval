;; Statement-only formalization of PutnamBench corpus artifact putnam_1987_a6:
;; the positive real numbers for which the series x^(a(n))/n^3 converges,
;; where a(n) counts zeroes in the base-3 digits of n, are exactly 0 < x < 25.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no primitive carrier containing every real number. Following the
;; repository's statement-only convention for real analysis, the conservative
;; interfaces below describe an arbitrary Dedekind-complete Archimedean ordered
;; field, hence the real field up to ordered-field isomorphism. All carrier,
;; algebraic, order, completeness, and convergence conditions are explicit;
;; no real is replaced by a rational or by a finite table.

(defstub putnam-1987-a6-real-p (real-type value) t)
(defstub putnam-1987-a6-zero (real-type) t)
(defstub putnam-1987-a6-one (real-type) t)
(defstub putnam-1987-a6-add (real-type left right) t)
(defstub putnam-1987-a6-mul (real-type left right) t)
(defstub putnam-1987-a6-neg (real-type value) t)
(defstub putnam-1987-a6-inv (real-type value) t)
(defstub putnam-1987-a6-less (real-type left right) t)
(defstub putnam-1987-a6-supremum (real-type set) t)

(defun putnam-1987-a6-leq (real-type left right)
  (not (putnam-1987-a6-less real-type right left)))

(defun putnam-1987-a6-sub (real-type left right)
  (putnam-1987-a6-add
   real-type
   left
   (putnam-1987-a6-neg real-type right)))

(defun putnam-1987-a6-div (real-type numerator denominator)
  (putnam-1987-a6-mul
   real-type
   numerator
   (putnam-1987-a6-inv real-type denominator)))

(defun putnam-1987-a6-abs (real-type value)
  (if (putnam-1987-a6-less
       real-type value (putnam-1987-a6-zero real-type))
      (putnam-1987-a6-neg real-type value)
    value))

(defun putnam-1987-a6-positive-p (real-type value)
  (and
   (putnam-1987-a6-real-p real-type value)
   (putnam-1987-a6-less
    real-type (putnam-1987-a6-zero real-type) value)))

(defun putnam-1987-a6-real-set-member-p (set value)
  (if (apply$ set (list value)) t nil))

(defun-sk putnam-1987-a6-valid-real-set-p (real-type set)
  (forall (value)
    (implies
     (putnam-1987-a6-real-set-member-p set value)
     (putnam-1987-a6-real-p real-type value))))

;; Complete ordered-field structure.

(defun-sk putnam-1987-a6-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1987-a6-real-p real-type x)
      (putnam-1987-a6-real-p real-type y)
      (putnam-1987-a6-real-p real-type z))
     (let* ((zero (putnam-1987-a6-zero real-type))
            (one (putnam-1987-a6-one real-type))
            (xy-add (putnam-1987-a6-add real-type x y))
            (yz-add (putnam-1987-a6-add real-type y z))
            (xy-mul (putnam-1987-a6-mul real-type x y))
            (yz-mul (putnam-1987-a6-mul real-type y z))
            (neg-x (putnam-1987-a6-neg real-type x))
            (inv-x (putnam-1987-a6-inv real-type x)))
       (and
        (putnam-1987-a6-real-p real-type xy-add)
        (putnam-1987-a6-real-p real-type xy-mul)
        (putnam-1987-a6-real-p real-type neg-x)
        (putnam-1987-a6-real-p real-type inv-x)
        (equal
         (putnam-1987-a6-add real-type xy-add z)
         (putnam-1987-a6-add real-type x yz-add))
        (equal xy-add (putnam-1987-a6-add real-type y x))
        (equal (putnam-1987-a6-add real-type x zero) x)
        (equal (putnam-1987-a6-add real-type x neg-x) zero)
        (equal
         (putnam-1987-a6-mul real-type xy-mul z)
         (putnam-1987-a6-mul real-type x yz-mul))
        (equal xy-mul (putnam-1987-a6-mul real-type y x))
        (equal (putnam-1987-a6-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1987-a6-mul real-type x inv-x)
          one))
        (equal
         (putnam-1987-a6-mul real-type x yz-add)
         (putnam-1987-a6-add
          real-type
          (putnam-1987-a6-mul real-type x y)
          (putnam-1987-a6-mul real-type x z))))))))

(defun-sk putnam-1987-a6-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1987-a6-real-p real-type x)
      (putnam-1987-a6-real-p real-type y)
      (putnam-1987-a6-real-p real-type z))
     (let ((zero (putnam-1987-a6-zero real-type)))
       (and
        (not (putnam-1987-a6-less real-type x x))
        (or
         (putnam-1987-a6-less real-type x y)
         (equal x y)
         (putnam-1987-a6-less real-type y x))
        (implies
         (and
          (putnam-1987-a6-less real-type x y)
          (putnam-1987-a6-less real-type y z))
         (putnam-1987-a6-less real-type x z))
        (implies
         (putnam-1987-a6-less real-type x y)
         (putnam-1987-a6-less
          real-type
          (putnam-1987-a6-add real-type x z)
          (putnam-1987-a6-add real-type y z)))
        (implies
         (and
          (putnam-1987-a6-less real-type zero x)
          (putnam-1987-a6-less real-type zero y))
         (putnam-1987-a6-less
          real-type
          zero
          (putnam-1987-a6-mul real-type x y))))))))

(defun-sk putnam-1987-a6-upper-bound-p
    (real-type set upper)
  (forall (x)
    (implies
     (and
      (putnam-1987-a6-real-p real-type x)
      (putnam-1987-a6-real-set-member-p set x))
     (putnam-1987-a6-leq real-type x upper))))

(defun-sk putnam-1987-a6-real-set-nonempty-p
    (real-type set)
  (exists (x)
    (and
     (putnam-1987-a6-real-p real-type x)
     (putnam-1987-a6-real-set-member-p set x))))

(defun-sk putnam-1987-a6-real-set-bounded-p
    (real-type set)
  (exists (upper)
    (and
     (putnam-1987-a6-real-p real-type upper)
     (putnam-1987-a6-upper-bound-p
      real-type set upper))))

(defun-sk putnam-1987-a6-least-upper-bound-p
    (real-type set supremum)
  (forall (upper)
    (implies
     (and
      (putnam-1987-a6-real-p real-type upper)
      (putnam-1987-a6-upper-bound-p
       real-type set upper))
     (putnam-1987-a6-leq
      real-type supremum upper))))

(defun-sk putnam-1987-a6-completeness-p (real-type)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1987-a6-valid-real-set-p real-type set)
      (putnam-1987-a6-real-set-nonempty-p real-type set)
      (putnam-1987-a6-real-set-bounded-p real-type set))
     (let ((supremum
            (putnam-1987-a6-supremum real-type set)))
       (and
        (putnam-1987-a6-real-p real-type supremum)
        (putnam-1987-a6-upper-bound-p
         real-type set supremum)
        (putnam-1987-a6-least-upper-bound-p
         real-type set supremum))))))

(defun putnam-1987-a6-r-nat (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-1987-a6-zero real-type)
    (putnam-1987-a6-add
     real-type
     (putnam-1987-a6-one real-type)
     (putnam-1987-a6-r-nat real-type (1- n)))))

(defun-sk putnam-1987-a6-archimedean-witness-p
    (real-type value)
  (exists (n)
    (and
     (natp n)
     (putnam-1987-a6-less
      real-type
      value
      (putnam-1987-a6-r-nat real-type n)))))

(defun-sk putnam-1987-a6-archimedean-p (real-type)
  (forall (value)
    (implies
     (putnam-1987-a6-real-p real-type value)
     (putnam-1987-a6-archimedean-witness-p
      real-type value))))

(defun putnam-1987-a6-real-field-p (real-type)
  (let ((zero (putnam-1987-a6-zero real-type))
        (one (putnam-1987-a6-one real-type)))
    (and
     (putnam-1987-a6-real-p real-type zero)
     (putnam-1987-a6-real-p real-type one)
     (not (equal zero one))
     (putnam-1987-a6-field-laws-p real-type)
     (putnam-1987-a6-order-laws-p real-type)
     (putnam-1987-a6-less real-type zero one)
     (putnam-1987-a6-completeness-p real-type)
     (putnam-1987-a6-archimedean-p real-type))))

;; Exact base-3 zero count. The fuel is internal and exceeds the number of
;; recursive base-3 divisions for every natural input.

(defun putnam-1987-a6-zero-digits-aux (n fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond
   ((or (not (natp n))
        (zp fuel))
    0)
   ((< n 3)
    (if (equal n 0) 1 0))
   (t
    (+ (if (equal (mod n 3) 0) 1 0)
       (putnam-1987-a6-zero-digits-aux
        (floor n 3)
        (1- fuel))))))

(defun putnam-1987-a6-zero-digits (n)
  (if (natp n)
      (putnam-1987-a6-zero-digits-aux n (+ n 1))
    0))

(defun putnam-1987-a6-r-power
    (real-type base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (putnam-1987-a6-one real-type)
    (putnam-1987-a6-mul
     real-type
     base
     (putnam-1987-a6-r-power
      real-type base (1- exponent)))))

(defun putnam-1987-a6-term (real-type x n)
  (if (natp n)
      (putnam-1987-a6-div
       real-type
       (putnam-1987-a6-r-power
        real-type
        x
        (putnam-1987-a6-zero-digits n))
       (putnam-1987-a6-r-power
        real-type
        (putnam-1987-a6-r-nat real-type n)
        3))
    (putnam-1987-a6-zero real-type)))

;; Sum over 0 <= n < TERMS. At n = 0 the field inverse of zero is zero,
;; matching the totalized division used by the Lean and Isabelle statements;
;; consequently this is the same series as the published sum from n = 1.

(defun putnam-1987-a6-prefix-sum
    (real-type x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (putnam-1987-a6-zero real-type)
    (let ((index (1- terms)))
      (putnam-1987-a6-add
       real-type
       (putnam-1987-a6-prefix-sum
        real-type x index)
       (putnam-1987-a6-term
        real-type x index)))))

;; Literal epsilon-N convergence of the partial sums to an internally
;; existentially quantified real limit.

(defun-sk putnam-1987-a6-limit-tail-p
    (real-type x limit epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (putnam-1987-a6-less
      real-type
      (putnam-1987-a6-abs
       real-type
       (putnam-1987-a6-sub
        real-type
        (putnam-1987-a6-prefix-sum
         real-type x terms)
        limit))
      epsilon))))

(defun-sk putnam-1987-a6-limit-cutoff-p
    (real-type x limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1987-a6-limit-tail-p
      real-type x limit epsilon cutoff))))

(defun-sk putnam-1987-a6-converges-to-p
    (real-type x limit)
  (forall (epsilon)
    (implies
     (putnam-1987-a6-positive-p real-type epsilon)
     (putnam-1987-a6-limit-cutoff-p
      real-type x limit epsilon))))

(defun-sk putnam-1987-a6-summable-p (real-type x)
  (exists (limit)
    (and
     (putnam-1987-a6-real-p real-type limit)
     (putnam-1987-a6-converges-to-p
      real-type x limit))))

;; Equality of the two source sets is expressed extensionally, without taking
;; 0 < x < 25 as an assumption: every real x is in the positive convergence
;; set if and only if it lies in the open interval (0,25).

(defun-sk putnam-1987-a6-classification-p (real-type)
  (forall (x)
    (implies
     (putnam-1987-a6-real-p real-type x)
     (iff
      (and
       (putnam-1987-a6-positive-p real-type x)
       (putnam-1987-a6-summable-p real-type x))
      (and
       (putnam-1987-a6-positive-p real-type x)
       (putnam-1987-a6-less
        real-type
        x
        (putnam-1987-a6-r-nat real-type 25)))))))

(defun putnambench-putnam-1987-a6-statement (real-type)
  (implies
   (putnam-1987-a6-real-field-p real-type)
   (putnam-1987-a6-classification-p real-type)))

(value-triple :itpeval-statement-checked)
:q
