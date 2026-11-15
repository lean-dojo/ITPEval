;; Statement-only formalization of PutnamBench corpus artifact putnam_1977_a4:
;; for every real x in (0,1), the power-of-two series sums to x/(1-x).
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The series has an explicit limit, so its statement needs field algebra and
;; the Archimedean property, not quantification over every subset of the real
;; line. Conservative generic symbols avoid restricting x to ACL2 rationals.

(defstub p77a4-scalar-p (x) t)
(defstub p77a4-add (x y) t)
(defstub p77a4-multiply (x y) t)
(defstub p77a4-negate (x) t)
(defstub p77a4-inverse (x) t)
(defstub p77a4-less (x y) t)
(defstub p77a4-archimedean-bound (x) t)

(defun p77a4-member-p (x)
  (if (p77a4-scalar-p x) t nil))

(defun p77a4-less-p (x y)
  (if (p77a4-less x y) t nil))

(defun p77a4-subtract (x y)
  (p77a4-add x (p77a4-negate y)))

(defun p77a4-divide (x y)
  (p77a4-multiply x (p77a4-inverse y)))

(defun p77a4-absolute-value (zero x)
  (if (p77a4-less-p x zero)
      (p77a4-negate x)
    x))

(defun p77a4-positive-p (zero x)
  (and
   (p77a4-member-p x)
   (p77a4-less-p zero x)))

(defun-sk p77a4-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p77a4-member-p x)
      (p77a4-member-p y)
      (p77a4-member-p z))
     (and
      (p77a4-member-p (p77a4-add x y))
      (p77a4-member-p (p77a4-multiply x y))
      (p77a4-member-p (p77a4-negate x))
      (p77a4-member-p (p77a4-inverse x))
      (equal
       (p77a4-add (p77a4-add x y) z)
       (p77a4-add x (p77a4-add y z)))
      (equal (p77a4-add x y) (p77a4-add y x))
      (equal (p77a4-add x zero) x)
      (equal (p77a4-add x (p77a4-negate x)) zero)
      (equal
       (p77a4-multiply (p77a4-multiply x y) z)
       (p77a4-multiply x (p77a4-multiply y z)))
      (equal (p77a4-multiply x y) (p77a4-multiply y x))
      (equal (p77a4-multiply x one) x)
      (implies
       (equal x zero)
       (equal (p77a4-inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p77a4-multiply x (p77a4-inverse x))
        one))
      (equal
       (p77a4-multiply x (p77a4-add y z))
       (p77a4-add
        (p77a4-multiply x y)
        (p77a4-multiply x z)))))))

(defun-sk p77a4-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p77a4-member-p x)
      (p77a4-member-p y)
      (p77a4-member-p z))
     (and
      (not (p77a4-less-p x x))
      (or
       (equal x y)
       (p77a4-less-p x y)
       (p77a4-less-p y x))
      (implies
       (and
        (p77a4-less-p x y)
        (p77a4-less-p y z))
       (p77a4-less-p x z))
      (implies
       (p77a4-less-p x y)
       (p77a4-less-p
        (p77a4-add x z)
        (p77a4-add y z)))
      (implies
       (and
        (p77a4-less-p zero x)
        (p77a4-less-p zero y))
       (p77a4-less-p
        zero
        (p77a4-multiply x y)))))))

(defun p77a4-natural-value (zero one n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p77a4-add
     (p77a4-natural-value zero one (- n 1))
     one)))

(defun-sk p77a4-archimedean-law-p (zero one)
  (forall (x)
    (implies
     (p77a4-member-p x)
     (and
      (natp (p77a4-archimedean-bound x))
      (p77a4-less-p
       x
       (p77a4-natural-value
        zero one
        (p77a4-archimedean-bound x)))))))

(defun p77a4-archimedean-ordered-field-p (zero one)
  (and
   (p77a4-member-p zero)
   (p77a4-member-p one)
   (not (equal zero one))
   (p77a4-field-laws-p zero one)
   (p77a4-order-laws-p zero)
   (p77a4-less-p zero one)
   (p77a4-archimedean-law-p zero one)))

(defun p77a4-power (one base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (p77a4-multiply
     base
     (p77a4-power one base (- exponent 1)))))

(defun p77a4-series-term (one x n)
  (let* ((power (expt 2 (nfix n)))
         (numerator (p77a4-power one x power))
         (denominator
          (p77a4-subtract
           one
           (p77a4-power one x (* 2 power)))))
    (p77a4-divide numerator denominator)))

(defun p77a4-series-prefix (zero one x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      zero
    (let ((index (- terms 1)))
      (p77a4-add
       (p77a4-series-prefix zero one x index)
       (p77a4-series-term one x index)))))

(defun p77a4-solution (one x)
  (p77a4-divide
   x
   (p77a4-subtract one x)))

(defun-sk p77a4-series-tail-p
    (zero one x epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (p77a4-less-p
      (p77a4-absolute-value
       zero
       (p77a4-subtract
        (p77a4-series-prefix zero one x terms)
        (p77a4-solution one x)))
      epsilon))))

(defun-sk p77a4-series-cutoff-exists-p
    (zero one x epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p77a4-series-tail-p
      zero one x epsilon cutoff))))

(defun-sk p77a4-series-sums-to-solution-p
    (zero one x)
  (forall (epsilon)
    (implies
     (p77a4-positive-p zero epsilon)
     (p77a4-series-cutoff-exists-p
      zero one x epsilon))))

(defun-sk putnambench-putnam-1977-a4-statement (zero one)
  (forall (x)
    (implies
     (and
      (p77a4-archimedean-ordered-field-p zero one)
      (p77a4-member-p x)
      (p77a4-less-p zero x)
      (p77a4-less-p x one))
     (p77a4-series-sums-to-solution-p
      zero one x))))

(value-triple :itpeval-statement-checked)
:q
