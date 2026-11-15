;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__085, "Divisibility by 3 Rule": the base-10 value
;; of any finite integer coefficient sequence has the same residue modulo 3
;; as its coefficient sum, so both are divisible by 3 together; equivalently,
;; a natural number is divisible by 3 exactly when its decimal digit sum is.
;; This file contains no proof.

(in-package "ACL2")

;; COEFFICIENTS is ordered least-significant first.  For every source function
;; d and bound n, the list (d(0), ..., d(n)) gives the same base-10 polynomial
;; and coefficient sum; conversely, every nonempty integer list extends to such
;; a total integer-valued function.  The empty list also represents the decimal
;; digit list of zero.

(defun ht085-integer-listp (coefficients)
  (if (consp coefficients)
      (and (integerp (car coefficients))
           (ht085-integer-listp (cdr coefficients)))
    (equal coefficients nil)))

(defun ht085-coefficient-sum (coefficients)
  (if (consp coefficients)
      (+ (car coefficients)
         (ht085-coefficient-sum (cdr coefficients)))
    0))

(defun ht085-base10-value (coefficients)
  (if (consp coefficients)
      (+ (car coefficients)
         (* 10
            (ht085-base10-value (cdr coefficients))))
    0))

(defun ht085-decimal-digit-sum-aux (fuel n)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel)
          (zp n))
      0
    (+ (mod n 10)
       (ht085-decimal-digit-sum-aux
        (- fuel 1)
        (floor n 10)))))

(defun ht085-decimal-digit-sum (n)
  (if (natp n)
      (ht085-decimal-digit-sum-aux (+ n 1) n)
    0))

(defun ht085-divisible-by-3-p (x)
  (and (integerp x)
       (equal (mod x 3) 0)))

(defun hundred-theorems-085-divisibility-by-3-rule-statement
    (coefficients n)
  (and
   (implies
    (ht085-integer-listp coefficients)
    (let ((value (ht085-base10-value coefficients))
          (sum (ht085-coefficient-sum coefficients)))
      (and
       (equal (mod value 3)
              (mod sum 3))
       (equal (ht085-divisible-by-3-p value)
              (ht085-divisible-by-3-p sum)))))
   (implies
    (natp n)
    (equal
     (ht085-divisible-by-3-p n)
     (ht085-divisible-by-3-p
      (ht085-decimal-digit-sum n))))))

(value-triple :itpeval-statement-checked)
:q
