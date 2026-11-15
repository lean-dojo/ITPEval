;; Statement-only formalization of PutnamBench corpus artifact putnam_2008_b4:
;; for a prime p and an integer-coefficient polynomial h, pairwise distinct
;; values at 0,...,p^2-1 modulo p^2 imply pairwise distinct values at
;; 0,...,p^3-1 modulo p^3. This file contains no proof.

(in-package "ACL2")

;; Coefficients are stored in ascending degree order. Every integer polynomial
;; has such a finite list representation, and trailing zero coefficients do
;; not affect evaluation.
(defun putnam-2008-b4-integer-listp (coefficients)
  (if (consp coefficients)
      (and
       (integerp (car coefficients))
       (putnam-2008-b4-integer-listp (cdr coefficients)))
    (equal coefficients nil)))

(defun putnam-2008-b4-polynomial-evaluate (coefficients x)
  (if (consp coefficients)
      (+ (car coefficients)
         (* x
            (putnam-2008-b4-polynomial-evaluate
             (cdr coefficients) x)))
    0))

(defun putnam-2008-b4-no-divisor-through-p (p candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod p candidate) 0))
     (putnam-2008-b4-no-divisor-through-p
      p (- candidate 1)))))

(defun putnam-2008-b4-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (putnam-2008-b4-no-divisor-through-p
    p (- p 1))))

;; Equality of remainders modulo the positive modulus is exactly integer
;; congruence. This checks the value at I against the values at
;; 0,...,COUNT-1.
(defun putnam-2008-b4-distinct-from-lower-p
    (coefficients modulus i count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let ((j (- count 1)))
      (and
       (not
        (equal
         (mod
          (putnam-2008-b4-polynomial-evaluate
           coefficients i)
          modulus)
         (mod
          (putnam-2008-b4-polynomial-evaluate
           coefficients j)
          modulus)))
       (putnam-2008-b4-distinct-from-lower-p
        coefficients modulus i j)))))

;; COUNT represents the source range 0,...,COUNT-1. Comparing each final
;; index with every smaller one is equivalent to pairwise injectivity on that
;; range.
(defun putnam-2008-b4-distinct-mod-p
    (coefficients modulus count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let ((i (- count 1)))
      (and
       (putnam-2008-b4-distinct-from-lower-p
        coefficients modulus i i)
       (putnam-2008-b4-distinct-mod-p
        coefficients modulus i)))))

(defun putnambench-putnam-2008-b4-statement
    (p coefficients)
  (implies
   (and
    (putnam-2008-b4-prime-p p)
    (putnam-2008-b4-integer-listp coefficients)
    (putnam-2008-b4-distinct-mod-p
     coefficients (expt p 2) (expt p 2)))
   (putnam-2008-b4-distinct-mod-p
    coefficients (expt p 3) (expt p 3))))

(value-triple :itpeval-statement-checked)
:q
