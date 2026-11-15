;; Statement-only formalization of thousand-theorems corpus artifact Q1186808,
;; "Lucas's theorem": for a prime p and natural n and k below p^a, choose(n,k)
;; is congruent modulo p to the product of the binomial coefficients of their
;; corresponding base-p digits through position a - 1. This file contains no
;; proof.

(in-package "ACL2")

(defun q1186808-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (q1186808-binomial-coefficient (- n 1) k)
       (q1186808-binomial-coefficient (- n 1) (- k 1)))))

(defun q1186808-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and
       (not (equal (mod number divisor) 0))
       (q1186808-no-divisor-from-p number (+ divisor 1)))
    t))

(defun q1186808-primep (number)
  (and (natp number)
       (< 1 number)
       (q1186808-no-divisor-from-p number 2)))

(defun q1186808-digit-binomial-product (n k p a)
  (declare (xargs :measure (nfix a)))
  (if (zp a)
      1
    (let* ((i (- a 1))
           (p-to-i (expt p i))
           (n-digit (mod (floor n p-to-i) p))
           (k-digit (mod (floor k p-to-i) p)))
      (* (q1186808-binomial-coefficient n-digit k-digit)
         (q1186808-digit-binomial-product n k p i)))))

(defun thousand-theorems-q1186808-lucas-theorem-statement (n k p a)
  (implies
   (and (natp n)
        (natp k)
        (natp p)
        (natp a)
        (q1186808-primep p)
        (< n (expt p a))
        (< k (expt p a)))
   (equal
    (mod (q1186808-binomial-coefficient n k) p)
    (mod (q1186808-digit-binomial-product n k p a) p))))

(value-triple :itpeval-statement-checked)
:q
