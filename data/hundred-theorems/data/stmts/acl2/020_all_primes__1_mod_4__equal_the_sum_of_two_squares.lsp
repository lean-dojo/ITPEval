;; Statement-only formalization of hundred-theorems artifact
;; 020_all_primes__1_mod_4__equal_the_sum_of_two_squares, "All Primes (1 mod
;; 4) Equal the Sum of Two Squares": every natural prime congruent to 1 modulo
;; 4 equals x^2 + y^2 for some natural numbers x and y. The bounded searches
;; encode the existential witnesses. This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-020-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (hundred-theorems-020-no-divisor-from-p n (+ d 1)))
    t))

(defun hundred-theorems-020-primep (n)
  (and (natp n)
       (< 1 n)
       (hundred-theorems-020-no-divisor-from-p n 2)))

(defun hundred-theorems-020-square-sum-with-x-through-y-p (p x y)
  (declare (xargs :measure (nfix y)))
  (if (and (natp p)
           (natp x)
           (natp y))
      (or (equal p (+ (* x x) (* y y)))
          (and (not (zp y))
               (hundred-theorems-020-square-sum-with-x-through-y-p
                p x (- y 1))))
    nil))

(defun hundred-theorems-020-square-sum-through-x-p (p x)
  (declare (xargs :measure (nfix x)))
  (if (and (natp p)
           (natp x))
      (or (hundred-theorems-020-square-sum-with-x-through-y-p p x p)
          (and (not (zp x))
               (hundred-theorems-020-square-sum-through-x-p
                p (- x 1))))
    nil))

(defun hundred-theorems-020-sum-of-two-squares-statement (p)
  (implies
   (and (natp p)
        (hundred-theorems-020-primep p)
        (equal (mod p 4) 1))
   (hundred-theorems-020-square-sum-through-x-p p p)))

(value-triple :itpeval-statement-checked)
:q
