;; Statement-only formalization of PutnamBench corpus artifact putnam_2019_a5:
;; the exact multiplicity of x = 1 in a polynomial over the prime field whose
;; kth coefficient is k^((p-1)/2) is (p-1)/2. This file contains no proof.

(in-package "ACL2")

;; For a natural number, checking every candidate from 2 through number-1 is
;; exactly the usual definition of primality.
(defun putnam-2019-a5-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and
       (not (equal (mod number divisor) 0))
       (putnam-2019-a5-no-divisor-from-p
        number (+ divisor 1)))
    t))

(defun putnam-2019-a5-primep (number)
  (and
   (natp number)
   (< 1 number)
   (putnam-2019-a5-no-divisor-from-p number 2)))

(defun putnam-2019-a5-solution (p)
  (floor (- p 1) 2))

(defun putnam-2019-a5-q-coefficient (p k)
  (if (and (natp p)
           (natp k)
           (< 0 k)
           (< k p))
      (mod
       (expt k (putnam-2019-a5-solution p))
       p)
    0))

(defun putnam-2019-a5-binomial (n k)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (and (natp n) (natp k))) 0)
   ((equal k 0) 1)
   ((< n k) 0)
   ((equal n 0) 0)
   (t
    (+ (putnam-2019-a5-binomial (- n 1) (- k 1))
       (putnam-2019-a5-binomial (- n 1) k)))))

;; This is the coefficient of y^j in q(y+1), reduced modulo p. The remaining
;; argument counts k downward from p-1 to j.
(defun putnam-2019-a5-shifted-coefficient-sum
    (p j remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let ((k (+ j (- remaining 1))))
      (mod
       (+ (* (putnam-2019-a5-binomial k j)
             (putnam-2019-a5-q-coefficient p k))
          (putnam-2019-a5-shifted-coefficient-sum
           p j (- remaining 1)))
       p))))

(defun putnam-2019-a5-shifted-coefficient (p j)
  (if (and (natp p)
           (natp j)
           (<= j p))
      (putnam-2019-a5-shifted-coefficient-sum
       p j (- p j))
    0))

;; A polynomial is divisible by (x-1)^n exactly when the coefficients below
;; degree n in q(x+1) vanish. Nonvanishing at degree n makes n the greatest
;; such exponent.
(defun putnam-2019-a5-shifted-zero-below-p (p n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (and
     (equal
      (putnam-2019-a5-shifted-coefficient p (- n 1))
      0)
     (putnam-2019-a5-shifted-zero-below-p p (- n 1)))))

(defun putnambench-putnam-2019-a5-statement (p)
  (implies
   (and
    (natp p)
    (equal (mod p 2) 1)
    (putnam-2019-a5-primep p))
   (let ((solution (putnam-2019-a5-solution p)))
     (and
      (putnam-2019-a5-shifted-zero-below-p p solution)
      (not
       (equal
        (putnam-2019-a5-shifted-coefficient p solution)
        0))))))

(value-triple :itpeval-statement-checked)
:q
