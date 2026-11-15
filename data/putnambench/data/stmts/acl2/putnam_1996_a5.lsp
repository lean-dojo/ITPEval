;; Statement-only formalization of PutnamBench corpus artifact putnam_1996_a5:
;; for every prime natural p greater than 3, the sum of choose(p,i) from
;; i = 1 through floor(2*p/3) is divisible by p^2. This file contains no proof.

(in-package "ACL2")

;; Trial division through p-1 is exactly primality for natural p > 1.
(defun putnam-1996-a5-no-divisor-through-p (p candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod p candidate) 0))
     (putnam-1996-a5-no-divisor-through-p
      p (- candidate 1)))))

(defun putnam-1996-a5-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (putnam-1996-a5-no-divisor-through-p
    p (- p 1))))

;; Pascal recursion represents the natural-number binomial coefficient.
(defun putnam-1996-a5-binomial-coefficient (n i)
  (declare (xargs :measure (nfix n)))
  (if (or (zp i)
          (zp n))
      (if (zp i) 1 0)
    (+ (putnam-1996-a5-binomial-coefficient (- n 1) i)
       (putnam-1996-a5-binomial-coefficient
        (- n 1) (- i 1)))))

;; Inclusive sum of choose(p,i) for i = 1,...,upper.
(defun putnam-1996-a5-binomial-sum-through (p upper)
  (declare (xargs :measure (nfix upper)))
  (if (zp upper)
      0
    (+ (putnam-1996-a5-binomial-sum-through
        p (- upper 1))
       (putnam-1996-a5-binomial-coefficient p upper))))

(defun putnambench-putnam-1996-a5-statement (p k)
  (implies
   (and
    (natp p)
    (natp k)
    (putnam-1996-a5-prime-p p)
    (> p 3)
    (equal k (floor (* 2 p) 3)))
   (equal
    (mod
     (putnam-1996-a5-binomial-sum-through p k)
     (expt p 2))
    0)))

(value-triple :itpeval-statement-checked)
:q
