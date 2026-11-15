;; Statement-only formalization of PutnamBench corpus artifact putnam_1977_a5:
;; for a prime natural p and natural numbers m >= n, the binomial coefficients
;; choose(p*m,p*n) and choose(m,n) are congruent modulo p. This file contains
;; no proof.

(in-package "ACL2")

;; Pascal recursion represents the natural-number binomial coefficient.
(defun putnam-1977-a5-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (putnam-1977-a5-binomial-coefficient (- n 1) k)
       (putnam-1977-a5-binomial-coefficient
        (- n 1) (- k 1)))))

(defun putnam-1977-a5-no-divisor-through-p (p candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod p candidate) 0))
     (putnam-1977-a5-no-divisor-through-p
      p (- candidate 1)))))

(defun putnam-1977-a5-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (putnam-1977-a5-no-divisor-through-p
    p (- p 1))))

(defun putnambench-putnam-1977-a5-statement (p m n)
  (implies
   (and
    (natp p)
    (natp m)
    (natp n)
    (putnam-1977-a5-prime-p p)
    (<= n m))
   (equal
    (mod
     (putnam-1977-a5-binomial-coefficient
      (* p m) (* p n))
     p)
    (mod
     (putnam-1977-a5-binomial-coefficient m n)
     p))))

(value-triple :itpeval-statement-checked)
:q
