;; Statement-only formalization of PutnamBench corpus artifact putnam_1991_b4:
;; for every odd prime p, a binomial sum from 0 through p is congruent to
;; 2^p + 1 modulo p^2. This file contains no proof.

(in-package "ACL2")

(defun putnam-1991-b4-no-divisor-through-p (p candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod p candidate) 0))
     (putnam-1991-b4-no-divisor-through-p
      p (- candidate 1)))))

(defun putnam-1991-b4-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (putnam-1991-b4-no-divisor-through-p
    p (- p 1))))

;; Pascal recursion represents the natural-number binomial coefficient.
(defun putnam-1991-b4-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (putnam-1991-b4-binomial-coefficient (- n 1) k)
       (putnam-1991-b4-binomial-coefficient
        (- n 1) (- k 1)))))

;; Sum choose(p,j) * choose(p+j,j) for j = 0,...,term-count-1.
(defun putnam-1991-b4-binomial-sum (p term-count)
  (declare (xargs :measure (nfix term-count)))
  (if (zp term-count)
      0
    (let ((j (- term-count 1)))
      (+
       (*
        (putnam-1991-b4-binomial-coefficient p j)
        (putnam-1991-b4-binomial-coefficient (+ p j) j))
       (putnam-1991-b4-binomial-sum p j)))))

(defun putnambench-putnam-1991-b4-statement (p)
  (implies
   (and
    (natp p)
    (putnam-1991-b4-prime-p p)
    (equal (mod p 2) 1))
   (equal
    (mod
     (putnam-1991-b4-binomial-sum p (+ p 1))
     (expt p 2))
    (mod
     (+ (expt 2 p) 1)
     (expt p 2)))))

(value-triple :itpeval-statement-checked)
:q
