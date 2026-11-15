;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_sumkmulnckeqnmul2pownm1: for every positive natural n, the
;; sum from k = 1 to n of k times choose(n,k) equals n times 2^(n-1).
;; This file contains no proof.

(in-package "ACL2")

;; Pascal recursion represents the natural-number binomial coefficient.
(defun numbertheory-sumkmulnckeqnmul2pownm1-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (numbertheory-sumkmulnckeqnmul2pownm1-binomial-coefficient
        (- n 1) k)
       (numbertheory-sumkmulnckeqnmul2pownm1-binomial-coefficient
        (- n 1) (- k 1)))))

(defun numbertheory-sumkmulnckeqnmul2pownm1-weighted-sum (n k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      0
    (+ (* k
          (numbertheory-sumkmulnckeqnmul2pownm1-binomial-coefficient
           n k))
       (numbertheory-sumkmulnckeqnmul2pownm1-weighted-sum
        n (- k 1)))))

(defun numbertheory-sumkmulnckeqnmul2pownm1-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (equal
    (numbertheory-sumkmulnckeqnmul2pownm1-weighted-sum n n)
    (* n (expt 2 (- n 1))))))

(value-triple :itpeval-statement-checked)
:q
