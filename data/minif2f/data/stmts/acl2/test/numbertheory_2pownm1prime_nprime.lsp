;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_2pownm1prime_nprime: for every positive natural number n,
;; if the Mersenne number 2^n - 1 is prime, then n is prime. This file
;; contains no proof.

(in-package "ACL2")

(defun numbertheory-2pownm1prime-nprime-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (numbertheory-2pownm1prime-nprime-no-divisor-from-p
            n
            (+ d 1)))
    t))

(defun numbertheory-2pownm1prime-nprime-primep (n)
  (and (natp n)
       (< 1 n)
       (numbertheory-2pownm1prime-nprime-no-divisor-from-p n 2)))

(defun numbertheory-2pownm1prime-nprime-statement (n)
  (implies
   (and (natp n)
        (< 0 n)
        (numbertheory-2pownm1prime-nprime-primep
         (- (expt 2 n) 1)))
   (numbertheory-2pownm1prime-nprime-primep n)))

(value-triple :itpeval-statement-checked)
:q
