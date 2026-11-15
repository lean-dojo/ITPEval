;; Statement-only formalization of Logipedia corpus artifact
;; primes.quotient, catalog title "primes.quotient": for natural numbers n,
;; m, and q, a factorization m = n*q entails that n divides m. This file
;; contains no proof.

(in-package "ACL2")

(defstub logipedia-primes-quotient-divides-p (n m) t)

(defun-sk logipedia-primes-quotient-statement ()
  (forall (n m q)
    (implies
     (and
      (natp n)
      (natp m)
      (natp q))
     (implies
      (equal m (* n q))
      (logipedia-primes-quotient-divides-p n m)))))

(value-triple :itpeval-statement-checked)
:q
