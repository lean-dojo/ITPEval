;; Statement-only formalization of Logipedia corpus artifact
;; primes.let_clause_15311, catalog title "primes.let_clause_15311": for
;; natural numbers, if positive m is divisible by n and equals n*(p+1), then
;; m equals n+n*p; d remains universally quantified. This file contains no
;; proof.

(in-package "ACL2")

(defun-sk logipedia-primes-let-clause-15311-divides-p (n m)
  (exists (q)
    (and
     (natp q)
     (equal m (* n q)))))

(defun logipedia-primes-let-clause-15311-statement (n m d p)
  (implies
   (and
    (natp n)
    (natp m)
    (natp d)
    (natp p)
    (< 0 m)
    (logipedia-primes-let-clause-15311-divides-p n m)
    (equal m (* n (+ p 1))))
   (equal m (+ n (* n p)))))

(value-triple :itpeval-statement-checked)
:q
