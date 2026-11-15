;; Statement-only formalization of Logipedia corpus artifact
;; primes.decidable_divides, catalog title "primes.decidable_divides":
;; divisibility is decidable for every pair of natural numbers. This file
;; contains no proof.

(in-package "ACL2")

(defun-sk logipedia-primes-decidable-divides-divides-p (n m)
  (exists (q)
    (and (natp q)
         (equal m (* n q)))))

(defun-sk logipedia-primes-decidable-divides-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (or
      (logipedia-primes-decidable-divides-divides-p n m)
      (not
       (logipedia-primes-decidable-divides-divides-p n m))))))

(value-triple :itpeval-statement-checked)
:q
