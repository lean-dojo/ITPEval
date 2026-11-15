;; Statement-only formalization of Logipedia corpus artifact
;; primes.divides_n_n, catalog title "primes.divides_n_n": every natural
;; number divides itself, with divisibility witnessed by a natural quotient.
;; This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-primes-divides-n-n-divides-p (n m)
  (exists (q)
    (and
     (natp q)
     (equal m (* n q)))))

(defun-sk logipedia-primes-divides-n-n-statement ()
  (forall (n)
    (implies
     (natp n)
     (logipedia-primes-divides-n-n-divides-p n n))))

(value-triple :itpeval-statement-checked)
:q
