;; Statement-only formalization of Logipedia corpus artifact
;; primes.reflexive_divides, catalog title "primes.reflexive_divides":
;; natural-number divisibility is reflexive, with divisibility witnessed by
;; a natural quotient. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-primes-reflexive-divides-divides-p (n m)
  (exists (q)
    (and
     (natp q)
     (equal m (* n q)))))

(defun-sk logipedia-primes-reflexive-divides-statement ()
  (forall (x)
    (implies
     (natp x)
     (logipedia-primes-reflexive-divides-divides-p x x))))

(value-triple :itpeval-statement-checked)
:q
