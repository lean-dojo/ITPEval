;; Statement-only formalization of Logipedia corpus artifact
;; primes.divides_to_le, catalog title "primes.divides_to_le": for natural
;; numbers n and m, if m is positive and n divides m, then n is at most m.
;; Divisibility is witnessed by a natural quotient. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-primes-divides-to-le-divides-p (n m)
  (exists (q)
    (and
     (natp q)
     (equal m (* n q)))))

(defun-sk logipedia-primes-divides-to-le-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (< 0 m)
      (logipedia-primes-divides-to-le-divides-p n m))
     (<= n m))))

(value-triple :itpeval-statement-checked)
:q
