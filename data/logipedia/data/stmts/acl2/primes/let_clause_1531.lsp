;; Statement-only formalization of Logipedia corpus artifact
;; primes.let_clause_1531, catalog title "primes.let_clause_1531": for natural
;; numbers n, m, and d, if m is positive, n divides m, and m equals n times
;; zero, then m equals zero. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-primes-let-clause-1531-divides-p (n m)
  (exists (q)
    (and
     (natp q)
     (equal m (* n q)))))

(defun-sk logipedia-primes-let-clause-1531-statement ()
  (forall (n m d)
    (implies
     (and
      (natp n)
      (natp m)
      (< 0 m)
      (logipedia-primes-let-clause-1531-divides-p n m)
      (natp d)
      (equal m (* n 0)))
     (equal m 0))))

(value-triple :itpeval-statement-checked)
:q
