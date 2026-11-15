;; Statement-only formalization of Logipedia corpus artifact
;; primes.match_divides_prop, catalog title "primes.match_divides_prop": the
;; eliminator principle saying that divisibility yields any proposition that
;; follows from every natural-number factorization. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-primes-match-divides-prop-divides-p (n m) t)

(defun-sk logipedia-primes-match-divides-prop-factorizations-imply-p
    (n m return-type)
  (forall (q)
    (implies
     (natp q)
     (implies
      (equal m (* n q))
      return-type))))

(defun-sk logipedia-primes-match-divides-prop-statement ()
  (forall (n m return-type)
    (implies
     (and
      (natp n)
      (natp m))
     (implies
      (logipedia-primes-match-divides-prop-factorizations-imply-p
       n m return-type)
      (implies
       (logipedia-primes-match-divides-prop-divides-p n m)
       return-type)))))

(value-triple :itpeval-statement-checked)
:q
