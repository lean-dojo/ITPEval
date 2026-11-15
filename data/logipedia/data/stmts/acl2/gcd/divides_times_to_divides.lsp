;; Statement-only formalization of Logipedia corpus artifact
;; gcd.divides_times_to_divides, catalog title
;; "gcd.divides_times_to_divides": for all natural p, n, and m, if p is
;; prime and divides n times m, then p divides n or p divides m. This file
;; contains no proof.

(in-package "ACL2")

;; Source divisibility is the existence of a natural quotient.

(defun-sk logipedia-gcd-divides-times-to-divides-divides-p
    (divisor dividend)
  (exists (quotient)
    (and
     (natp divisor)
     (natp dividend)
     (natp quotient)
     (equal dividend (* divisor quotient)))))

;; The source prime predicate says that p is greater than one and every
;; divisor of p that is greater than one is p itself.

(defun-sk logipedia-gcd-divides-times-to-divides-prime-divisors-p
    (p)
  (forall (divisor)
    (implies
     (and
      (natp divisor)
      (logipedia-gcd-divides-times-to-divides-divides-p
       divisor p)
      (< 1 divisor))
     (equal divisor p))))

(defun logipedia-gcd-divides-times-to-divides-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (logipedia-gcd-divides-times-to-divides-prime-divisors-p
    p)))

(defun-sk logipedia-gcd-divides-times-to-divides-statement ()
  (forall (p n m)
    (implies
     (and
      (natp p)
      (natp n)
      (natp m)
      (logipedia-gcd-divides-times-to-divides-prime-p p)
      (logipedia-gcd-divides-times-to-divides-divides-p
       p (* n m)))
     (or
      (logipedia-gcd-divides-times-to-divides-divides-p
       p n)
      (logipedia-gcd-divides-times-to-divides-divides-p
       p m)))))

(value-triple :itpeval-statement-checked)
:q
