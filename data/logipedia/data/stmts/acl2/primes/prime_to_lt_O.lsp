;; Statement-only formalization of Logipedia corpus artifact
;; primes.prime_to_lt_O, catalog title "primes.prime_to_lt_O": every natural
;; prime is strictly positive. This file contains no proof.

(in-package "ACL2")

;; Source divisibility is exactly the existence of a natural quotient.

(defun-sk logipedia-primes-prime-to-lt-o-divides-p
    (divisor value)
  (exists (quotient)
    (and
     (natp quotient)
     (equal value (* divisor quotient)))))

;; The source prime predicate requires p > 1 and says that every divisor of p
;; greater than one is p itself.

(defun-sk logipedia-primes-prime-to-lt-o-prime-divisors-p
    (p)
  (forall (divisor)
    (implies
     (and
      (natp divisor)
      (logipedia-primes-prime-to-lt-o-divides-p
       divisor p)
      (< 1 divisor))
     (equal divisor p))))

(defun logipedia-primes-prime-to-lt-o-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (logipedia-primes-prime-to-lt-o-prime-divisors-p
    p)))

(defun-sk logipedia-primes-prime-to-lt-o-statement ()
  (forall (p)
    (implies
     (and
      (natp p)
      (logipedia-primes-prime-to-lt-o-prime-p p))
     (< 0 p))))

(value-triple :itpeval-statement-checked)
:q
