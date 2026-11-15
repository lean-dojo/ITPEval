;; Statement-only formalization of Logipedia corpus artifact
;; fermat.prime_to_not_divides_fact, catalog title
;; "fermat.prime_to_not_divides_fact": a natural prime p does not divide n!
;; when the natural number n is strictly less than p. This file contains no
;; proof.

(in-package "ACL2")

(defun-sk logipedia-fermat-prime-to-not-divides-fact-divides-p
    (divisor value)
  (exists (quotient)
    (and
     (natp quotient)
     (equal value (* divisor quotient)))))

(defun-sk logipedia-fermat-prime-to-not-divides-fact-prime-divisors-p
    (p)
  (forall (m)
    (implies
     (and
      (natp m)
      (logipedia-fermat-prime-to-not-divides-fact-divides-p m p)
      (< 1 m))
     (equal m p))))

(defun logipedia-fermat-prime-to-not-divides-fact-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (logipedia-fermat-prime-to-not-divides-fact-prime-divisors-p p)))

(defun logipedia-fermat-prime-to-not-divides-fact-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (logipedia-fermat-prime-to-not-divides-fact-factorial (- n 1))
       n)))

(defun-sk logipedia-fermat-prime-to-not-divides-fact-statement ()
  (forall (p n)
    (implies
     (and
      (natp p)
      (logipedia-fermat-prime-to-not-divides-fact-prime-p p)
      (natp n)
      (< n p))
     (not
      (logipedia-fermat-prime-to-not-divides-fact-divides-p
       p
       (logipedia-fermat-prime-to-not-divides-fact-factorial n))))))

(value-triple :itpeval-statement-checked)
:q
