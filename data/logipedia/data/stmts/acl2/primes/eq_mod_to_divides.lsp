;; Statement-only formalization of Logipedia corpus artifact
;; primes.eq_mod_to_divides, catalog title "primes.eq_mod_to_divides":
;; natural numbers with equal remainders modulo a positive natural modulus
;; have a truncated natural difference divisible by that modulus. This file
;; contains no proof.

(in-package "ACL2")

;; The source module's divisibility relation is existence of a natural
;; quotient whose product with the divisor is the value.
(defun-sk logipedia-primes-eq-mod-to-divides-divides-p
    (divisor value)
  (exists (quotient)
    (and
     (natp divisor)
     (natp value)
     (natp quotient)
     (equal value (* divisor quotient)))))

;; This total ACL2 function restricts on natural inputs to the source module's
;; recursion equations for mod_aux.
(defun logipedia-primes-eq-mod-to-divides-mod-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (<= (nfix dividend) (nfix divisor))
        (nfix dividend)
      (logipedia-primes-eq-mod-to-divides-mod-aux
       (- index 1)
       (nfix (- (nfix dividend)
                (+ 1 (nfix divisor))))
       (nfix divisor)))))

;; At divisor zero the source mod function returns the dividend; at a positive
;; divisor it invokes mod_aux with the predecessor of the divisor.
(defun logipedia-primes-eq-mod-to-divides-mod
    (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (logipedia-primes-eq-mod-to-divides-mod-aux
     (nfix dividend)
     (nfix dividend)
     (- (nfix divisor) 1))))

(defun-sk logipedia-primes-eq-mod-to-divides-statement ()
  (forall (n m q)
    (implies
     (and
      (natp n)
      (natp m)
      (natp q)
      (< 0 q)
      (equal
       (logipedia-primes-eq-mod-to-divides-mod n q)
       (logipedia-primes-eq-mod-to-divides-mod m q)))
     (logipedia-primes-eq-mod-to-divides-divides-p
      q
      (nfix (- n m))))))

(value-triple :itpeval-statement-checked)
:q
