;; Statement-only formalization of Logipedia corpus artifact
;; primes.mod_O_to_divides, catalog title "primes.mod_O_to_divides": for
;; natural numbers n and m, if n is positive and the module's remainder of m
;; modulo n is zero, then n divides m. This file contains no proof.

(in-package "ACL2")

;; The source module's divisibility interface is characterized by a natural
;; quotient witness.
(defun-sk logipedia-primes-mod-o-to-divides-divides-p (divisor value)
  (exists (quotient)
    (and
     (natp quotient)
     (equal value (* divisor quotient)))))

;; This total ACL2 function restricts on natural inputs to the source module's
;; recursion equation for mod_aux.
(defun logipedia-primes-mod-o-to-divides-mod-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (<= (nfix dividend) (nfix divisor))
        (nfix dividend)
      (logipedia-primes-mod-o-to-divides-mod-aux
       (- index 1)
       (nfix (- (nfix dividend)
                (+ 1 (nfix divisor))))
       (nfix divisor)))))

;; At divisor zero the source mod function returns the dividend; at a positive
;; divisor it invokes mod_aux with the predecessor of the divisor.
(defun logipedia-primes-mod-o-to-divides-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (logipedia-primes-mod-o-to-divides-mod-aux
     (nfix dividend)
     (nfix dividend)
     (- (nfix divisor) 1))))

(defun-sk logipedia-primes-mod-o-to-divides-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (< 0 n)
      (equal
       (logipedia-primes-mod-o-to-divides-mod m n)
       0))
     (logipedia-primes-mod-o-to-divides-divides-p n m))))

(value-triple :itpeval-statement-checked)
:q
