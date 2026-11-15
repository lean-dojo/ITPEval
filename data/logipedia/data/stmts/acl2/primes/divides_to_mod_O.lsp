;; Statement-only formalization of Logipedia corpus artifact
;; primes.divides_to_mod_O, catalog title "primes.divides_to_mod_O": for
;; natural numbers n and m, if n is positive and divides m, then the module's
;; remainder of m modulo n is zero. This file contains no proof.

(in-package "ACL2")

;; The source module's divisibility interface is characterized by a natural
;; quotient witness.
(defun-sk logipedia-primes-divides-to-mod-o-divides-p (divisor value)
  (exists (quotient)
    (and
     (natp quotient)
     (equal value (* divisor quotient)))))

;; This total ACL2 function restricts on natural inputs to the source module's
;; recursion equation for mod_aux.
(defun logipedia-primes-divides-to-mod-o-mod-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (<= (nfix dividend) (nfix divisor))
        (nfix dividend)
      (logipedia-primes-divides-to-mod-o-mod-aux
       (- index 1)
       (nfix (- (nfix dividend)
                (+ 1 (nfix divisor))))
       (nfix divisor)))))

;; At divisor zero the source mod function returns the dividend; at a positive
;; divisor it invokes mod_aux with the predecessor of the divisor.
(defun logipedia-primes-divides-to-mod-o-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (logipedia-primes-divides-to-mod-o-mod-aux
     (nfix dividend)
     (nfix dividend)
     (- (nfix divisor) 1))))

(defun-sk logipedia-primes-divides-to-mod-o-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (< 0 n)
      (logipedia-primes-divides-to-mod-o-divides-p n m))
     (equal
      (logipedia-primes-divides-to-mod-o-mod m n)
      0))))

(value-triple :itpeval-statement-checked)
:q
