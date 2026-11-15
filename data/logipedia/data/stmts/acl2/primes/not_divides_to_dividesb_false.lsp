;; Statement-only formalization of Logipedia corpus artifact
;; primes.not_divides_to_dividesb_false, catalog title
;; "primes.not_divides_to_dividesb_false": for natural numbers n and m, if n
;; is positive and does not divide m, the module's Boolean divisibility test
;; returns false. This file contains no proof.

(in-package "ACL2")

;; The source module's divisibility interface is characterized by a natural
;; quotient witness.
(defun-sk logipedia-primes-not-divides-to-dividesb-false-divides-p
    (divisor value)
  (exists (quotient)
    (and
     (natp quotient)
     (equal value (* divisor quotient)))))

;; This total ACL2 function restricts on natural inputs to the source module's
;; recursion equation for mod_aux.
(defun logipedia-primes-not-divides-to-dividesb-false-mod-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (<= (nfix dividend) (nfix divisor))
        (nfix dividend)
      (logipedia-primes-not-divides-to-dividesb-false-mod-aux
       (- index 1)
       (nfix (- (nfix dividend)
                (+ 1 (nfix divisor))))
       (nfix divisor)))))

;; At divisor zero the source mod function returns the dividend; at a positive
;; divisor it invokes mod_aux with the predecessor of the divisor.
(defun logipedia-primes-not-divides-to-dividesb-false-mod
    (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (logipedia-primes-not-divides-to-dividesb-false-mod-aux
     (nfix dividend)
     (nfix dividend)
     (- (nfix divisor) 1))))

;; This is the source module's Peano recursion for Boolean equality, represented
;; on ACL2's natural numbers with T and NIL as the true and false constructors.
(defun logipedia-primes-not-divides-to-dividesb-false-eqb (left right)
  (if (zp left)
      (if (zp right) t nil)
    (if (zp right)
        nil
      (logipedia-primes-not-divides-to-dividesb-false-eqb
       (1- left)
       (1- right)))))

(defun logipedia-primes-not-divides-to-dividesb-false-dividesb
    (divisor value)
  (logipedia-primes-not-divides-to-dividesb-false-eqb
   (logipedia-primes-not-divides-to-dividesb-false-mod value divisor)
   0))

(defun-sk logipedia-primes-not-divides-to-dividesb-false-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (< 0 n)
      (not
       (logipedia-primes-not-divides-to-dividesb-false-divides-p n m)))
     (equal
      (logipedia-primes-not-divides-to-dividesb-false-dividesb n m)
      nil))))

(value-triple :itpeval-statement-checked)
:q
