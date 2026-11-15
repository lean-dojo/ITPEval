;; Statement-only formalization of Logipedia corpus artifact
;; primes.dividesb_false_to_not_divides, catalog title
;; "primes.dividesb_false_to_not_divides": for natural numbers n and m, if
;; the module's Boolean divisibility test returns false, then n does not divide
;; m. This file contains no proof.

(in-package "ACL2")

;; The source module's divisibility interface is characterized by a natural
;; quotient witness.
(defun-sk logipedia-primes-dividesb-false-to-not-divides-divides-p
    (divisor value)
  (exists (quotient)
    (and
     (natp quotient)
     (equal value (* divisor quotient)))))

;; This total ACL2 function restricts on natural inputs to the source module's
;; recursion equation for mod_aux.
(defun logipedia-primes-dividesb-false-to-not-divides-mod-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (<= (nfix dividend) (nfix divisor))
        (nfix dividend)
      (logipedia-primes-dividesb-false-to-not-divides-mod-aux
       (- index 1)
       (nfix (- (nfix dividend)
                (+ 1 (nfix divisor))))
       (nfix divisor)))))

;; At divisor zero the source mod function returns the dividend; at a positive
;; divisor it invokes mod_aux with the predecessor of the divisor.
(defun logipedia-primes-dividesb-false-to-not-divides-mod
    (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (logipedia-primes-dividesb-false-to-not-divides-mod-aux
     (nfix dividend)
     (nfix dividend)
     (- (nfix divisor) 1))))

;; This is the source module's Peano recursion for Boolean equality, represented
;; on ACL2's natural numbers with T and NIL as the true and false constructors.
(defun logipedia-primes-dividesb-false-to-not-divides-eqb (left right)
  (if (zp left)
      (if (zp right) t nil)
    (if (zp right)
        nil
      (logipedia-primes-dividesb-false-to-not-divides-eqb
       (1- left)
       (1- right)))))

(defun logipedia-primes-dividesb-false-to-not-divides-dividesb
    (divisor value)
  (logipedia-primes-dividesb-false-to-not-divides-eqb
   (logipedia-primes-dividesb-false-to-not-divides-mod value divisor)
   0))

(defun-sk logipedia-primes-dividesb-false-to-not-divides-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (equal
       (logipedia-primes-dividesb-false-to-not-divides-dividesb n m)
       nil))
     (not
      (logipedia-primes-dividesb-false-to-not-divides-divides-p n m)))))

(value-triple :itpeval-statement-checked)
:q
