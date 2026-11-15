;; Statement-only formalization of Logipedia corpus artifact
;; primes.divides_to_dividesb_true, catalog title
;; "primes.divides_to_dividesb_true": for natural numbers n and m, if n is
;; positive and divides m, the module's Boolean divisibility test returns true.
;; This file contains no proof.

(in-package "ACL2")

;; The source module's divisibility interface is characterized by a natural
;; quotient witness.
(defun-sk logipedia-primes-divides-to-dividesb-true-divides-p
    (divisor value)
  (exists (quotient)
    (and
     (natp quotient)
     (equal value (* divisor quotient)))))

;; This total ACL2 function restricts on natural inputs to the source module's
;; recursion equation for mod_aux.
(defun logipedia-primes-divides-to-dividesb-true-mod-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (<= (nfix dividend) (nfix divisor))
        (nfix dividend)
      (logipedia-primes-divides-to-dividesb-true-mod-aux
       (- index 1)
       (nfix (- (nfix dividend)
                (+ 1 (nfix divisor))))
       (nfix divisor)))))

;; At divisor zero the source mod function returns the dividend; at a positive
;; divisor it invokes mod_aux with the predecessor of the divisor.
(defun logipedia-primes-divides-to-dividesb-true-mod
    (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (logipedia-primes-divides-to-dividesb-true-mod-aux
     (nfix dividend)
     (nfix dividend)
     (- (nfix divisor) 1))))

;; This is the source module's Peano recursion for Boolean equality, represented
;; on ACL2's natural numbers with T and NIL as the true and false constructors.
(defun logipedia-primes-divides-to-dividesb-true-eqb (left right)
  (if (zp left)
      (if (zp right) t nil)
    (if (zp right)
        nil
      (logipedia-primes-divides-to-dividesb-true-eqb
       (1- left)
       (1- right)))))

(defun logipedia-primes-divides-to-dividesb-true-dividesb
    (divisor value)
  (logipedia-primes-divides-to-dividesb-true-eqb
   (logipedia-primes-divides-to-dividesb-true-mod value divisor)
   0))

(defun-sk logipedia-primes-divides-to-dividesb-true-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (< 0 n)
      (logipedia-primes-divides-to-dividesb-true-divides-p n m))
     (equal
      (logipedia-primes-divides-to-dividesb-true-dividesb n m)
      t))))

(value-triple :itpeval-statement-checked)
:q
