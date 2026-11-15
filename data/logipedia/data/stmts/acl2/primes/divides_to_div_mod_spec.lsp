;; Statement-only formalization of Logipedia corpus artifact
;; primes.divides_to_div_mod_spec, catalog title
;; "primes.divides_to_div_mod_spec": a positive natural divisor of a natural
;; number yields the module's division specification with its computed quotient
;; and remainder zero. This file contains no proof.

(in-package "ACL2")

;; The source module's divisibility interface is characterized by a natural
;; quotient witness.
(defun-sk logipedia-primes-divides-to-div-mod-spec-divides-p
    (divisor value)
  (exists (quotient)
    (and
     (natp quotient)
     (equal value (* divisor quotient)))))

;; This total ACL2 function restricts on natural inputs to the source module's
;; recursion equation for div_aux.
(defun logipedia-primes-divides-to-div-mod-spec-div-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      0
    (if (<= (nfix dividend) (nfix divisor))
        0
      (+ 1
         (logipedia-primes-divides-to-div-mod-spec-div-aux
          (- index 1)
          (nfix (- (nfix dividend)
                   (+ 1 (nfix divisor))))
          (nfix divisor))))))

;; The source div function returns one plus the dividend at divisor zero. At
;; a positive divisor it invokes div_aux with the predecessor of the divisor.
(defun logipedia-primes-divides-to-div-mod-spec-div
    (dividend divisor)
  (if (zp divisor)
      (+ 1 (nfix dividend))
    (logipedia-primes-divides-to-div-mod-spec-div-aux
     (nfix dividend)
     (nfix dividend)
     (- (nfix divisor) 1))))

;; The source constructor and eliminator characterize div_mod_spec by the
;; remainder bound and quotient-remainder equation.
(defun logipedia-primes-divides-to-div-mod-spec-p
    (dividend divisor quotient remainder)
  (and
   (< remainder divisor)
   (equal
    dividend
    (+ (* quotient divisor) remainder))))

(defun-sk logipedia-primes-divides-to-div-mod-spec-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (< 0 n)
      (logipedia-primes-divides-to-div-mod-spec-divides-p n m))
     (logipedia-primes-divides-to-div-mod-spec-p
      m
      n
      (logipedia-primes-divides-to-div-mod-spec-div m n)
      0))))

(value-triple :itpeval-statement-checked)
:q
