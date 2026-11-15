;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.div_mod_spec_to_eq, catalog title
;; "div_mod.div_mod_spec_to_eq": two natural quotient-remainder
;; specifications for the same dividend and divisor have equal quotients.
;; This file contains no proof.

(in-package "ACL2")

;; The source constructor and eliminator characterize div_mod_spec by the
;; remainder bound and quotient-remainder equation.
(defun logipedia-div-mod-spec-to-eq-div-mod-spec
    (dividend divisor quotient remainder)
  (and
   (< remainder divisor)
   (equal
    dividend
    (+ (* quotient divisor) remainder))))

(defun-sk logipedia-div-mod-spec-to-eq-statement ()
  (forall (dividend divisor quotient remainder quotient1 remainder1)
    (implies
     (and
      (natp dividend)
      (natp divisor)
      (natp quotient)
      (natp remainder)
      (natp quotient1)
      (natp remainder1))
     (implies
      (logipedia-div-mod-spec-to-eq-div-mod-spec
       dividend divisor quotient remainder)
      (implies
       (logipedia-div-mod-spec-to-eq-div-mod-spec
        dividend divisor quotient1 remainder1)
       (equal quotient quotient1))))))

(value-triple :itpeval-statement-checked)
:q
