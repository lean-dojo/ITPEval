;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.div_mod_spec_intro, catalog title
;; "div_mod.div_mod_spec_intro": natural quotient and remainder data satisfying
;; the remainder bound and division equation meet the division specification.
;; This file contains no proof.

(in-package "ACL2")

;; Conservative interface for the source module's abstract div_mod_spec
;; predicate.
(defstub logipedia-div-mod-spec-intro-div-mod-spec
    (dividend divisor quotient remainder)
  t)

(defun-sk logipedia-div-mod-spec-intro-statement ()
  (forall (dividend divisor quotient remainder)
    (implies
     (and
      (natp dividend)
      (natp divisor)
      (natp quotient)
      (natp remainder))
     (implies
      (< remainder divisor)
      (implies
       (equal
        dividend
        (+ (* quotient divisor) remainder))
       (logipedia-div-mod-spec-intro-div-mod-spec
        dividend divisor quotient remainder))))))

(value-triple :itpeval-statement-checked)
:q
