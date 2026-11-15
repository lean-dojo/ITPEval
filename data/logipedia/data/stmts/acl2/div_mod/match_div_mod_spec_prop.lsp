;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.match_div_mod_spec_prop, catalog title
;; "div_mod.match_div_mod_spec_prop": the abstract natural quotient-remainder
;; specification entails its remainder bound and quotient-remainder equation.
;; This file contains no proof.

(in-package "ACL2")

;; Conservative interface for the module's abstract div_mod_spec predicate.
(defstub logipedia-div-mod-match-div-mod-spec-prop-div-mod-spec-p
  (dividend divisor quotient remainder)
  t)

;; The source eliminator, universally quantified over its return proposition,
;; is equivalent to this conjunction.
(defun logipedia-div-mod-match-div-mod-spec-prop-statement
    (dividend divisor quotient remainder)
  (implies
   (and
    (natp dividend)
    (natp divisor)
    (natp quotient)
    (natp remainder))
   (implies
    (logipedia-div-mod-match-div-mod-spec-prop-div-mod-spec-p
     dividend divisor quotient remainder)
    (and
     (< remainder divisor)
     (equal
      dividend
      (+ (* quotient divisor) remainder))))))

(value-triple :itpeval-statement-checked)
:q
