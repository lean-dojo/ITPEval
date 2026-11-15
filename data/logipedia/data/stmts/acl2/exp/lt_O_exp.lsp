;; Statement-only formalization of Logipedia corpus artifact exp.lt_O_exp,
;; catalog title "exp.lt_O_exp": for every natural base and exponent, a
;; positive base has a positive natural-number power. This file contains no
;; proof.

(in-package "ACL2")

(defun logipedia-exp-lt-o-exp-statement (base exponent)
  (implies
   (and (natp base)
        (natp exponent)
        (< 0 base))
   (< 0 (expt base exponent))))

(value-triple :itpeval-statement-checked)
:q
