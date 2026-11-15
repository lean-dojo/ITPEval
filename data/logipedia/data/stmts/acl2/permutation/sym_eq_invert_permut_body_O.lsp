;; Statement-only formalization of Logipedia corpus artifact
;; permutation.sym_eq_invert_permut_body_O, catalog title
;; "permutation.sym_eq_invert_permut_body_O": the higher-order function that
;; returns zero in both branches after comparing m with f(0) is Leibniz-equal
;; to the permutation-inversion body at zero. This file contains no proof.

(in-package "ACL2")

;; The source lambda chooses zero in both Boolean branches, so its pointwise
;; result is zero without assuming anything about the represented function.
(defstub logipedia-permutation-sym-eq-invert-body-o-raw
  (function natural)
  t)

(defun logipedia-permutation-sym-eq-invert-body-o
    (function natural)
  (nfix
   (logipedia-permutation-sym-eq-invert-body-o-raw
    function
    (nfix natural))))

(defun-sk logipedia-permutation-sym-eq-invert-permut-body-o-statement ()
  (forall (function natural)
    (implies
     (natp natural)
     (equal
      0
      (logipedia-permutation-sym-eq-invert-body-o
       function natural)))))

(value-triple :itpeval-statement-checked)
:q
