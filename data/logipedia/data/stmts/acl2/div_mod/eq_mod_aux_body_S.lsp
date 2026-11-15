;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.eq_mod_aux_body_S, catalog title "div_mod.eq_mod_aux_body_S":
;; at every successor recursion index, the auxiliary remainder body is
;; Leibniz-equal at its binary natural-number function type to the conditional
;; remainder-step function. This file contains no proof.

(in-package "ACL2")

;; ACL2 is first order, so function-valued source terms are represented by
;; their pointwise applications. The nfix wrappers encode their natural
;; codomains without adding totality hypotheses.

(defstub logipedia-div-mod-eq-mod-aux-body-s-mod-aux-raw
  (index dividend divisor)
  t)

(defstub logipedia-div-mod-eq-mod-aux-body-s-raw
  (index dividend divisor)
  t)

(defun logipedia-div-mod-eq-mod-aux-body-s-mod-aux
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-eq-mod-aux-body-s-mod-aux-raw
    index dividend divisor)))

(defun logipedia-div-mod-eq-mod-aux-body-s
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-eq-mod-aux-body-s-raw
    index dividend divisor)))

(defun-sk logipedia-div-mod-eq-mod-aux-body-s-statement ()
  (forall (index dividend divisor)
    (implies
     (and
      (natp index)
      (natp dividend)
      (natp divisor))
     (equal
      (logipedia-div-mod-eq-mod-aux-body-s
       (+ 1 index) dividend divisor)
      (if (<= dividend divisor)
          dividend
        (logipedia-div-mod-eq-mod-aux-body-s-mod-aux
         index
         (nfix (- dividend (+ 1 divisor)))
         divisor))))))

(value-triple :itpeval-statement-checked)
:q
