;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.sym_eq_mod_aux_body_S, catalog title
;; "div_mod.sym_eq_mod_aux_body_S": at every successor recursion index, the
;; conditional remainder-step binary natural-number function is Leibniz-equal
;; to the auxiliary remainder body. This file contains no proof.

(in-package "ACL2")

;; ACL2 is first order, so function-valued source terms are represented by
;; their pointwise applications. The nfix wrappers encode their natural
;; codomains without adding totality hypotheses.

(defstub logipedia-div-mod-sym-eq-mod-aux-body-s-mod-aux-raw
  (index dividend divisor)
  t)

(defstub logipedia-div-mod-sym-eq-mod-aux-body-s-raw
  (index dividend divisor)
  t)

(defun logipedia-div-mod-sym-eq-mod-aux-body-s-mod-aux
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-sym-eq-mod-aux-body-s-mod-aux-raw
    index dividend divisor)))

(defun logipedia-div-mod-sym-eq-mod-aux-body-s
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-sym-eq-mod-aux-body-s-raw
    index dividend divisor)))

(defun-sk logipedia-div-mod-sym-eq-mod-aux-body-s-statement ()
  (forall (index dividend divisor)
    (implies
     (and
      (natp index)
      (natp dividend)
      (natp divisor))
     (equal
      (if (<= dividend divisor)
          dividend
        (logipedia-div-mod-sym-eq-mod-aux-body-s-mod-aux
         index
         (nfix (- dividend (+ 1 divisor)))
         divisor))
      (logipedia-div-mod-sym-eq-mod-aux-body-s
       (+ 1 index) dividend divisor)))))

(value-triple :itpeval-statement-checked)
:q
