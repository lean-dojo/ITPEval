;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.sym_eq_div_aux_body_S, catalog title
;; "div_mod.sym_eq_div_aux_body_S": at every successor recursion index, the
;; conditional quotient-step binary natural-number function is Leibniz-equal
;; to the auxiliary division body. This file contains no proof.

(in-package "ACL2")

;; ACL2 is first order, so function-valued source terms are represented by
;; their pointwise applications. The nfix wrappers encode their natural
;; codomains without adding totality hypotheses.

(defstub logipedia-div-mod-sym-eq-div-aux-body-s-div-aux-raw
  (index dividend divisor)
  t)

(defstub logipedia-div-mod-sym-eq-div-aux-body-s-raw
  (index dividend divisor)
  t)

(defun logipedia-div-mod-sym-eq-div-aux-body-s-div-aux
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-sym-eq-div-aux-body-s-div-aux-raw
    index dividend divisor)))

(defun logipedia-div-mod-sym-eq-div-aux-body-s
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-sym-eq-div-aux-body-s-raw
    index dividend divisor)))

(defun-sk logipedia-div-mod-sym-eq-div-aux-body-s-statement ()
  (forall (index dividend divisor)
    (implies
     (and
      (natp index)
      (natp dividend)
      (natp divisor))
     (equal
      (if (<= dividend divisor)
          0
        (+ 1
           (logipedia-div-mod-sym-eq-div-aux-body-s-div-aux
            index
            (nfix (- dividend (+ 1 divisor)))
            divisor)))
      (logipedia-div-mod-sym-eq-div-aux-body-s
       (+ 1 index) dividend divisor)))))

(value-triple :itpeval-statement-checked)
:q
