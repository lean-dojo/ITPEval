;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.eq_mod_aux, catalog title "div_mod.eq_mod_aux": for every natural
;; recursion index, the auxiliary remainder function is Leibniz-equal to its
;; natural-filtered body as a binary natural-number function. This file
;; contains no proof.

(in-package "ACL2")

;; ACL2 stubs are untyped. Wrapping their results with nfix encodes the
;; source functions' natural codomain without making totality a hypothesis.

(defstub logipedia-div-mod-eq-mod-aux-raw
  (index dividend divisor)
  t)

(defstub logipedia-div-mod-eq-mod-aux-body-raw
  (index dividend divisor)
  t)

(defun logipedia-div-mod-eq-mod-aux
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-eq-mod-aux-raw
    index dividend divisor)))

(defun logipedia-div-mod-eq-mod-aux-body
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-eq-mod-aux-body-raw
    index dividend divisor)))

;; Universal pointwise equality is ACL2's first-order rendering of source
;; Leibniz equality at the complete binary natural-function type.
(defun-sk logipedia-div-mod-eq-mod-aux-statement ()
  (forall (index dividend divisor)
    (implies
     (and
      (natp index)
      (natp dividend)
      (natp divisor))
     (equal
      (logipedia-div-mod-eq-mod-aux
       index dividend divisor)
      (logipedia-div-mod-eq-mod-aux-body
       index dividend divisor)))))

(value-triple :itpeval-statement-checked)
:q
