;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.sym_eq_div_aux, catalog title "div_mod.sym_eq_div_aux": for every
;; natural recursion index, the natural-filtered auxiliary division body is
;; Leibniz-equal to the auxiliary division function as a binary natural-number
;; function. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's arbitrary natural-valued
;; functions.  The nfix wrappers make the source codomain native to ACL2
;; without imposing it as an extra hypothesis of the statement.

(defstub logipedia-div-mod-sym-eq-div-aux-raw
  (index dividend divisor)
  t)

(defstub logipedia-div-mod-sym-eq-div-aux-body-raw
  (index dividend divisor)
  t)

(defun logipedia-div-mod-sym-eq-div-aux
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-sym-eq-div-aux-raw
    index dividend divisor)))

(defun logipedia-div-mod-sym-eq-div-aux-body
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-sym-eq-div-aux-body-raw
    index dividend divisor)))

;; On natural indices, the source module's filter_nat_type is extensionally
;; the identity. This helper makes that definitional encoding explicit.
(defun logipedia-div-mod-sym-eq-div-aux-filtered-body
    (index dividend divisor)
  (logipedia-div-mod-sym-eq-div-aux-body index dividend divisor))

(defun-sk logipedia-div-mod-sym-eq-div-aux-statement ()
  (forall (index dividend divisor)
    (implies
     (and
      (natp index)
      (natp dividend)
      (natp divisor))
     (equal
      (logipedia-div-mod-sym-eq-div-aux-filtered-body
       index dividend divisor)
      (logipedia-div-mod-sym-eq-div-aux
       index dividend divisor)))))

(value-triple :itpeval-statement-checked)
:q
