;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.eq_mod_aux_body_O, catalog title "div_mod.eq_mod_aux_body_O":
;; the zero-indexed modular-remainder auxiliary body is extensionally equal
;; on natural-number arguments to the first projection. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-div-mod-mod-aux-body (p m n) t)

(defun-sk logipedia-div-mod-eq-mod-aux-body-o-statement ()
  (forall (m n)
    (implies (and (natp m) (natp n))
             (equal (logipedia-div-mod-mod-aux-body 0 m n) m))))

(value-triple :itpeval-statement-checked)
:q
