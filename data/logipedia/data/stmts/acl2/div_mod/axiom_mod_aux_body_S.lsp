;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.axiom_mod_aux_body_S, catalog title
;; "div_mod.axiom_mod_aux_body_S": at every successor recursion index, the
;; auxiliary remainder body is extensionally the natural-valued conditional
;; step determined by comparison and truncated subtraction. This file
;; contains no proof.

(in-package "ACL2")

;; ACL2 is first order, so the source function equality is stated pointwise.
;; NFIX wrappers preserve the natural codomains of the two source constants.
(defstub logipedia-div-mod-axiom-mod-aux-body-s-raw
  (index dividend divisor)
  t)

(defstub logipedia-div-mod-axiom-mod-aux-body-s-mod-aux-raw
  (index dividend divisor)
  t)

(defun logipedia-div-mod-axiom-mod-aux-body-s
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-axiom-mod-aux-body-s-raw
    (nfix index)
    (nfix dividend)
    (nfix divisor))))

(defun logipedia-div-mod-axiom-mod-aux-body-s-mod-aux
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-axiom-mod-aux-body-s-mod-aux-raw
    (nfix index)
    (nfix dividend)
    (nfix divisor))))

(defun-sk logipedia-div-mod-axiom-mod-aux-body-s-statement ()
  (forall (index dividend divisor)
    (implies
     (and
      (natp index)
      (natp dividend)
      (natp divisor))
     (equal
      (logipedia-div-mod-axiom-mod-aux-body-s
       (+ 1 index) dividend divisor)
      (if (<= dividend divisor)
          dividend
        (logipedia-div-mod-axiom-mod-aux-body-s-mod-aux
         index
         (nfix (- dividend (+ 1 divisor)))
         divisor))))))

(value-triple :itpeval-statement-checked)
:q
