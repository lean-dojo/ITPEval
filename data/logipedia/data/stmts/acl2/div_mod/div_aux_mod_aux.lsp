;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.div_aux_mod_aux, catalog title "div_mod.div_aux_mod_aux": the
;; auxiliary quotient and remainder recurrences decompose every natural
;; dividend as quotient times one plus the divisor, plus remainder. This file
;; contains no proof.

(in-package "ACL2")

;; These total ACL2 functions restrict on natural inputs to the source
;; module's recursion equations for mod_aux and div_aux.

(defun logipedia-div-mod-div-aux-mod-aux-mod-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (<= (nfix dividend) (nfix divisor))
        (nfix dividend)
      (logipedia-div-mod-div-aux-mod-aux-mod-aux
       (- index 1)
       (nfix (- (nfix dividend)
                (+ 1 (nfix divisor))))
       (nfix divisor)))))

(defun logipedia-div-mod-div-aux-mod-aux-div-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      0
    (if (<= (nfix dividend) (nfix divisor))
        0
      (+ 1
         (logipedia-div-mod-div-aux-mod-aux-div-aux
          (- index 1)
          (nfix (- (nfix dividend)
                   (+ 1 (nfix divisor))))
          (nfix divisor))))))

(defun-sk logipedia-div-mod-div-aux-mod-aux-statement ()
  (forall (index dividend divisor)
    (implies
     (and
      (natp index)
      (natp dividend)
      (natp divisor))
     (equal
      dividend
      (+
       (*
        (logipedia-div-mod-div-aux-mod-aux-div-aux
         index dividend divisor)
        (+ 1 divisor))
       (logipedia-div-mod-div-aux-mod-aux-mod-aux
        index dividend divisor))))))

(value-triple :itpeval-statement-checked)
:q
