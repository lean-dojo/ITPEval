;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.le_mod_aux_m_m, catalog title "div_mod.le_mod_aux_m_m": when the
;; natural input n is at most the recursion index p, the auxiliary remainder
;; value mod_aux(p, n, m) is at most m. This file contains no proof.

(in-package "ACL2")

;; This total ACL2 function restricts on natural inputs to the source
;; module's recursion equations for mod_aux.
(defun logipedia-div-mod-le-mod-aux-m-m-mod-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (<= (nfix dividend) (nfix divisor))
        (nfix dividend)
      (logipedia-div-mod-le-mod-aux-m-m-mod-aux
       (- index 1)
       (nfix (- (nfix dividend)
                (+ 1 (nfix divisor))))
       (nfix divisor)))))

(defun-sk logipedia-div-mod-le-mod-aux-m-m-statement ()
  (forall (p n m)
    (implies
     (and
      (natp p)
      (natp n)
      (natp m)
      (<= n p))
     (<=
      (logipedia-div-mod-le-mod-aux-m-m-mod-aux p n m)
      m))))

(value-triple :itpeval-statement-checked)
:q
