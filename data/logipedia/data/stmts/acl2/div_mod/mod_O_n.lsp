;; Statement-only formalization of Logipedia corpus artifact div_mod.mod_O_n,
;; catalog title "div_mod.mod_O_n": the module's remainder of zero modulo
;; every natural number is zero. This file contains no proof.

(in-package "ACL2")

;; This total ACL2 function restricts on natural inputs to the source
;; module's recursion equations for mod_aux.
(defun logipedia-div-mod-mod-o-n-mod-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (<= (nfix dividend) (nfix divisor))
        (nfix dividend)
      (logipedia-div-mod-mod-o-n-mod-aux
       (- index 1)
       (nfix (- (nfix dividend)
                (+ 1 (nfix divisor))))
       (nfix divisor)))))

;; The source mod function returns the dividend at divisor zero. At a
;; positive divisor it invokes mod_aux with the predecessor of the divisor.
(defun logipedia-div-mod-mod-o-n-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (logipedia-div-mod-mod-o-n-mod-aux
     (nfix dividend)
     (nfix dividend)
     (- (nfix divisor) 1))))

(defun-sk logipedia-div-mod-mod-o-n-statement ()
  (forall (n)
    (implies
     (natp n)
     (equal
      (logipedia-div-mod-mod-o-n-mod 0 n)
      0))))

(value-triple :itpeval-statement-checked)
:q
