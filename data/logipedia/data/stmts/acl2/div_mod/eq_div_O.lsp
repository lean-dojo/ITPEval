;; Statement-only formalization of Logipedia corpus artifact div_mod.eq_div_O,
;; catalog title "div_mod.eq_div_O": for natural numbers n and m with n less
;; than m, the module's quotient of n by m is zero. This file contains no proof.

(in-package "ACL2")

;; This total ACL2 function restricts on natural inputs to the source
;; module's recursion equation for div_aux.
(defun logipedia-div-mod-eq-div-o-div-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      0
    (if (<= (nfix dividend) (nfix divisor))
        0
      (+ 1
         (logipedia-div-mod-eq-div-o-div-aux
          (- index 1)
          (nfix (- (nfix dividend)
                   (+ 1 (nfix divisor))))
          (nfix divisor))))))

;; The source div function returns one plus the dividend at divisor zero. At
;; a positive divisor it invokes div_aux with the predecessor of the divisor.
(defun logipedia-div-mod-eq-div-o-div (dividend divisor)
  (if (zp divisor)
      (+ 1 (nfix dividend))
    (logipedia-div-mod-eq-div-o-div-aux
     (nfix dividend)
     (nfix dividend)
     (- (nfix divisor) 1))))

(defun-sk logipedia-div-mod-eq-div-o-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (< n m))
     (equal
      (logipedia-div-mod-eq-div-o-div n m)
      0))))

(value-triple :itpeval-statement-checked)
:q
