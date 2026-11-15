;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.div_times, catalog title "div_mod.div_times": for every natural
;; number a and positive natural number b, the module's quotient of a times b
;; by b equals a. This file contains no proof.

(in-package "ACL2")

;; This total ACL2 function restricts on natural inputs to the source
;; module's recursion equation for div_aux.
(defun logipedia-div-mod-div-times-div-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      0
    (if (<= (nfix dividend) (nfix divisor))
        0
      (+ 1
         (logipedia-div-mod-div-times-div-aux
          (- index 1)
          (nfix (- (nfix dividend)
                   (+ 1 (nfix divisor))))
          (nfix divisor))))))

;; The source div function returns one plus the dividend at divisor zero. At
;; a positive divisor it invokes div_aux with the predecessor of the divisor.
(defun logipedia-div-mod-div-times-div (dividend divisor)
  (if (zp divisor)
      (+ 1 (nfix dividend))
    (logipedia-div-mod-div-times-div-aux
     (nfix dividend)
     (nfix dividend)
     (- (nfix divisor) 1))))

(defun-sk logipedia-div-mod-div-times-statement ()
  (forall (a b)
    (implies
     (and
      (natp a)
      (natp b)
      (< 0 b))
     (equal
      (logipedia-div-mod-div-times-div (* a b) b)
      a))))

(value-triple :itpeval-statement-checked)
:q
