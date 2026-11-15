;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.lt_mod_m_m, catalog title "div_mod.lt_mod_m_m": for every natural
;; number n and positive natural number m, the module's remainder of n modulo
;; m is strictly less than m. This file contains no proof.

(in-package "ACL2")

;; This total ACL2 function restricts on natural inputs to the source
;; module's recursion equations for mod_aux.
(defun logipedia-div-mod-lt-mod-m-m-mod-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (<= (nfix dividend) (nfix divisor))
        (nfix dividend)
      (logipedia-div-mod-lt-mod-m-m-mod-aux
       (- index 1)
       (nfix (- (nfix dividend)
                (+ 1 (nfix divisor))))
       (nfix divisor)))))

;; The source mod function returns the dividend at divisor zero. At a
;; positive divisor it invokes mod_aux with the predecessor of the divisor.
(defun logipedia-div-mod-lt-mod-m-m-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (logipedia-div-mod-lt-mod-m-m-mod-aux
     (nfix dividend)
     (nfix dividend)
     (- (nfix divisor) 1))))

(defun-sk logipedia-div-mod-lt-mod-m-m-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (< 0 m))
     (<
      (logipedia-div-mod-lt-mod-m-m-mod n m)
      m))))

(value-triple :itpeval-statement-checked)
:q
