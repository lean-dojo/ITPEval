;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.eq_times_div_minus_mod, catalog title
;; "div_mod.eq_times_div_minus_mod": for all natural numbers, the module's
;; quotient times the divisor equals the dividend minus its remainder. This
;; file contains no proof.

(in-package "ACL2")

;; These total ACL2 functions restrict on natural inputs to the source
;; module's recursion equations for mod_aux and div_aux.

(defun logipedia-div-mod-eq-times-div-minus-mod-mod-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (<= (nfix dividend) (nfix divisor))
        (nfix dividend)
      (logipedia-div-mod-eq-times-div-minus-mod-mod-aux
       (- index 1)
       (nfix (- (nfix dividend)
                (+ 1 (nfix divisor))))
       (nfix divisor)))))

(defun logipedia-div-mod-eq-times-div-minus-mod-div-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      0
    (if (<= (nfix dividend) (nfix divisor))
        0
      (+ 1
         (logipedia-div-mod-eq-times-div-minus-mod-div-aux
          (- index 1)
          (nfix (- (nfix dividend)
                   (+ 1 (nfix divisor))))
          (nfix divisor))))))

;; The source functions inspect the divisor. At zero, mod(a, 0) = a and
;; div(a, 0) = a + 1; at a successor divisor they invoke the auxiliaries with
;; recursion index and dividend both equal to a.

(defun logipedia-div-mod-eq-times-div-minus-mod-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (logipedia-div-mod-eq-times-div-minus-mod-mod-aux
     (nfix dividend)
     (nfix dividend)
     (- (nfix divisor) 1))))

(defun logipedia-div-mod-eq-times-div-minus-mod-div (dividend divisor)
  (if (zp divisor)
      (+ 1 (nfix dividend))
    (logipedia-div-mod-eq-times-div-minus-mod-div-aux
     (nfix dividend)
     (nfix dividend)
     (- (nfix divisor) 1))))

(defun-sk logipedia-div-mod-eq-times-div-minus-mod-statement ()
  (forall (a b)
    (implies
     (and
      (natp a)
      (natp b))
     (equal
      (*
       (logipedia-div-mod-eq-times-div-minus-mod-div a b)
       b)
      (nfix
       (- a
          (logipedia-div-mod-eq-times-div-minus-mod-mod a b)))))))

(value-triple :itpeval-statement-checked)
:q
