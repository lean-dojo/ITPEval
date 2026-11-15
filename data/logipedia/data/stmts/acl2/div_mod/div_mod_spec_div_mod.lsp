;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.div_mod_spec_div_mod, catalog title
;; "div_mod.div_mod_spec_div_mod": for a positive natural divisor, the
;; module's quotient and remainder satisfy the natural-number division
;; specification. This file contains no proof.

(in-package "ACL2")

;; These total ACL2 functions restrict on natural inputs to the source
;; module's recursion equations for mod_aux and div_aux.

(defun logipedia-div-mod-spec-div-mod-mod-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (<= (nfix dividend) (nfix divisor))
        (nfix dividend)
      (logipedia-div-mod-spec-div-mod-mod-aux
       (- index 1)
       (nfix (- (nfix dividend)
                (+ 1 (nfix divisor))))
       (nfix divisor)))))

(defun logipedia-div-mod-spec-div-mod-div-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      0
    (if (<= (nfix dividend) (nfix divisor))
        0
      (+ 1
         (logipedia-div-mod-spec-div-mod-div-aux
          (- index 1)
          (nfix (- (nfix dividend)
                   (+ 1 (nfix divisor))))
          (nfix divisor))))))

;; The source functions inspect the divisor. At zero, mod(n, 0) = n and
;; div(n, 0) = n + 1; at a successor divisor they invoke the auxiliaries with
;; recursion index and dividend both equal to n.

(defun logipedia-div-mod-spec-div-mod-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (logipedia-div-mod-spec-div-mod-mod-aux
     (nfix dividend)
     (nfix dividend)
     (- (nfix divisor) 1))))

(defun logipedia-div-mod-spec-div-mod-div (dividend divisor)
  (if (zp divisor)
      (+ 1 (nfix dividend))
    (logipedia-div-mod-spec-div-mod-div-aux
     (nfix dividend)
     (nfix dividend)
     (- (nfix divisor) 1))))

;; The source div_mod_spec constructor and eliminator characterize the
;; predicate by these two conjuncts.

(defun-sk logipedia-div-mod-spec-div-mod-statement ()
  (forall (dividend divisor)
    (implies
     (and
      (natp dividend)
      (natp divisor)
      (< 0 divisor))
     (and
      (<
       (logipedia-div-mod-spec-div-mod-mod dividend divisor)
       divisor)
      (equal
       dividend
       (+
        (*
         (logipedia-div-mod-spec-div-mod-div dividend divisor)
         divisor)
        (logipedia-div-mod-spec-div-mod-mod dividend divisor)))))))

(value-triple :itpeval-statement-checked)
:q
