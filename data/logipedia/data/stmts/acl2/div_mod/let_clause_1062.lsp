;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.let_clause_1062, catalog title "div_mod.let_clause_1062": two
;; natural quotient-remainder specifications with the second quotient below
;; the first yield the second quotient-remainder decomposition in commuted
;; arithmetic form. This file contains no proof.

(in-package "ACL2")

;; The source constructor and eliminator characterize div_mod_spec by the
;; remainder bound and quotient-remainder equation.
(defun logipedia-div-mod-let-clause-1062-div-mod-spec
    (dividend divisor quotient remainder)
  (and
   (< remainder divisor)
   (equal
    dividend
    (+ (* quotient divisor) remainder))))

(defun-sk logipedia-div-mod-let-clause-1062-statement ()
  (forall (a b q r q1 r1)
    (implies
     (and
      (natp a)
      (natp b)
      (natp q)
      (natp r)
      (natp q1)
      (natp r1))
     (implies
      (logipedia-div-mod-let-clause-1062-div-mod-spec a b q r)
      (implies
       (< r b)
       (implies
        (equal a (+ (* q b) r))
        (implies
         (logipedia-div-mod-let-clause-1062-div-mod-spec a b q1 r1)
         (implies
          (< r1 b)
          (implies
           (equal a (+ (* q1 b) r1))
           (implies
            (not (<= q q1))
            (equal a (+ r1 (* b q1)))))))))))))

(value-triple :itpeval-statement-checked)
:q
