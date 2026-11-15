;; Statement-only formalization of Logipedia corpus artifact
;; gcd.axiom_gcd_aux_body_O, catalog title
;; "gcd.axiom_gcd_aux_body_O": at recursion index zero, the auxiliary gcd
;; body is extensionally the binary natural-number function that returns its
;; first argument. This file contains no proof.

(in-package "ACL2")

;; Conservative interface for the source's natural-valued ternary function.

(defstub logipedia-gcd-axiom-gcd-aux-body-o
  (index first second)
  t)

(defun-sk logipedia-gcd-axiom-gcd-aux-body-o-typed-p ()
  (forall (index first second)
    (implies
     (and
      (natp index)
      (natp first)
      (natp second))
     (natp
      (logipedia-gcd-axiom-gcd-aux-body-o
       index first second)))))

(defun-sk logipedia-gcd-axiom-gcd-aux-body-o-pointwise-p ()
  (forall (first second)
    (implies
     (and
      (natp first)
      (natp second))
     (equal
      (logipedia-gcd-axiom-gcd-aux-body-o
       0 first second)
      first))))

(defun logipedia-gcd-axiom-gcd-aux-body-o-statement ()
  (implies
   (logipedia-gcd-axiom-gcd-aux-body-o-typed-p)
   (logipedia-gcd-axiom-gcd-aux-body-o-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
