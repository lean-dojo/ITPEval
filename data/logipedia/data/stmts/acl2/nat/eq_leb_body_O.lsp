;; Statement-only formalization of Logipedia corpus artifact
;; nat.eq_leb_body_O, catalog title "nat.eq_leb_body_O": the natural-number
;; less-than-or-equal Boolean comparison body at zero is Leibniz-equal to the
;; constant-true function on naturals. This file contains no proof.

(in-package "ACL2")

;; Conservative interface for the source's natural-to-Boolean binary function.

(defstub logipedia-nat-eq-leb-body-o
  (n m)
  t)

(defun-sk logipedia-nat-eq-leb-body-o-typed-p ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (booleanp
      (logipedia-nat-eq-leb-body-o n m)))))

(defun-sk logipedia-nat-eq-leb-body-o-pointwise-p ()
  (forall (m)
    (implies
     (natp m)
     (equal
      (logipedia-nat-eq-leb-body-o 0 m)
      t))))

(defun logipedia-nat-eq-leb-body-o-statement ()
  (implies
   (logipedia-nat-eq-leb-body-o-typed-p)
   (logipedia-nat-eq-leb-body-o-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
