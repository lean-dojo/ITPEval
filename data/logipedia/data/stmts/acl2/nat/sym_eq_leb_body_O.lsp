;; Statement-only formalization of Logipedia corpus artifact
;; nat.sym_eq_leb_body_O, catalog title "nat.sym_eq_leb_body_O": the
;; constant-true function on natural numbers is Leibniz-equal to the
;; natural-number less-than-or-equal Boolean comparison body at zero. This
;; file contains no proof.

(in-package "ACL2")

;; Conservative interface for the source's natural-to-Boolean binary function.

(defstub logipedia-nat-sym-eq-leb-body-o
  (n m)
  t)

(defun-sk logipedia-nat-sym-eq-leb-body-o-typed-p ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (booleanp
      (logipedia-nat-sym-eq-leb-body-o n m)))))

;; Leibniz equality of the source functions nat -> bool is represented
;; extensionally at every natural argument, with the source order preserved.

(defun-sk logipedia-nat-sym-eq-leb-body-o-pointwise-p ()
  (forall (m)
    (implies
     (natp m)
     (equal
      t
      (logipedia-nat-sym-eq-leb-body-o 0 m)))))

(defun logipedia-nat-sym-eq-leb-body-o-statement ()
  (implies
   (logipedia-nat-sym-eq-leb-body-o-typed-p)
   (logipedia-nat-sym-eq-leb-body-o-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
