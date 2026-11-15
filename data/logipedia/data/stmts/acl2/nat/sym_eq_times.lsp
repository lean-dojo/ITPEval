;; Statement-only formalization of Logipedia corpus artifact nat.sym_eq_times,
;; catalog title "nat.sym_eq_times": for every natural number, the
;; natural-filtered multiplication body is Leibniz-equal to the corresponding
;; unary multiplication function. This file contains no proof.

(in-package "ACL2")

;; Raw conservative interfaces are wrapped with NFIX so that the represented
;; source constants retain their nat -> nat -> nat types without adding any
;; hypothesis to the proposition. Every natural-valued binary function is
;; represented by a suitable interpretation of its raw stub.

(defstub logipedia-nat-sym-eq-times-raw
  (left right)
  t)

(defstub logipedia-nat-sym-eq-times-body-raw
  (left right)
  t)

(defun logipedia-nat-sym-eq-times (left right)
  (nfix
   (logipedia-nat-sym-eq-times-raw
    (nfix left)
    (nfix right))))

(defun logipedia-nat-sym-eq-times-body (left right)
  (nfix
   (logipedia-nat-sym-eq-times-body-raw
    (nfix left)
    (nfix right))))

;; At the source instantiation return_ = nat -> nat, filter_nat_type returns
;; the unary-function value obtained by partially applying times_body.
(defun logipedia-nat-sym-eq-times-filtered-body (left right)
  (logipedia-nat-sym-eq-times-body left right))

;; Function-valued Leibniz equality is represented extensionally by equality
;; at every natural argument.
(defun-sk logipedia-nat-sym-eq-times-statement ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (equal
      (logipedia-nat-sym-eq-times-filtered-body left right)
      (logipedia-nat-sym-eq-times left right)))))

(value-triple :itpeval-statement-checked)
:q
