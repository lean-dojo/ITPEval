;; Statement-only formalization of Logipedia corpus artifact
;; nat.eq_times_body_O, catalog title "nat.eq_times_body_O": the
;; multiplication body at zero is Leibniz-equal at the unary natural-number
;; function type to the constant-zero function. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source function and application of its
;; reified unary natural-number function values.

(defstub logipedia-nat-eq-times-body-o
  (multiplicand)
  t)

(defstub logipedia-nat-eq-times-body-o-generic-apply
  (function-value multiplier)
  t)

(defun logipedia-nat-eq-times-body-o-constant-zero-function ()
  (list 'logipedia-nat-eq-times-body-o-constant-zero-function))

(defun logipedia-nat-eq-times-body-o-apply
    (function-value multiplier)
  (if
      (equal
       function-value
       (logipedia-nat-eq-times-body-o-constant-zero-function))
      0
    (logipedia-nat-eq-times-body-o-generic-apply
     function-value multiplier)))

(defun-sk logipedia-nat-eq-times-body-o-function-value-p
    (function-value)
  (forall (multiplier)
    (implies
     (natp multiplier)
     (natp
      (logipedia-nat-eq-times-body-o-apply
       function-value multiplier)))))

(defun-sk logipedia-nat-eq-times-body-o-typed-p ()
  (forall (multiplicand)
    (implies
     (natp multiplicand)
     (logipedia-nat-eq-times-body-o-function-value-p
      (logipedia-nat-eq-times-body-o multiplicand)))))

;; Identity of the reified values is Leibniz equality at the complete source
;; unary-function type.

(defun logipedia-nat-eq-times-body-o-leibniz-p ()
  (equal
   (logipedia-nat-eq-times-body-o 0)
   (logipedia-nat-eq-times-body-o-constant-zero-function)))

(defun logipedia-nat-eq-times-body-o-statement ()
  (implies
   (logipedia-nat-eq-times-body-o-typed-p)
   (logipedia-nat-eq-times-body-o-leibniz-p)))

(value-triple :itpeval-statement-checked)
:q
