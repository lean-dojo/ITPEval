;; Statement-only formalization of Logipedia corpus artifact
;; nat.eq_minus_body_O, catalog title "nat.eq_minus_body_O": the natural
;; subtraction body at zero is Leibniz-equal to the constant-zero function on
;; natural numbers. This file contains no proof.

(in-package "ACL2")

;; MINUS-BODY-AT reifies the curried source constant
;; minus_body : nat -> (nat -> nat). Every ACL2 object remains eligible as a
;; function value; GENERIC-APPLICATION conservatively supplies application for
;; values whose behavior is not defined here.

(defstub logipedia-nat-eq-minus-body-o-minus-body-at
  (n)
  t)

(defstub logipedia-nat-eq-minus-body-o-generic-application
  (function-object argument)
  t)

;; This reified value is exactly the source lambda fun m : nat => O.

(defun logipedia-nat-eq-minus-body-o-constant-zero-function ()
  '(logipedia-nat-eq-minus-body-o-constant-zero-function))

(defun logipedia-nat-eq-minus-body-o-application
    (function-object argument)
  (if
      (equal
       function-object
       (logipedia-nat-eq-minus-body-o-constant-zero-function))
      0
    (logipedia-nat-eq-minus-body-o-generic-application
     function-object argument)))

(defun-sk logipedia-nat-eq-minus-body-o-natural-function-p
    (function-object)
  (forall (m)
    (implies
     (natp m)
     (natp
      (logipedia-nat-eq-minus-body-o-application
       function-object m)))))

(defun-sk logipedia-nat-eq-minus-body-o-minus-body-typed-p ()
  (forall (n)
    (implies
     (natp n)
     (logipedia-nat-eq-minus-body-o-natural-function-p
      (logipedia-nat-eq-minus-body-o-minus-body-at n)))))

;; ACL2 object identity is the direct reification of Leibniz equality at the
;; complete source function type, not an extensional pointwise replacement.

(defun logipedia-nat-eq-minus-body-o-statement ()
  (implies
   (logipedia-nat-eq-minus-body-o-minus-body-typed-p)
   (equal
    (logipedia-nat-eq-minus-body-o-minus-body-at 0)
    (logipedia-nat-eq-minus-body-o-constant-zero-function))))

(value-triple :itpeval-statement-checked)
:q
