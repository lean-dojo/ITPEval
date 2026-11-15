;; Statement-only formalization of Logipedia corpus artifact
;; gcd.eq_gcd_aux_body_O, catalog title "gcd.eq_gcd_aux_body_O": at recursion
;; index zero, the auxiliary gcd body is Leibniz-equal at its binary
;; natural-number function type to the function returning its first argument.
;; This file contains no proof.

(in-package "ACL2")

;; Reify the source's binary function values so ACL2 equality represents
;; Leibniz equality at the complete function type.

(defstub logipedia-gcd-eq-gcd-aux-body-o-gcd-aux-body
  (index)
  t)

(defstub logipedia-gcd-eq-gcd-aux-body-o-generic-apply
  (function-value first second)
  t)

(defun logipedia-gcd-eq-gcd-aux-body-o-first-projection ()
  'logipedia-gcd-eq-gcd-aux-body-o-first-projection)

(defun logipedia-gcd-eq-gcd-aux-body-o-apply
    (function-value first second)
  (if
      (equal
       function-value
       (logipedia-gcd-eq-gcd-aux-body-o-first-projection))
      (nfix first)
    (logipedia-gcd-eq-gcd-aux-body-o-generic-apply
     function-value first second)))

(defun-sk logipedia-gcd-eq-gcd-aux-body-o-function-value-p
    (function-value)
  (forall (first second)
    (implies
     (and
      (natp first)
      (natp second))
     (natp
      (logipedia-gcd-eq-gcd-aux-body-o-apply
       function-value first second)))))

(defun-sk logipedia-gcd-eq-gcd-aux-body-o-gcd-aux-body-typed-p ()
  (forall (index)
    (implies
     (natp index)
     (logipedia-gcd-eq-gcd-aux-body-o-function-value-p
      (logipedia-gcd-eq-gcd-aux-body-o-gcd-aux-body index)))))

(defun logipedia-gcd-eq-gcd-aux-body-o-statement ()
  (implies
   (logipedia-gcd-eq-gcd-aux-body-o-gcd-aux-body-typed-p)
   (equal
    (logipedia-gcd-eq-gcd-aux-body-o-gcd-aux-body 0)
    (logipedia-gcd-eq-gcd-aux-body-o-first-projection))))

(value-triple :itpeval-statement-checked)
:q
