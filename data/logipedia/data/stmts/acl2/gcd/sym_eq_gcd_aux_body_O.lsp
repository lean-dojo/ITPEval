;; Statement-only formalization of Logipedia corpus artifact
;; gcd.sym_eq_gcd_aux_body_O, catalog title "gcd.sym_eq_gcd_aux_body_O": at
;; recursion index zero, the binary natural-number function returning its
;; first argument is Leibniz-equal to the auxiliary gcd body. This file
;; contains no proof.

(in-package "ACL2")

;; Reify the source's binary function values so ACL2 equality represents
;; Leibniz equality at the complete function type.

(defstub logipedia-gcd-sym-eq-gcd-aux-body-o-gcd-aux-body
  (index)
  t)

(defstub logipedia-gcd-sym-eq-gcd-aux-body-o-generic-apply
  (function-value first second)
  t)

(defun logipedia-gcd-sym-eq-gcd-aux-body-o-first-projection ()
  'logipedia-gcd-sym-eq-gcd-aux-body-o-first-projection)

(defun logipedia-gcd-sym-eq-gcd-aux-body-o-apply
    (function-value first second)
  (if
      (equal
       function-value
       (logipedia-gcd-sym-eq-gcd-aux-body-o-first-projection))
      (nfix first)
    (logipedia-gcd-sym-eq-gcd-aux-body-o-generic-apply
     function-value first second)))

(defun-sk logipedia-gcd-sym-eq-gcd-aux-body-o-function-value-p
    (function-value)
  (forall (first second)
    (implies
     (and
      (natp first)
      (natp second))
     (natp
      (logipedia-gcd-sym-eq-gcd-aux-body-o-apply
       function-value first second)))))

(defun-sk logipedia-gcd-sym-eq-gcd-aux-body-o-gcd-aux-body-typed-p ()
  (forall (index)
    (implies
     (natp index)
     (logipedia-gcd-sym-eq-gcd-aux-body-o-function-value-p
      (logipedia-gcd-sym-eq-gcd-aux-body-o-gcd-aux-body index)))))

(defun logipedia-gcd-sym-eq-gcd-aux-body-o-statement ()
  (implies
   (logipedia-gcd-sym-eq-gcd-aux-body-o-gcd-aux-body-typed-p)
   (equal
    (logipedia-gcd-sym-eq-gcd-aux-body-o-first-projection)
    (logipedia-gcd-sym-eq-gcd-aux-body-o-gcd-aux-body 0))))

(value-triple :itpeval-statement-checked)
:q
