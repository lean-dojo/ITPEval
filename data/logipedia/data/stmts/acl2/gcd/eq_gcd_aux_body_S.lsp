;; Statement-only formalization of Logipedia corpus artifact
;; gcd.eq_gcd_aux_body_S, catalog title "gcd.eq_gcd_aux_body_S": at every
;; successor recursion index, the auxiliary gcd body is Leibniz-equal at its
;; binary natural-number function type to the branch that returns the divisor
;; when it divides the dividend and otherwise recurses on the corresponding
;; remainder. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's natural-valued auxiliary gcd
;; function and its body, whose values are binary natural-number functions.

(defstub logipedia-gcd-eq-gcd-aux-body-s-gcd-aux
  (index first second)
  t)

(defstub logipedia-gcd-eq-gcd-aux-body-s-gcd-aux-body
  (index)
  t)

(defstub logipedia-gcd-eq-gcd-aux-body-s-generic-apply
  (function-value first second)
  t)

;; The source remainder is totalized by mod(m, 0) = m.

(defun logipedia-gcd-eq-gcd-aux-body-s-mod
    (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (mod (nfix dividend) (nfix divisor))))

(defun logipedia-gcd-eq-gcd-aux-body-s-dividesb
    (divisor dividend)
  (equal
   (logipedia-gcd-eq-gcd-aux-body-s-mod
    dividend divisor)
   0))

(defun logipedia-gcd-eq-gcd-aux-body-s-step-function (index)
  (list 'logipedia-gcd-eq-gcd-aux-body-s-step-function index))

(defun logipedia-gcd-eq-gcd-aux-body-s-step-function-p
    (function-value)
  (and
   (consp function-value)
   (equal
    (car function-value)
    'logipedia-gcd-eq-gcd-aux-body-s-step-function)
   (consp (cdr function-value))
   (natp (cadr function-value))
   (equal (cddr function-value) nil)))

(defun logipedia-gcd-eq-gcd-aux-body-s-apply
    (function-value dividend divisor)
  (if
      (logipedia-gcd-eq-gcd-aux-body-s-step-function-p
       function-value)
      (let ((index (cadr function-value)))
        (if
         (logipedia-gcd-eq-gcd-aux-body-s-dividesb
          divisor dividend)
         (nfix divisor)
         (logipedia-gcd-eq-gcd-aux-body-s-gcd-aux
          index
          (nfix divisor)
          (logipedia-gcd-eq-gcd-aux-body-s-mod
           dividend divisor))))
    (logipedia-gcd-eq-gcd-aux-body-s-generic-apply
     function-value dividend divisor)))

(defun-sk logipedia-gcd-eq-gcd-aux-body-s-gcd-aux-typed-p ()
  (forall (index first second)
    (implies
     (and
      (natp index)
      (natp first)
      (natp second))
     (natp
      (logipedia-gcd-eq-gcd-aux-body-s-gcd-aux
       index first second)))))

(defun-sk logipedia-gcd-eq-gcd-aux-body-s-function-value-p
    (function-value)
  (forall (first second)
    (implies
     (and
      (natp first)
      (natp second))
     (natp
      (logipedia-gcd-eq-gcd-aux-body-s-apply
       function-value first second)))))

(defun-sk logipedia-gcd-eq-gcd-aux-body-s-gcd-aux-body-typed-p ()
  (forall (index)
    (implies
     (natp index)
     (logipedia-gcd-eq-gcd-aux-body-s-function-value-p
      (logipedia-gcd-eq-gcd-aux-body-s-gcd-aux-body index)))))

;; Equality of the reified function values is Leibniz equality at the complete
;; source binary-function type, rather than merely pointwise equality.

(defun-sk logipedia-gcd-eq-gcd-aux-body-s-leibniz-p ()
  (forall (index)
    (implies
     (natp index)
     (equal
      (logipedia-gcd-eq-gcd-aux-body-s-gcd-aux-body
       (+ 1 index))
      (logipedia-gcd-eq-gcd-aux-body-s-step-function index)))))

(defun logipedia-gcd-eq-gcd-aux-body-s-statement ()
  (implies
   (and
    (logipedia-gcd-eq-gcd-aux-body-s-gcd-aux-typed-p)
    (logipedia-gcd-eq-gcd-aux-body-s-gcd-aux-body-typed-p))
   (logipedia-gcd-eq-gcd-aux-body-s-leibniz-p)))

(value-triple :itpeval-statement-checked)
:q
