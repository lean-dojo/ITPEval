;; Statement-only formalization of Logipedia corpus artifact
;; nat.sym_eq_minus_body_S, catalog title "nat.sym_eq_minus_body_S": for every
;; natural number, the function that returns its successor at zero and
;; subtracts the predecessor at successor inputs is Leibniz-equal to the
;; subtraction body at that successor. This file contains no proof.

(in-package "ACL2")

;; MINUS-BODY-AT reifies the curried source constant
;; minus_body : nat -> (nat -> nat). GENERIC-APPLICATION conservatively
;; supplies application for function objects not constructed in this file.

(defstub logipedia-nat-sym-eq-minus-body-s-minus
  (left right)
  t)

(defstub logipedia-nat-sym-eq-minus-body-s-minus-body-at
  (n)
  t)

(defstub logipedia-nat-sym-eq-minus-body-s-generic-application
  (function-object argument)
  t)

;; This reified value is exactly the source lambda
;; fun m => match_nat_type nat (S n) (fun q => minus n q) m.

(defun logipedia-nat-sym-eq-minus-body-s-successor-function (n)
  (list 'logipedia-nat-sym-eq-minus-body-s-successor-function n))

(defun logipedia-nat-sym-eq-minus-body-s-successor-function-p
    (function-object)
  (and
   (consp function-object)
   (equal
    (car function-object)
    'logipedia-nat-sym-eq-minus-body-s-successor-function)
   (consp (cdr function-object))
   (natp (cadr function-object))
   (equal (cddr function-object) nil)))

(defun logipedia-nat-sym-eq-minus-body-s-application
    (function-object argument)
  (if
      (logipedia-nat-sym-eq-minus-body-s-successor-function-p
       function-object)
      (let ((n (cadr function-object)))
        (if (equal argument 0)
            (+ n 1)
          (logipedia-nat-sym-eq-minus-body-s-minus
           n (- argument 1))))
    (logipedia-nat-sym-eq-minus-body-s-generic-application
     function-object argument)))

(defun-sk logipedia-nat-sym-eq-minus-body-s-minus-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-sym-eq-minus-body-s-minus left right)))))

(defun-sk logipedia-nat-sym-eq-minus-body-s-natural-function-p
    (function-object)
  (forall (m)
    (implies
     (natp m)
     (natp
      (logipedia-nat-sym-eq-minus-body-s-application
       function-object m)))))

(defun-sk logipedia-nat-sym-eq-minus-body-s-minus-body-typed-p ()
  (forall (n)
    (implies
     (natp n)
     (logipedia-nat-sym-eq-minus-body-s-natural-function-p
      (logipedia-nat-sym-eq-minus-body-s-minus-body-at n)))))

;; Leibniz equality, forall P, P(x) -> P(y), is equivalent to identity.
;; ACL2 object identity therefore represents equality at the complete source
;; function type without adding a function-extensionality assumption.

(defun-sk logipedia-nat-sym-eq-minus-body-s-equality-p ()
  (forall (n)
    (implies
     (natp n)
     (equal
      (logipedia-nat-sym-eq-minus-body-s-successor-function n)
      (logipedia-nat-sym-eq-minus-body-s-minus-body-at (+ n 1))))))

(defun logipedia-nat-sym-eq-minus-body-s-statement ()
  (implies
   (and
    (logipedia-nat-sym-eq-minus-body-s-minus-typed-p)
    (logipedia-nat-sym-eq-minus-body-s-minus-body-typed-p))
   (logipedia-nat-sym-eq-minus-body-s-equality-p)))

(value-triple :itpeval-statement-checked)
:q
