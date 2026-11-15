;; Statement-only formalization of Logipedia corpus artifact
;; nat.sym_eq_times_body_S, catalog title "nat.sym_eq_times_body_S": for every
;; natural number n, the function mapping m to plus m (times n m) is
;; Leibniz-equal at the unary natural-number function type to the
;; multiplication body at the successor of n. This file contains no proof.

(in-package "ACL2")

;; TIMES-BODY-AT reifies the curried source constant
;; times_body : nat -> (nat -> nat). Function values remain unrestricted ACL2
;; objects, with GENERIC-APPLICATION supplying application outside the lambda
;; family defined below.

(defstub logipedia-nat-sym-eq-times-body-s-plus
  (left right)
  t)

(defstub logipedia-nat-sym-eq-times-body-s-times
  (left right)
  t)

(defstub logipedia-nat-sym-eq-times-body-s-times-body-at
  (n)
  t)

(defstub logipedia-nat-sym-eq-times-body-s-generic-application
  (function-object argument)
  t)

;; This tagged value reifies the source lambda
;; fun m : nat => plus m (times n m), retaining its captured natural n.

(defun logipedia-nat-sym-eq-times-body-s-plus-times-function (n)
  (list :logipedia-nat-sym-eq-times-body-s-plus-times-function n))

(defun logipedia-nat-sym-eq-times-body-s-application
    (function-object argument)
  (if
      (and
       (true-listp function-object)
       (equal (len function-object) 2)
       (equal
        (car function-object)
        :logipedia-nat-sym-eq-times-body-s-plus-times-function))
      (logipedia-nat-sym-eq-times-body-s-plus
       argument
       (logipedia-nat-sym-eq-times-body-s-times
        (cadr function-object)
        argument))
    (logipedia-nat-sym-eq-times-body-s-generic-application
     function-object argument)))

(defun-sk logipedia-nat-sym-eq-times-body-s-plus-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-sym-eq-times-body-s-plus left right)))))

(defun-sk logipedia-nat-sym-eq-times-body-s-times-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-sym-eq-times-body-s-times left right)))))

(defun-sk logipedia-nat-sym-eq-times-body-s-natural-function-p
    (function-object)
  (forall (m)
    (implies
     (natp m)
     (natp
      (logipedia-nat-sym-eq-times-body-s-application
       function-object m)))))

(defun-sk logipedia-nat-sym-eq-times-body-s-times-body-typed-p ()
  (forall (n)
    (implies
     (natp n)
     (logipedia-nat-sym-eq-times-body-s-natural-function-p
      (logipedia-nat-sym-eq-times-body-s-times-body-at n)))))

;; ACL2 object identity directly represents Leibniz equality at the complete
;; source function type nat -> nat.

(defun-sk logipedia-nat-sym-eq-times-body-s-leibniz-p ()
  (forall (n)
    (implies
     (natp n)
     (equal
      (logipedia-nat-sym-eq-times-body-s-plus-times-function n)
      (logipedia-nat-sym-eq-times-body-s-times-body-at (+ n 1))))))

(defun logipedia-nat-sym-eq-times-body-s-statement ()
  (implies
   (and
    (logipedia-nat-sym-eq-times-body-s-plus-typed-p)
    (logipedia-nat-sym-eq-times-body-s-times-typed-p)
    (logipedia-nat-sym-eq-times-body-s-times-body-typed-p))
   (logipedia-nat-sym-eq-times-body-s-leibniz-p)))

(value-triple :itpeval-statement-checked)
:q
