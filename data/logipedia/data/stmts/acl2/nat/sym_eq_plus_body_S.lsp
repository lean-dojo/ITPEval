;; Statement-only formalization of Logipedia corpus artifact
;; nat.sym_eq_plus_body_S, catalog title "nat.sym_eq_plus_body_S": for every
;; natural number, the function mapping each natural argument to the successor
;; of its sum with that number is Leibniz-equal to the addition body at the
;; number's successor. This file contains no proof.

(in-package "ACL2")

;; PLUS-BODY-AT reifies the curried source constant
;; plus_body : nat -> (nat -> nat). Function values remain unrestricted ACL2
;; objects, with GENERIC-APPLICATION supplying application outside the lambda
;; family defined below.

(defstub logipedia-nat-sym-eq-plus-body-s-plus
  (left right)
  t)

(defstub logipedia-nat-sym-eq-plus-body-s-plus-body-at
  (n)
  t)

(defstub logipedia-nat-sym-eq-plus-body-s-generic-application
  (function-object argument)
  t)

;; This tagged value reifies the source lambda
;; fun m : nat => S (plus n m), retaining its captured natural n.

(defun logipedia-nat-sym-eq-plus-body-s-successor-plus-function (n)
  (list :logipedia-nat-sym-eq-plus-body-s-successor-plus-function n))

(defun logipedia-nat-sym-eq-plus-body-s-application
    (function-object argument)
  (if
      (and
       (true-listp function-object)
       (equal (len function-object) 2)
       (equal
        (car function-object)
        :logipedia-nat-sym-eq-plus-body-s-successor-plus-function))
      (+
       (logipedia-nat-sym-eq-plus-body-s-plus
        (cadr function-object)
        argument)
       1)
    (logipedia-nat-sym-eq-plus-body-s-generic-application
     function-object argument)))

(defun-sk logipedia-nat-sym-eq-plus-body-s-plus-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-sym-eq-plus-body-s-plus left right)))))

(defun-sk logipedia-nat-sym-eq-plus-body-s-natural-function-p
    (function-object)
  (forall (m)
    (implies
     (natp m)
     (natp
      (logipedia-nat-sym-eq-plus-body-s-application
       function-object m)))))

(defun-sk logipedia-nat-sym-eq-plus-body-s-plus-body-typed-p ()
  (forall (n)
    (implies
     (natp n)
     (logipedia-nat-sym-eq-plus-body-s-natural-function-p
      (logipedia-nat-sym-eq-plus-body-s-plus-body-at n)))))

;; ACL2 object identity directly represents Leibniz equality at the complete
;; source function type nat -> nat.

(defun-sk logipedia-nat-sym-eq-plus-body-s-leibniz-p ()
  (forall (n)
    (implies
     (natp n)
     (equal
      (logipedia-nat-sym-eq-plus-body-s-successor-plus-function n)
      (logipedia-nat-sym-eq-plus-body-s-plus-body-at (+ n 1))))))

(defun logipedia-nat-sym-eq-plus-body-s-statement ()
  (implies
   (and
    (logipedia-nat-sym-eq-plus-body-s-plus-typed-p)
    (logipedia-nat-sym-eq-plus-body-s-plus-body-typed-p))
   (logipedia-nat-sym-eq-plus-body-s-leibniz-p)))

(value-triple :itpeval-statement-checked)
:q
