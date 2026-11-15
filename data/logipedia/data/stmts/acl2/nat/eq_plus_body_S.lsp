;; Statement-only formalization of Logipedia corpus artifact
;; nat.eq_plus_body_S, catalog title "nat.eq_plus_body_S": for every natural
;; number, the addition body at its successor is Leibniz-equal to the function
;; mapping each natural argument to the successor of their sum. This file
;; contains no proof.

(in-package "ACL2")

;; PLUS-BODY-AT reifies the curried source constant
;; plus_body : nat -> (nat -> nat). Function values remain unrestricted ACL2
;; objects, with GENERIC-APPLICATION supplying application outside the lambda
;; family defined below.

(defstub logipedia-nat-eq-plus-body-s-plus
  (left right)
  t)

(defun logipedia-nat-eq-plus-body-s-plus-value (left right)
  (nfix
   (logipedia-nat-eq-plus-body-s-plus left right)))

(defstub logipedia-nat-eq-plus-body-s-plus-body-at
  (n)
  t)

(defstub logipedia-nat-eq-plus-body-s-generic-application
  (function-object argument)
  t)

;; This tagged value reifies the source lambda
;; fun m : nat => S (plus n m), retaining its captured natural n.

(defun logipedia-nat-eq-plus-body-s-successor-plus-function (n)
  (list :logipedia-nat-eq-plus-body-s-successor-plus-function n))

(defun logipedia-nat-eq-plus-body-s-application
    (function-object argument)
  (if
      (and
       (true-listp function-object)
       (equal (len function-object) 2)
       (equal
        (car function-object)
        :logipedia-nat-eq-plus-body-s-successor-plus-function))
      (+
       (logipedia-nat-eq-plus-body-s-plus-value
        (cadr function-object)
        argument)
       1)
    (logipedia-nat-eq-plus-body-s-generic-application
     function-object argument)))

;; ACL2 object identity directly represents Leibniz equality at the complete
;; source function type nat -> nat.

(defun-sk logipedia-nat-eq-plus-body-s-leibniz-p ()
  (forall (n)
    (implies
     (natp n)
     (equal
      (logipedia-nat-eq-plus-body-s-plus-body-at (+ n 1))
      (logipedia-nat-eq-plus-body-s-successor-plus-function n)))))

(defun logipedia-nat-eq-plus-body-s-statement ()
  (logipedia-nat-eq-plus-body-s-leibniz-p))

(value-triple :itpeval-statement-checked)
:q
