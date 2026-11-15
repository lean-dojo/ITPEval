;; Statement-only formalization of Logipedia corpus artifact
;; nat.sym_eq_minus_body_O, catalog title "nat.sym_eq_minus_body_O": the
;; constant-zero function on natural numbers is Leibniz-equal to the natural
;; subtraction body at zero. This file contains no proof.

(in-package "ACL2")

;; On ACL2 naturals, O is 0 and S is addition by one. This definition mirrors
;; the source equations for minus_body: its zero branch is constantly zero,
;; while its successor branch returns the successor at zero and recursively
;; subtracts predecessors at successor inputs.
(defun logipedia-nat-sym-eq-minus-body-o-minus-body (n m)
  (if (zp n)
      0
    (if (zp m)
        n
      (logipedia-nat-sym-eq-minus-body-o-minus-body
       (- n 1)
       (- m 1)))))

;; Leibniz equality at the source function type nat -> nat is represented by
;; extensional equality at every natural-number argument, in the source order.
(defun-sk logipedia-nat-sym-eq-minus-body-o-statement ()
  (forall (m)
    (implies
     (natp m)
     (equal
      0
      (logipedia-nat-sym-eq-minus-body-o-minus-body 0 m)))))

(value-triple :itpeval-statement-checked)
:q
