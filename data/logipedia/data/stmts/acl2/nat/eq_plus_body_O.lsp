;; Statement-only formalization of Logipedia corpus artifact
;; nat.eq_plus_body_O, catalog title "nat.eq_plus_body_O": the natural
;; addition body at zero is Leibniz-equal to the identity function on natural
;; numbers. This file contains no proof.

(in-package "ACL2")

;; This is the full natural addition body: zero returns the second argument,
;; and each successor of the first argument adds one recursive successor.

(defun logipedia-nat-eq-plus-body-o-plus-body (left right)
  (if (zp left)
      right
    (1+
     (logipedia-nat-eq-plus-body-o-plus-body
      (1- left)
      right))))

;; Leibniz equality at source function type nat -> nat is rendered as equality
;; at every argument in the complete, unbounded natural domain.

(defun-sk logipedia-nat-eq-plus-body-o-statement ()
  (forall (m)
    (implies
     (natp m)
     (equal
      (logipedia-nat-eq-plus-body-o-plus-body 0 m)
      m))))

(value-triple :itpeval-statement-checked)
:q
