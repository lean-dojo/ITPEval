;; Statement-only formalization of Logipedia corpus artifact
;; nat.sym_eq_times_body_O, catalog title "nat.sym_eq_times_body_O": the
;; constant-zero function on natural numbers is Leibniz-equal to the natural
;; multiplication body at zero. This file contains no proof.

(in-package "ACL2")

;; On ACL2 naturals, O is 0 and S is addition by one. This recursive
;; definition mirrors the source multiplication body: the zero branch is
;; constantly zero, and a successor branch adds the multiplier to the
;; preceding multiplication value.
(defun logipedia-nat-sym-eq-times-body-o-times-body (n m)
  (if (zp n)
      0
    (+
     (nfix m)
     (logipedia-nat-sym-eq-times-body-o-times-body
      (- n 1)
      m))))

;; For these concretely defined natural functions, pointwise equality on the
;; complete natural domain is definitionally equivalent to the displayed
;; Leibniz equality at source function type nat -> nat.
(defun-sk logipedia-nat-sym-eq-times-body-o-statement ()
  (forall (m)
    (implies
     (natp m)
     (equal
      0
      (logipedia-nat-sym-eq-times-body-o-times-body 0 m)))))

(value-triple :itpeval-statement-checked)
:q
