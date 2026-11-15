;; Statement-only formalization of Logipedia corpus artifact logic.eq_ind,
;; catalog title "logic.eq_ind": the logic module's abstract polymorphic
;; equality supports substitution in every predicate. This file contains no
;; proof.

(in-package "ACL2")

;; For elements x and y of one carrier, transport from P(x) to P(y) for every
;; predicate P is bidirectionally equivalent to native identity: identity
;; transports every predicate, while the converse follows by choosing the
;; predicate that holds exactly at x. Thus the source axiom is represented
;; exactly by requiring the abstract equality relation to imply ACL2 EQUAL.

(defstub logipedia-logic-eq-ind-member-p
  (a-type value)
  t)

(defstub logipedia-logic-eq-ind-source-equal-p
  (a-type left right)
  t)

(defun-sk logipedia-logic-eq-ind-statement ()
  (forall (a-type x y)
    (implies
     (and
      (logipedia-logic-eq-ind-member-p a-type x)
      (logipedia-logic-eq-ind-member-p a-type y))
     (implies
      (logipedia-logic-eq-ind-source-equal-p a-type x y)
      (equal x y)))))

(value-triple :itpeval-statement-checked)
:q
