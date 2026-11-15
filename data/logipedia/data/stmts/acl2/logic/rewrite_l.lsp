;; Statement-only formalization of Logipedia corpus artifact logic.rewrite_l,
;; catalog title "logic.rewrite_l": the logic module's abstract polymorphic
;; equality transports every predicate from an element to an equal element.
;; This file contains no proof.

(in-package "ACL2")

;; For elements x and y of one carrier, transport from P(x) to P(y) for every
;; predicate P is bidirectionally equivalent to native identity: identity
;; transports every predicate, while the converse follows by choosing the
;; predicate that holds exactly at x. Thus the universal predicate quantifier
;; is preserved exactly rather than restricted to a fixed family.

(defstub logipedia-logic-rewrite-l-member-p
  (a-type value)
  t)

(defstub logipedia-logic-rewrite-l-source-equal-p
  (a-type left right)
  t)

(defun-sk logipedia-logic-rewrite-l-statement ()
  (forall (a-type x y)
    (implies
     (and
      (logipedia-logic-rewrite-l-member-p a-type x)
      (logipedia-logic-rewrite-l-member-p a-type y))
     (implies
      (logipedia-logic-rewrite-l-source-equal-p a-type x y)
      (equal x y)))))

(value-triple :itpeval-statement-checked)
:q
