;; Statement-only formalization of Logipedia corpus artifact logic.rewrite_r,
;; catalog title "logic.rewrite_r": the logic module's abstract polymorphic
;; equality transports every predicate from x to y when y is equal to x.
;; This file contains no proof.

(in-package "ACL2")

;; For elements x and y of one carrier, the source statement
;; forall P, P(x) -> (source-equal(y,x) -> P(y)) is bidirectionally equivalent
;; to source-equal(y,x) -> y = x. The forward direction chooses P(z) to mean
;; z = x; the reverse direction uses identity substitution. Thus the universal
;; predicate quantifier is preserved exactly rather than restricted to a fixed
;; family.

(defstub logipedia-logic-rewrite-r-member-p
  (a-type value)
  t)

(defstub logipedia-logic-rewrite-r-source-equal-p
  (a-type left right)
  t)

(defun-sk logipedia-logic-rewrite-r-statement ()
  (forall (a-type x y)
    (implies
     (and
      (logipedia-logic-rewrite-r-member-p a-type x)
      (logipedia-logic-rewrite-r-member-p a-type y))
     (implies
      (logipedia-logic-rewrite-r-source-equal-p a-type y x)
      (equal y x)))))

(value-triple :itpeval-statement-checked)
:q
