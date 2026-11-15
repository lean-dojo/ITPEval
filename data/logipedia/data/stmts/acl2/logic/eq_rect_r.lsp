;; Statement-only formalization of Logipedia corpus artifact logic.eq_rect_r,
;; catalog title "logic.eq_rect_r": the logic module's abstract polymorphic
;; equality supports right-oriented transport in every predicate. This file
;; contains no proof.

(in-package "ACL2")

;; For elements x and a of one carrier, the source statement
;; source-equal(x,a) -> forall P, P(a) -> P(x) is bidirectionally equivalent
;; to source-equal(x,a) -> x = a. The forward direction chooses P(z) to mean
;; z = a; the reverse direction uses identity substitution. Thus the universal
;; predicate quantifier is preserved exactly rather than restricted to a fixed
;; collection of predicates.

(defstub logipedia-logic-eq-rect-r-member-p
  (a-type value)
  t)

(defstub logipedia-logic-eq-rect-r-source-equal-p
  (a-type left right)
  t)

(defun-sk logipedia-logic-eq-rect-r-statement ()
  (forall (a-type a x)
    (implies
     (and
      (logipedia-logic-eq-rect-r-member-p a-type a)
      (logipedia-logic-eq-rect-r-member-p a-type x))
     (implies
      (logipedia-logic-eq-rect-r-source-equal-p a-type x a)
      (equal x a)))))

(value-triple :itpeval-statement-checked)
:q
