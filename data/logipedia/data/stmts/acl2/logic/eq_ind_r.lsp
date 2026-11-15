;; Statement-only formalization of Logipedia corpus artifact logic.eq_ind_r,
;; catalog title "logic.eq_ind_r": the logic module's abstract polymorphic
;; equality supports right-oriented substitution in every predicate. This file
;; contains no proof.

(in-package "ACL2")

;; For elements x and a of one carrier, the source statement
;; forall P, P(a) -> (source-equal(x,a) -> P(x)) is bidirectionally equivalent
;; to source-equal(x,a) -> x = a. The forward direction chooses P(z) to mean
;; z = a; the reverse direction uses identity substitution. Thus the universal
;; predicate quantifier is preserved exactly rather than restricted to a fixed
;; collection of predicates.

(defstub logipedia-logic-eq-ind-r-member-p
  (a-type value)
  t)

(defstub logipedia-logic-eq-ind-r-source-equal-p
  (a-type left right)
  t)

(defun-sk logipedia-logic-eq-ind-r-statement ()
  (forall (a-type a x)
    (implies
     (and
      (logipedia-logic-eq-ind-r-member-p a-type a)
      (logipedia-logic-eq-ind-r-member-p a-type x))
     (implies
      (logipedia-logic-eq-ind-r-source-equal-p a-type x a)
      (equal x a)))))

(value-triple :itpeval-statement-checked)
:q
