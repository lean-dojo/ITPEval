;; Statement-only formalization of Logipedia corpus artifact logic.sym_eq,
;; catalog title "logic.sym_eq": the logic module's abstract polymorphic
;; equality is symmetric on every type. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify arbitrary source types, their carriers, and
;; the logic module's fixed abstract equality relation. Type tags and typed
;; elements remain universally quantified in the statement below.
(defstub logipedia-logic-sym-eq-member-p
  (a-type value)
  t)

(defstub logipedia-logic-sym-eq-source-equal-p
  (a-type left right)
  t)

(defun-sk logipedia-logic-sym-eq-statement ()
  (forall (a-type x y)
    (implies
     (and
      (logipedia-logic-sym-eq-member-p a-type x)
      (logipedia-logic-sym-eq-member-p a-type y))
     (implies
      (logipedia-logic-sym-eq-source-equal-p a-type x y)
      (logipedia-logic-sym-eq-source-equal-p a-type y x)))))

(value-triple :itpeval-statement-checked)
:q
