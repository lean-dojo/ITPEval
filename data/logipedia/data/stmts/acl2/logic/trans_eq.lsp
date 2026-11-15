;; Statement-only formalization of Logipedia corpus artifact logic.trans_eq,
;; catalog title "logic.trans_eq": the logic module's abstract polymorphic
;; equality is transitive on every type. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify arbitrary source types, their carriers, and
;; the logic module's fixed abstract equality relation. The type tag and all
;; three typed elements remain universally quantified in the statement below.
(defstub logipedia-logic-trans-eq-member-p
  (a-type value)
  t)

(defstub logipedia-logic-trans-eq-source-equal-p
  (a-type left right)
  t)

(defun-sk logipedia-logic-trans-eq-statement ()
  (forall (a-type x y z)
    (implies
     (and
      (logipedia-logic-trans-eq-member-p a-type x)
      (logipedia-logic-trans-eq-member-p a-type y)
      (logipedia-logic-trans-eq-member-p a-type z))
     (implies
      (logipedia-logic-trans-eq-source-equal-p a-type x y)
      (implies
       (logipedia-logic-trans-eq-source-equal-p a-type y z)
       (logipedia-logic-trans-eq-source-equal-p a-type x z))))))

(value-triple :itpeval-statement-checked)
:q
