;; Statement-only formalization of Logipedia corpus artifact logic.refl,
;; catalog title "logic.refl": for every type and every element of that type,
;; the logic module's abstract equality relates the element to itself. This
;; file contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify arbitrary source types, their carriers, and
;; the logic module's abstract equality. The type tag and element remain
;; universally quantified in the statement below.
(defstub logipedia-logic-refl-member-p
  (a-type value)
  t)

(defstub logipedia-logic-refl-source-equal-p
  (a-type left right)
  t)

(defun-sk logipedia-logic-refl-statement ()
  (forall (a-type x)
    (implies
     (logipedia-logic-refl-member-p a-type x)
     (logipedia-logic-refl-source-equal-p a-type x x))))

(value-triple :itpeval-statement-checked)
:q
