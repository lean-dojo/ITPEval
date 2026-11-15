;; Statement-only formalization of Logipedia corpus artifact logic.sym_not_eq,
;; catalog title "logic.sym_not_eq": for every type and two of its elements,
;; negated equality is symmetric. This file contains no proof.

(in-package "ACL2")

;; ACL2 objects reify source types and elements, with membership relativizing
;; the element quantifiers to each carrier. The source equality is
;; bidirectionally equivalent to native identity: eq_ind with the predicate
;; (lambda (z) x = z) gives source-eq(x,y) -> x = y, while native substitution
;; and source reflexivity give x = y -> source-eq(x,y).
;;
;; The source Not P is likewise equivalent to native negation. Not_ind,
;; instantiated with Q = (P -> source-False), gives Not P -> (P ->
;; source-False), and nmk gives the converse. Source False is equivalent to
;; falsity because its elimination law specializes to native false, while
;; native false eliminates into source False. Thus the normalized Boolean body
;; below is bidirectionally equivalent to the source proposition.
(defstub logipedia-logic-sym-not-eq-member-p
  (a-type value)
  t)

(defun-sk logipedia-logic-sym-not-eq-statement ()
  (forall (a-type x y)
    (implies
     (and
      (logipedia-logic-sym-not-eq-member-p a-type x)
      (logipedia-logic-sym-not-eq-member-p a-type y))
     (implies
      (not (equal x y))
      (not (equal y x))))))

(value-triple :itpeval-statement-checked)
:q
