;; Statement-only formalization of Logipedia corpus artifact logic.eq_f2,
;; catalog title "logic.eq_f2": every curried binary function preserves the
;; logic module's polymorphic equality in both arguments. This file contains
;; no proof.

(in-package "ACL2")

;; Type tags, function values, and arguments remain universally quantified.
;; The source equality has reflexivity and unrestricted predicate
;; substitution, so it is bidirectionally equivalent to identity: substitution
;; yields identity, and identity yields source equality by reflexivity. The
;; type-indexed wrapper below therefore represents it exactly with ACL2 EQUAL.

(defstub logipedia-logic-eq-f2-member-p
  (type value)
  t)

(defstub logipedia-logic-eq-f2-apply
  (function argument)
  t)

(defun logipedia-logic-eq-f2-source-equal-p
    (type left right)
  (declare (ignore type))
  (equal left right))

(defun-sk logipedia-logic-eq-f2-function-p
    (a-type b-type c-type function)
  (forall (x y)
    (implies
     (and
      (logipedia-logic-eq-f2-member-p a-type x)
      (logipedia-logic-eq-f2-member-p b-type y))
     (logipedia-logic-eq-f2-member-p
      c-type
      (logipedia-logic-eq-f2-apply
       (logipedia-logic-eq-f2-apply function x)
       y)))))

(defun-sk logipedia-logic-eq-f2-statement ()
  (forall (a-type b-type c-type function x1 x2 y1 y2)
    (implies
     (and
      (logipedia-logic-eq-f2-function-p
       a-type b-type c-type function)
      (logipedia-logic-eq-f2-member-p a-type x1)
      (logipedia-logic-eq-f2-member-p a-type x2)
      (logipedia-logic-eq-f2-member-p b-type y1)
      (logipedia-logic-eq-f2-member-p b-type y2))
     (implies
      (logipedia-logic-eq-f2-source-equal-p
       a-type x1 x2)
      (implies
       (logipedia-logic-eq-f2-source-equal-p
        b-type y1 y2)
       (logipedia-logic-eq-f2-source-equal-p
        c-type
        (logipedia-logic-eq-f2-apply
         (logipedia-logic-eq-f2-apply function x1)
         y1)
        (logipedia-logic-eq-f2-apply
         (logipedia-logic-eq-f2-apply function x2)
         y2)))))))

(value-triple :itpeval-statement-checked)
:q
