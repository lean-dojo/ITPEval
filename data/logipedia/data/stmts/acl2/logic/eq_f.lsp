;; Statement-only formalization of Logipedia corpus artifact logic.eq_f,
;; catalog title "logic.eq_f": every function preserves the logic module's
;; abstract equality between elements of its source type. This file contains
;; no proof.

(in-package "ACL2")

;; Type tags and function values remain universally quantified. The
;; conservative interfaces below reify arbitrary source carriers, application,
;; and the module's fixed polymorphic equality relation.

(defstub logipedia-logic-eq-f-member-p
  (type value)
  t)

(defstub logipedia-logic-eq-f-apply
  (function argument)
  t)

(defstub logipedia-logic-eq-f-source-equal-p
  (type left right)
  t)

(defun-sk logipedia-logic-eq-f-function-p
    (a-type b-type function)
  (forall (argument)
    (implies
     (logipedia-logic-eq-f-member-p a-type argument)
     (logipedia-logic-eq-f-member-p
      b-type
      (logipedia-logic-eq-f-apply function argument)))))

(defun-sk logipedia-logic-eq-f-statement ()
  (forall (a-type b-type function x y)
    (implies
     (and
      (logipedia-logic-eq-f-function-p a-type b-type function)
      (logipedia-logic-eq-f-member-p a-type x)
      (logipedia-logic-eq-f-member-p a-type y))
     (implies
      (logipedia-logic-eq-f-source-equal-p a-type x y)
      (logipedia-logic-eq-f-source-equal-p
       b-type
       (logipedia-logic-eq-f-apply function x)
       (logipedia-logic-eq-f-apply function y))))))

(value-triple :itpeval-statement-checked)
:q
