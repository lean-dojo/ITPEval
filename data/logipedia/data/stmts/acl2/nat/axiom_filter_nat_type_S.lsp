;; Statement-only formalization of Logipedia corpus artifact
;; nat.axiom_filter_nat_type_S, catalog title
;; "nat.axiom_filter_nat_type_S": for every return type, every function from
;; natural numbers to that type, and every natural number, the polymorphic
;; natural-number filter at its successor equals the function's value at that
;; successor. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify every type and function parameter as an ACL2
;; object. SOURCE-EQUAL-P remains the source module's fixed opaque equality;
;; this axiom must not replace it with ACL2 identity.

(defstub logipedia-nat-filter-s-source-equal-p
  (return-type left right)
  t)

(defstub logipedia-nat-filter-s-function-at
  (return-type return-function natural)
  t)

(defstub logipedia-nat-filter-s-filter
  (return-type return-function natural)
  t)

(defun-sk logipedia-nat-axiom-filter-type-s-statement ()
  (forall (return-type return-function natural)
    (logipedia-nat-filter-s-source-equal-p
     return-type
     (logipedia-nat-filter-s-filter
      return-type return-function (+ 1 (nfix natural)))
     (logipedia-nat-filter-s-function-at
      return-type return-function (+ 1 (nfix natural))))))

(value-triple :itpeval-statement-checked)
:q
