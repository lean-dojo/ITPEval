;; Statement-only formalization of Logipedia corpus artifact
;; nat.axiom_filter_nat_type_O, catalog title
;; "nat.axiom_filter_nat_type_O": for an arbitrary return type and arbitrary
;; function from natural numbers to that type, the polymorphic natural-number
;; filter at zero is related by the source's indexed equality to the function's
;; value at zero. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify every type and function parameter as an ACL2
;; object. SOURCE-EQUAL-P remains the source module's fixed opaque equality;
;; this axiom must not replace it with ACL2 identity.

(defstub logipedia-nat-filter-o-source-equal-p
  (return-type left right)
  t)

(defstub logipedia-nat-filter-o-function-at
  (return-type return-function natural)
  t)

(defstub logipedia-nat-filter-o-filter
  (return-type return-function natural)
  t)

(defun-sk logipedia-nat-axiom-filter-type-o-statement ()
  (forall (return-type return-function)
    (logipedia-nat-filter-o-source-equal-p
     return-type
     (logipedia-nat-filter-o-filter
      return-type return-function 0)
     (logipedia-nat-filter-o-function-at
      return-type return-function 0))))

(value-triple :itpeval-statement-checked)
:q
