;; Statement-only formalization of Logipedia corpus artifact
;; nat.eq_filter_nat_type_O, catalog title "nat.eq_filter_nat_type_O": for
;; every return type and every function from natural numbers to that type,
;; the polymorphic natural-number filter at zero is Leibniz-equal to the
;; function's value at zero. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify every function parameter as an ACL2 object
;; with a total application operation and retain the source return type as the
;; polymorphic filter's type index.

(defstub logipedia-nat-eq-filter-o-function-at
  (return-type return-function natural)
  t)

(defstub logipedia-nat-eq-filter-o-filter
  (return-type return-function natural)
  t)

;; Leibniz equality, forall P, P(x) -> P(y), is equivalent to identity:
;; identity transports every predicate, and the converse uses P(z) = (z = x).

(defun-sk logipedia-nat-eq-filter-type-o-statement ()
  (forall (return-type return-function)
    (equal
     (logipedia-nat-eq-filter-o-filter
      return-type return-function 0)
     (logipedia-nat-eq-filter-o-function-at
      return-type return-function 0))))

(value-triple :itpeval-statement-checked)
:q
