;; Statement-only formalization of Logipedia corpus artifact
;; nat.sym_eq_filter_nat_type_O, catalog title
;; "nat.sym_eq_filter_nat_type_O": for every return type and every function
;; from natural numbers to that type, the function's value at zero is
;; Leibniz-equal to the polymorphic natural-number filter at zero. This file
;; contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify every function parameter as an ACL2 object
;; with a total application operation and retain the source return type as the
;; polymorphic filter's type index.

(defstub logipedia-nat-sym-eq-filter-o-function-at
  (return-function natural)
  t)

(defstub logipedia-nat-sym-eq-filter-o-filter
  (return-type return-function natural)
  t)

;; Leibniz equality, forall P, P(x) -> P(y), is equivalent to identity:
;; identity transports every predicate, and the converse uses P(z) = (z = x).

(defun-sk logipedia-nat-sym-eq-filter-type-o-statement ()
  (forall (return-type return-function)
    (equal
     (logipedia-nat-sym-eq-filter-o-function-at
      return-function 0)
     (logipedia-nat-sym-eq-filter-o-filter
      return-type return-function 0))))

(value-triple :itpeval-statement-checked)
:q
