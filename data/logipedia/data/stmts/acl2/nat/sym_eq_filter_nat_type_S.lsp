;; Statement-only formalization of Logipedia corpus artifact
;; nat.sym_eq_filter_nat_type_S, catalog title
;; "nat.sym_eq_filter_nat_type_S": for every return type, every function from
;; natural numbers to that type, and every natural number, the function's
;; value at the successor is Leibniz-equal to the polymorphic natural-number
;; filter at that successor. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify functions from naturals into arbitrary
;; return types and the source's fixed polymorphic filter.

(defstub logipedia-nat-sym-eq-filter-s-function-at
  (return-function natural)
  t)

(defstub logipedia-nat-sym-eq-filter-s-filter
  (return-type return-function natural)
  t)

;; Leibniz equality, forall P, P(x) -> P(y), is equivalent to identity:
;; identity transports every predicate, and the converse uses P(z) = (z = x).

(defun-sk logipedia-nat-sym-eq-filter-type-s-statement ()
  (forall (return-type return-function natural)
    (implies
     (natp natural)
     (equal
      (logipedia-nat-sym-eq-filter-s-function-at
       return-function (+ natural 1))
      (logipedia-nat-sym-eq-filter-s-filter
       return-type return-function (+ natural 1))))))

(value-triple :itpeval-statement-checked)
:q
