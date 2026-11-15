;; Statement-only formalization of Logipedia corpus artifact
;; nat.eq_filter_nat_type_S, catalog title "nat.eq_filter_nat_type_S": for
;; every return type, every function from natural numbers to that type, and
;; every natural number, the polymorphic natural-number filter at its
;; successor is Leibniz-equal to the function's value at that successor.
;; This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify every function parameter as an ACL2 object
;; with a total application operation and retain the source return type as the
;; polymorphic filter's type index.

(defstub logipedia-nat-eq-filter-s-function-at
  (return-type return-function natural)
  t)

(defstub logipedia-nat-eq-filter-s-filter
  (return-type return-function natural)
  t)

;; NFIX is a surjective retraction onto the natural numbers, so universally
;; quantifying the term below is equivalent to quantifying its input over
;; naturals.  Leibniz equality is equivalent to identity: identity transports
;; every predicate, and the converse uses the predicate P(z) = (z = x).

(defun-sk logipedia-nat-eq-filter-type-s-statement ()
  (forall (return-type return-function natural)
    (equal
     (logipedia-nat-eq-filter-s-filter
      return-type return-function (+ (nfix natural) 1))
     (logipedia-nat-eq-filter-s-function-at
      return-type return-function (+ (nfix natural) 1)))))

(value-triple :itpeval-statement-checked)
:q
