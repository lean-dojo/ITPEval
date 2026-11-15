;; Statement-only formalization of Logipedia corpus artifact nat.eq_plus,
;; catalog title "nat.eq_plus": for every natural number, the natural
;; addition function is Leibniz-equal to its natural-filtered body.
;; This file contains no proof.

(in-package "ACL2")

;; The two interfaces represent plus and the fixed composite
;; filter_nat_type(plus_body). ACL2 is first order, so their function-valued
;; Leibniz equality is stated pointwise.
(defstub logipedia-nat-eq-plus-raw
  (left right)
  t)

(defstub logipedia-nat-eq-plus-filtered-body-raw
  (left right)
  t)

(defun logipedia-nat-eq-plus (left right)
  (nfix
   (logipedia-nat-eq-plus-raw
    (nfix left)
    (nfix right))))

(defun logipedia-nat-eq-plus-filtered-body (left right)
  (nfix
   (logipedia-nat-eq-plus-filtered-body-raw
    (nfix left)
    (nfix right))))

(defun-sk logipedia-nat-eq-plus-statement ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (equal
      (logipedia-nat-eq-plus left right)
      (logipedia-nat-eq-plus-filtered-body left right)))))

(value-triple :itpeval-statement-checked)
:q
