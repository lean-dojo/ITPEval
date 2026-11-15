;; Statement-only formalization of Logipedia corpus artifact nat.sym_eq_plus,
;; catalog title "nat.sym_eq_plus": for every natural number, the
;; natural-filtered addition body is Leibniz-equal to the natural addition
;; function. This file contains no proof.

(in-package "ACL2")

;; The two interfaces represent plus and the fixed composite
;; filter_nat_type(plus_body). ACL2 is first order, so their function-valued
;; Leibniz equality is stated pointwise.

(defstub logipedia-nat-sym-eq-plus-raw
  (left right)
  t)

(defstub logipedia-nat-sym-eq-plus-filtered-body-raw
  (left right)
  t)

(defun logipedia-nat-sym-eq-plus (left right)
  (nfix
   (logipedia-nat-sym-eq-plus-raw
    (nfix left)
    (nfix right))))

(defun logipedia-nat-sym-eq-plus-filtered-body (left right)
  (nfix
   (logipedia-nat-sym-eq-plus-filtered-body-raw
    (nfix left)
    (nfix right))))
(defun-sk logipedia-nat-sym-eq-plus-statement ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (equal
      (logipedia-nat-sym-eq-plus-filtered-body left right)
      (logipedia-nat-sym-eq-plus left right)))))

(value-triple :itpeval-statement-checked)
:q
