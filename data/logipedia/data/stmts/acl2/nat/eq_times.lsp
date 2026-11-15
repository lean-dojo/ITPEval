;; Statement-only formalization of Logipedia corpus artifact nat.eq_times,
;; catalog title "nat.eq_times": for every natural number, the natural
;; multiplication function is Leibniz-equal to its natural-filtered body.
;; This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's natural-valued functions.

(defstub logipedia-nat-eq-times-at
  (n)
  t)

(defstub logipedia-nat-eq-times-body-at
  (n)
  t)

;; The source module's filter_nat_type is extensionally the identity on
;; natural indices. Function values are reified as ACL2 objects so native
;; object equality represents the source's Leibniz equality at nat -> nat.
(defun logipedia-nat-eq-times-filtered-body-at (n)
  (logipedia-nat-eq-times-body-at n))

(defun-sk logipedia-nat-eq-times-leibniz-p ()
  (forall (n)
    (implies
     (natp n)
     (equal
      (logipedia-nat-eq-times-at n)
      (logipedia-nat-eq-times-filtered-body-at n)))))

(defun logipedia-nat-eq-times-statement ()
  (logipedia-nat-eq-times-leibniz-p))

(value-triple :itpeval-statement-checked)
:q
