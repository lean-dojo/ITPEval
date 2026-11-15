;; Statement-only formalization of Logipedia corpus artifact
;; gcd.eq_gcd_aux, catalog title "gcd.eq_gcd_aux": for every natural recursion
;; index, the auxiliary gcd function is Leibniz-equal to its natural-filtered
;; body as a binary natural-number function. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's natural-valued functions.

(defstub logipedia-gcd-eq-gcd-aux
  (index first second)
  t)

(defstub logipedia-gcd-eq-gcd-aux-body
  (index first second)
  t)

;; On natural indices, the source module's filter_nat_type is extensionally
;; the identity. This helper makes that definitional encoding explicit.
(defun logipedia-gcd-eq-gcd-aux-filtered-body
    (index first second)
  (logipedia-gcd-eq-gcd-aux-body index first second))

(defun-sk logipedia-gcd-eq-gcd-aux-typed-p ()
  (forall (index first second)
    (implies
     (and
      (natp index)
      (natp first)
      (natp second))
     (natp
      (logipedia-gcd-eq-gcd-aux index first second)))))

(defun-sk logipedia-gcd-eq-gcd-aux-body-typed-p ()
  (forall (index first second)
    (implies
     (and
      (natp index)
      (natp first)
      (natp second))
     (natp
      (logipedia-gcd-eq-gcd-aux-body
       index first second)))))

(defun-sk logipedia-gcd-eq-gcd-aux-pointwise-p ()
  (forall (index first second)
    (implies
     (and
      (natp index)
      (natp first)
      (natp second))
     (equal
      (logipedia-gcd-eq-gcd-aux
       index first second)
      (logipedia-gcd-eq-gcd-aux-filtered-body
       index first second)))))

(defun logipedia-gcd-eq-gcd-aux-statement ()
  (implies
   (and
    (logipedia-gcd-eq-gcd-aux-typed-p)
    (logipedia-gcd-eq-gcd-aux-body-typed-p))
   (logipedia-gcd-eq-gcd-aux-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
