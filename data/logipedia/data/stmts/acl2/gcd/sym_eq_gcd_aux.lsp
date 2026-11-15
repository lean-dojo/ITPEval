;; Statement-only formalization of Logipedia corpus artifact
;; gcd.sym_eq_gcd_aux, catalog title "gcd.sym_eq_gcd_aux": for every natural
;; recursion index, the natural-filtered auxiliary gcd body is Leibniz-equal
;; to the auxiliary gcd function as a binary natural-number function. This
;; file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's natural-valued functions.

(defstub logipedia-gcd-sym-eq-gcd-aux
  (index first second)
  t)

(defstub logipedia-gcd-sym-eq-gcd-aux-body
  (index first second)
  t)

;; On natural indices, the source module's filter_nat_type is extensionally
;; the identity. This helper makes that definitional encoding explicit.
(defun logipedia-gcd-sym-eq-gcd-aux-filtered-body
    (index first second)
  (logipedia-gcd-sym-eq-gcd-aux-body index first second))

(defun-sk logipedia-gcd-sym-eq-gcd-aux-typed-p ()
  (forall (index first second)
    (implies
     (and
      (natp index)
      (natp first)
      (natp second))
     (natp
      (logipedia-gcd-sym-eq-gcd-aux
       index first second)))))

(defun-sk logipedia-gcd-sym-eq-gcd-aux-body-typed-p ()
  (forall (index first second)
    (implies
     (and
      (natp index)
      (natp first)
      (natp second))
     (natp
      (logipedia-gcd-sym-eq-gcd-aux-body
       index first second)))))

(defun-sk logipedia-gcd-sym-eq-gcd-aux-pointwise-p ()
  (forall (index first second)
    (implies
     (and
      (natp index)
      (natp first)
      (natp second))
     (equal
      (logipedia-gcd-sym-eq-gcd-aux-filtered-body
       index first second)
      (logipedia-gcd-sym-eq-gcd-aux
       index first second)))))

(defun logipedia-gcd-sym-eq-gcd-aux-statement ()
  (implies
   (and
    (logipedia-gcd-sym-eq-gcd-aux-typed-p)
    (logipedia-gcd-sym-eq-gcd-aux-body-typed-p))
   (logipedia-gcd-sym-eq-gcd-aux-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
