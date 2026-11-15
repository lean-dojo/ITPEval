;; Statement-only formalization of Logipedia corpus artifact
;; gcd.axiom_gcd_aux, catalog title "gcd.axiom_gcd_aux": for every natural
;; recursion index, the auxiliary gcd function is extensionally equal to its
;; natural-filtered body. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's natural-valued functions.

(defstub logipedia-gcd-axiom-gcd-aux
  (index first second)
  t)

(defstub logipedia-gcd-axiom-gcd-aux-body
  (index first second)
  t)

;; On natural indices, the source module's filter_nat_type is extensionally
;; the identity. This helper makes that definitional encoding explicit.
(defun logipedia-gcd-axiom-gcd-aux-filtered-body
    (index first second)
  (logipedia-gcd-axiom-gcd-aux-body index first second))

(defun-sk logipedia-gcd-axiom-gcd-aux-typed-p ()
  (forall (index first second)
    (implies
     (and
      (natp index)
      (natp first)
      (natp second))
     (natp
      (logipedia-gcd-axiom-gcd-aux index first second)))))

(defun-sk logipedia-gcd-axiom-gcd-aux-body-typed-p ()
  (forall (index first second)
    (implies
     (and
      (natp index)
      (natp first)
      (natp second))
     (natp
      (logipedia-gcd-axiom-gcd-aux-body
       index first second)))))

(defun-sk logipedia-gcd-axiom-gcd-aux-pointwise-p ()
  (forall (index first second)
    (implies
     (and
      (natp index)
      (natp first)
      (natp second))
     (equal
      (logipedia-gcd-axiom-gcd-aux
       index first second)
      (logipedia-gcd-axiom-gcd-aux-filtered-body
       index first second)))))

(defun logipedia-gcd-axiom-gcd-aux-statement ()
  (implies
   (and
    (logipedia-gcd-axiom-gcd-aux-typed-p)
    (logipedia-gcd-axiom-gcd-aux-body-typed-p))
   (logipedia-gcd-axiom-gcd-aux-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
