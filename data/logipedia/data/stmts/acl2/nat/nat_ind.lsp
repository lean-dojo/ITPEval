;; Statement-only formalization of Logipedia corpus artifact nat.nat_ind,
;; catalog title "nat.nat_ind": mathematical induction for an arbitrary
;; proposition-valued predicate on the natural numbers. This file contains no
;; proof.

(in-package "ACL2")

;; This conservative interface represents the source's arbitrary predicate
;; nat -> Prop. Its use in Boolean positions imposes no additional law.
(defstub logipedia-nat-nat-ind-predicate (x) t)

(defun-sk logipedia-nat-nat-ind-step-p ()
  (forall (x)
    (implies
     (and
      (natp x)
      (logipedia-nat-nat-ind-predicate x))
     (logipedia-nat-nat-ind-predicate (+ 1 x)))))

(defun-sk logipedia-nat-nat-ind-conclusion-p ()
  (forall (x)
    (implies
     (natp x)
     (logipedia-nat-nat-ind-predicate x))))

(defun logipedia-nat-nat-ind-statement ()
  (implies
   (logipedia-nat-nat-ind-predicate 0)
   (implies
    (logipedia-nat-nat-ind-step-p)
    (logipedia-nat-nat-ind-conclusion-p))))

(value-triple :itpeval-statement-checked)
:q
