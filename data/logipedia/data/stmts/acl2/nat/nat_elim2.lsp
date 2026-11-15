;; Statement-only formalization of Logipedia corpus artifact nat.nat_elim2,
;; catalog title "nat.nat_elim2": two-variable induction on natural numbers
;; from the zero row, successor/zero column, and diagonal successor step.
;; This file contains no proof.

(in-package "ACL2")

;; This conservative interface represents the source's arbitrary relation
;; nat -> nat -> Prop. Its use in Boolean positions imposes no additional law.
(defstub logipedia-nat-nat-elim2-relation (n m) t)

(defun-sk logipedia-nat-nat-elim2-zero-row-p ()
  (forall (n)
    (implies
     (natp n)
     (logipedia-nat-nat-elim2-relation 0 n))))

(defun-sk logipedia-nat-nat-elim2-successor-zero-column-p ()
  (forall (n)
    (implies
     (natp n)
     (logipedia-nat-nat-elim2-relation (+ 1 n) 0))))

(defun-sk logipedia-nat-nat-elim2-diagonal-step-p ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (logipedia-nat-nat-elim2-relation n m))
     (logipedia-nat-nat-elim2-relation (+ 1 n) (+ 1 m)))))

(defun-sk logipedia-nat-nat-elim2-all-pairs-p ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (logipedia-nat-nat-elim2-relation n m))))

(defun logipedia-nat-nat-elim2-statement ()
  (implies
   (logipedia-nat-nat-elim2-zero-row-p)
   (implies
    (logipedia-nat-nat-elim2-successor-zero-column-p)
    (implies
     (logipedia-nat-nat-elim2-diagonal-step-p)
     (logipedia-nat-nat-elim2-all-pairs-p)))))

(value-triple :itpeval-statement-checked)
:q
