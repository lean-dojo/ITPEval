;; Statement-only formalization of Logipedia corpus artifact nat.le_ind,
;; catalog title "nat.le_ind": induction above an arbitrary natural lower
;; bound for a proposition-valued predicate. This file contains no proof.

(in-package "ACL2")

;; This conservative interface represents the source's arbitrary predicate
;; nat -> Prop. Its use in Boolean positions imposes no additional law.
(defstub logipedia-nat-le-ind-predicate (m) t)

(defun-sk logipedia-nat-le-ind-step-p (n)
  (forall (m)
    (implies
     (and
      (natp m)
      (<= n m)
      (logipedia-nat-le-ind-predicate m))
     (logipedia-nat-le-ind-predicate (+ 1 m)))))

(defun-sk logipedia-nat-le-ind-conclusion-p (n)
  (forall (m)
    (implies
     (and
      (natp m)
      (<= n m))
     (logipedia-nat-le-ind-predicate m))))

(defun-sk logipedia-nat-le-ind-statement ()
  (forall (n)
    (implies
     (natp n)
     (implies
      (logipedia-nat-le-ind-predicate n)
      (implies
       (logipedia-nat-le-ind-step-p n)
       (logipedia-nat-le-ind-conclusion-p n))))))

(value-triple :itpeval-statement-checked)
:q
