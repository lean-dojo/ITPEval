;; Statement-only formalization of Logipedia corpus artifact nat.nat_case,
;; catalog title "nat.nat_case": the zero and successor cases for an
;; arbitrary proposition-valued predicate imply that predicate at every
;; natural number. This file contains no proof.

(in-package "ACL2")

;; This conservative interface represents the source's arbitrary predicate
;; nat -> Prop. Its use in Boolean positions imposes no additional law.
(defstub logipedia-nat-nat-case-predicate (natural-value) t)

(defun-sk logipedia-nat-nat-case-successor-case-p (n)
  (forall (m)
    (implies
     (natp m)
     (implies
      (equal n (+ 1 m))
      (logipedia-nat-nat-case-predicate (+ 1 m))))))

(defun-sk logipedia-nat-nat-case-statement ()
  (forall (n)
    (implies
     (natp n)
     (implies
      (implies
       (equal n 0)
       (logipedia-nat-nat-case-predicate 0))
      (implies
       (logipedia-nat-nat-case-successor-case-p n)
       (logipedia-nat-nat-case-predicate n))))))

(value-triple :itpeval-statement-checked)
:q
