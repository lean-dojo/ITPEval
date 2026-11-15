;; Statement-only formalization of Logipedia corpus artifact
;; nat.axiom_times_body_S, catalog title "nat.axiom_times_body_S": for every
;; natural number, the multiplication body at its successor is extensionally
;; equal to the function sending m to plus m (times n m). This file contains
;; no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's natural-valued binary functions.

(defstub logipedia-nat-axiom-times-body-s-plus
  (left right)
  t)

(defstub logipedia-nat-axiom-times-body-s-times
  (left right)
  t)

(defstub logipedia-nat-axiom-times-body-s
  (left right)
  t)

;; This conservative predicate is the specific source proposition
;; connectives.equal (nat -> nat) (times_body (S n))
;;   (fun m => plus m (times n m)).

(defun-sk logipedia-nat-axiom-times-body-s-plus-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-axiom-times-body-s-plus left right)))))

(defun-sk logipedia-nat-axiom-times-body-s-times-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-axiom-times-body-s-times left right)))))

(defun-sk logipedia-nat-axiom-times-body-s-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-axiom-times-body-s left right)))))

(defun-sk logipedia-nat-axiom-times-body-s-pointwise-p ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (equal
      (logipedia-nat-axiom-times-body-s (+ n 1) m)
      (logipedia-nat-axiom-times-body-s-plus
       m
       (logipedia-nat-axiom-times-body-s-times n m))))))

(defun logipedia-nat-axiom-times-body-s-statement ()
  (implies
   (and
    (logipedia-nat-axiom-times-body-s-plus-typed-p)
    (logipedia-nat-axiom-times-body-s-times-typed-p)
    (logipedia-nat-axiom-times-body-s-typed-p))
   (logipedia-nat-axiom-times-body-s-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
