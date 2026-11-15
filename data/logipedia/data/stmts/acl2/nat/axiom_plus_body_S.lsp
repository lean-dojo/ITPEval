;; Statement-only formalization of Logipedia corpus artifact
;; nat.axiom_plus_body_S, catalog title "nat.axiom_plus_body_S": at every
;; natural successor, the addition body is extensionally equal to successor
;; composed with natural addition. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's natural-valued binary functions.

(defstub logipedia-nat-axiom-plus-body-s-plus
  (left right)
  t)

(defstub logipedia-nat-axiom-plus-body-s
  (left right)
  t)

(defun-sk logipedia-nat-axiom-plus-body-s-plus-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-axiom-plus-body-s-plus left right)))))

(defun-sk logipedia-nat-axiom-plus-body-s-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-axiom-plus-body-s left right)))))

(defun-sk logipedia-nat-axiom-plus-body-s-pointwise-p ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (equal
      (logipedia-nat-axiom-plus-body-s (+ n 1) m)
      (+ (logipedia-nat-axiom-plus-body-s-plus n m) 1)))))

(defun logipedia-nat-axiom-plus-body-s-statement ()
  (implies
   (and
    (logipedia-nat-axiom-plus-body-s-plus-typed-p)
    (logipedia-nat-axiom-plus-body-s-typed-p))
   (logipedia-nat-axiom-plus-body-s-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
