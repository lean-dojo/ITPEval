;; Statement-only formalization of Logipedia corpus artifact
;; bigops.mk_ACop, catalog title "bigops.mk_ACop": left and right identity,
;; associativity, and commutativity of an arbitrary binary operation imply
;; the source's opaque ACop predicate for its neutral element.
;; This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for arbitrary carriers and operation values, plus
;; the source module's single opaque ACop predicate.

(defstub logipedia-bigops-mk-acop-member-p (a-type value) t)

(defstub logipedia-bigops-mk-acop-operation
  (operation left right)
  t)

(defstub logipedia-bigops-mk-acop-p (a-type nil-value) t)

(defun-sk logipedia-bigops-mk-acop-binary-operation-p
    (a-type operation)
  (forall (left right)
    (implies
     (and
      (logipedia-bigops-mk-acop-member-p a-type left)
      (logipedia-bigops-mk-acop-member-p a-type right))
     (logipedia-bigops-mk-acop-member-p
      a-type
      (logipedia-bigops-mk-acop-operation
       operation left right)))))

(defun-sk logipedia-bigops-mk-acop-left-identity-p
    (a-type nil-value operation)
  (forall (a)
    (implies
     (logipedia-bigops-mk-acop-member-p a-type a)
     (equal
      (logipedia-bigops-mk-acop-operation
       operation nil-value a)
      a))))

(defun-sk logipedia-bigops-mk-acop-right-identity-p
    (a-type nil-value operation)
  (forall (a)
    (implies
     (logipedia-bigops-mk-acop-member-p a-type a)
     (equal
      (logipedia-bigops-mk-acop-operation
       operation a nil-value)
      a))))

(defun-sk logipedia-bigops-mk-acop-associative-p
    (a-type operation)
  (forall (a b c)
    (implies
     (and
      (logipedia-bigops-mk-acop-member-p a-type a)
      (logipedia-bigops-mk-acop-member-p a-type b)
      (logipedia-bigops-mk-acop-member-p a-type c))
     (equal
      (logipedia-bigops-mk-acop-operation
       operation
       a
       (logipedia-bigops-mk-acop-operation operation b c))
      (logipedia-bigops-mk-acop-operation
       operation
       (logipedia-bigops-mk-acop-operation operation a b)
       c)))))

(defun-sk logipedia-bigops-mk-acop-commutative-p
    (a-type operation)
  (forall (a b)
    (implies
     (and
      (logipedia-bigops-mk-acop-member-p a-type a)
      (logipedia-bigops-mk-acop-member-p a-type b))
     (equal
      (logipedia-bigops-mk-acop-operation operation a b)
      (logipedia-bigops-mk-acop-operation operation b a)))))

(defun-sk logipedia-bigops-mk-acop-statement ()
  (forall (a-type nil-value operation)
    (implies
     (and
      (logipedia-bigops-mk-acop-member-p a-type nil-value)
      (logipedia-bigops-mk-acop-binary-operation-p
       a-type operation)
      (logipedia-bigops-mk-acop-left-identity-p
       a-type nil-value operation)
      (logipedia-bigops-mk-acop-right-identity-p
       a-type nil-value operation)
      (logipedia-bigops-mk-acop-associative-p
       a-type operation)
      (logipedia-bigops-mk-acop-commutative-p
       a-type operation))
     (logipedia-bigops-mk-acop-p a-type nil-value))))

(value-triple :itpeval-statement-checked)
:q
