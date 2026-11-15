;; Statement-only formalization of Logipedia corpus artifact
;; bigops.mk_Aop, catalog title "bigops.mk_Aop": left and right identity
;; and associativity of an arbitrary binary operation imply the source's
;; opaque Aop predicate for its neutral element. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for arbitrary carriers and operation values, plus
;; the source module's single opaque Aop predicate.

(defstub logipedia-bigops-mk-aop-member-p (a-type value) t)

(defstub logipedia-bigops-mk-aop-operation
  (operation left right)
  t)

(defstub logipedia-bigops-mk-aop-p (a-type nil-value) t)

(defun-sk logipedia-bigops-mk-aop-binary-operation-p
    (a-type operation)
  (forall (left right)
    (implies
     (and
      (logipedia-bigops-mk-aop-member-p a-type left)
      (logipedia-bigops-mk-aop-member-p a-type right))
     (logipedia-bigops-mk-aop-member-p
      a-type
      (logipedia-bigops-mk-aop-operation
       operation left right)))))

(defun-sk logipedia-bigops-mk-aop-left-identity-p
    (a-type nil-value operation)
  (forall (a)
    (implies
     (logipedia-bigops-mk-aop-member-p a-type a)
     (equal
      (logipedia-bigops-mk-aop-operation
       operation nil-value a)
      a))))

(defun-sk logipedia-bigops-mk-aop-right-identity-p
    (a-type nil-value operation)
  (forall (a)
    (implies
     (logipedia-bigops-mk-aop-member-p a-type a)
     (equal
      (logipedia-bigops-mk-aop-operation
       operation a nil-value)
      a))))

(defun-sk logipedia-bigops-mk-aop-associative-p
    (a-type operation)
  (forall (a b c)
    (implies
     (and
      (logipedia-bigops-mk-aop-member-p a-type a)
      (logipedia-bigops-mk-aop-member-p a-type b)
      (logipedia-bigops-mk-aop-member-p a-type c))
     (equal
      (logipedia-bigops-mk-aop-operation
       operation
       a
       (logipedia-bigops-mk-aop-operation operation b c))
      (logipedia-bigops-mk-aop-operation
       operation
       (logipedia-bigops-mk-aop-operation operation a b)
       c)))))

(defun-sk logipedia-bigops-mk-aop-statement ()
  (forall (a-type nil-value operation)
    (implies
     (and
      (logipedia-bigops-mk-aop-member-p a-type nil-value)
      (logipedia-bigops-mk-aop-binary-operation-p
       a-type operation)
      (logipedia-bigops-mk-aop-left-identity-p
       a-type nil-value operation)
      (logipedia-bigops-mk-aop-right-identity-p
       a-type nil-value operation)
      (logipedia-bigops-mk-aop-associative-p
       a-type operation))
     (logipedia-bigops-mk-aop-p a-type nil-value))))

(value-triple :itpeval-statement-checked)
:q
