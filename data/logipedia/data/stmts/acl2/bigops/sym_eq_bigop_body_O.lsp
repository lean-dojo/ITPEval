;; Statement-only formalization of Logipedia corpus artifact
;; bigops.sym_eq_bigop_body_O, catalog title "bigops.sym_eq_bigop_body_O":
;; at natural index zero, the function returning its neutral argument is
;; Leibniz-equal at the full higher-order function type to the polymorphic
;; bigop body. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for arbitrary carriers, the function arguments,
;; and application of reified higher-order function values.

(defstub logipedia-bigops-sym-body-o-member-p (h-type value) t)
(defstub logipedia-bigops-sym-body-o-predicate-at (predicate index) t)
(defstub logipedia-bigops-sym-body-o-operation-at
  (operation left right)
  t)
(defstub logipedia-bigops-sym-body-o-sequence-at (sequence index) t)

(defstub logipedia-bigops-sym-body-o-generic-apply
  (h-type function-value predicate nil-value operation sequence)
  t)

(defstub logipedia-bigops-sym-body-o-bigop-body (h-type index) t)

;; This reified value is the source lambda
;; (fun predicate nil-value operation sequence => nil-value).

(defun logipedia-bigops-sym-body-o-constant-nil-function (h-type)
  (list 'logipedia-bigops-sym-body-o-constant-nil-function h-type))

(defun logipedia-bigops-sym-body-o-apply
    (h-type function-value predicate nil-value operation sequence)
  (if
      (equal
       function-value
       (logipedia-bigops-sym-body-o-constant-nil-function h-type))
      nil-value
    (logipedia-bigops-sym-body-o-generic-apply
     h-type function-value predicate nil-value operation sequence)))

(defun-sk logipedia-bigops-sym-body-o-nat-bool-function-p (predicate)
  (forall (index)
    (implies
     (natp index)
     (booleanp
      (logipedia-bigops-sym-body-o-predicate-at predicate index)))))

(defun-sk logipedia-bigops-sym-body-o-binary-operation-p
    (h-type operation)
  (forall (left right)
    (implies
     (and
      (logipedia-bigops-sym-body-o-member-p h-type left)
      (logipedia-bigops-sym-body-o-member-p h-type right))
     (logipedia-bigops-sym-body-o-member-p
      h-type
      (logipedia-bigops-sym-body-o-operation-at operation left right)))))

(defun-sk logipedia-bigops-sym-body-o-nat-sequence-p (h-type sequence)
  (forall (index)
    (implies
     (natp index)
     (logipedia-bigops-sym-body-o-member-p
      h-type
      (logipedia-bigops-sym-body-o-sequence-at sequence index)))))

(defun logipedia-bigops-sym-body-o-arguments-p
    (h-type predicate nil-value operation sequence)
  (and
   (logipedia-bigops-sym-body-o-nat-bool-function-p predicate)
   (logipedia-bigops-sym-body-o-member-p h-type nil-value)
   (logipedia-bigops-sym-body-o-binary-operation-p h-type operation)
   (logipedia-bigops-sym-body-o-nat-sequence-p h-type sequence)))

(defun-sk logipedia-bigops-sym-body-o-function-value-p
    (h-type function-value)
  (forall (predicate nil-value operation sequence)
    (implies
     (logipedia-bigops-sym-body-o-arguments-p
      h-type predicate nil-value operation sequence)
     (logipedia-bigops-sym-body-o-member-p
      h-type
      (logipedia-bigops-sym-body-o-apply
       h-type
       function-value
       predicate
       nil-value
       operation
       sequence)))))

(defun-sk logipedia-bigops-sym-body-o-bigop-body-typed-p ()
  (forall (h-type index)
    (implies
     (natp index)
     (logipedia-bigops-sym-body-o-function-value-p
      h-type
      (logipedia-bigops-sym-body-o-bigop-body h-type index)))))

;; ACL2 equality of the reified values is identity at the complete source
;; function type, hence the source Leibniz equality rather than merely
;; pointwise agreement.

(defun-sk logipedia-bigops-sym-eq-bigop-body-o-leibniz-p ()
  (forall (h-type)
    (equal
     (logipedia-bigops-sym-body-o-constant-nil-function h-type)
     (logipedia-bigops-sym-body-o-bigop-body h-type 0))))

(defun logipedia-bigops-sym-eq-bigop-body-o-statement ()
  (implies
   (logipedia-bigops-sym-body-o-bigop-body-typed-p)
   (logipedia-bigops-sym-eq-bigop-body-o-leibniz-p)))

(value-triple :itpeval-statement-checked)
:q
