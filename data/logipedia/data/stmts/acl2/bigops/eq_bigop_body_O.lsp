;; Statement-only formalization of Logipedia corpus artifact
;; bigops.eq_bigop_body_O, catalog title "bigops.eq_bigop_body_O": at natural
;; index zero, the polymorphic bigop body is Leibniz-equal to the four-argument
;; function that returns its nil argument. This file contains no proof.

(in-package "ACL2")

;; Reified source types and applications expose the arbitrary carrier H,
;; p : nat -> bool, nil : H, op : H -> H -> H, and f : nat -> H.

(defstub logipedia-bigops-eq-body-o-member-p (h-type value) t)
(defstub logipedia-bigops-eq-body-o-p-at (p index) t)
(defstub logipedia-bigops-eq-body-o-op-at (op left right) t)
(defstub logipedia-bigops-eq-body-o-f-at (f index) t)

(defstub logipedia-bigops-eq-body-o-generic-apply
  (h-type function-value p nil-value op f)
  t)

;; bigop_body H n is represented as a value at the complete source function
;; type (nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H.

(defstub logipedia-bigops-eq-body-o-bigop-body (h-type index) t)

;; This concrete reified value is the source lambda
;; (fun p nil op f => nil).

(defun logipedia-bigops-eq-body-o-constant-nil-function (h-type)
  (list 'logipedia-bigops-eq-body-o-constant-nil-function h-type))

(defun logipedia-bigops-eq-body-o-apply
    (h-type function-value p nil-value op f)
  (if
      (equal
       function-value
       (logipedia-bigops-eq-body-o-constant-nil-function h-type))
      nil-value
    (logipedia-bigops-eq-body-o-generic-apply
     h-type function-value p nil-value op f)))

(defun-sk logipedia-bigops-eq-body-o-nat-bool-function-p (p)
  (forall (index)
    (implies
     (natp index)
     (booleanp
      (logipedia-bigops-eq-body-o-p-at p index)))))

(defun-sk logipedia-bigops-eq-body-o-binary-operation-p (h-type op)
  (forall (left right)
    (implies
     (and
      (logipedia-bigops-eq-body-o-member-p h-type left)
      (logipedia-bigops-eq-body-o-member-p h-type right))
     (logipedia-bigops-eq-body-o-member-p
      h-type
      (logipedia-bigops-eq-body-o-op-at op left right)))))

(defun-sk logipedia-bigops-eq-body-o-nat-function-p (h-type f)
  (forall (index)
    (implies
     (natp index)
     (logipedia-bigops-eq-body-o-member-p
      h-type
      (logipedia-bigops-eq-body-o-f-at f index)))))

(defun logipedia-bigops-eq-body-o-arguments-p
    (h-type p nil-value op f)
  (and
   (logipedia-bigops-eq-body-o-nat-bool-function-p p)
   (logipedia-bigops-eq-body-o-member-p h-type nil-value)
   (logipedia-bigops-eq-body-o-binary-operation-p h-type op)
   (logipedia-bigops-eq-body-o-nat-function-p h-type f)))

(defun-sk logipedia-bigops-eq-body-o-function-value-p
    (h-type function-value)
  (forall (p nil-value op f)
    (implies
     (logipedia-bigops-eq-body-o-arguments-p
      h-type p nil-value op f)
     (logipedia-bigops-eq-body-o-member-p
      h-type
      (logipedia-bigops-eq-body-o-apply
       h-type function-value p nil-value op f)))))

(defun-sk logipedia-bigops-eq-body-o-bigop-body-typed-p ()
  (forall (h-type index)
    (implies
     (natp index)
     (logipedia-bigops-eq-body-o-function-value-p
      h-type
      (logipedia-bigops-eq-body-o-bigop-body h-type index)))))

;; Equality of the reified function values is identity at the full source
;; function type, and hence represents the displayed Leibniz equality.

(defun-sk logipedia-bigops-eq-bigop-body-o-leibniz-p ()
  (forall (h-type)
    (equal
     (logipedia-bigops-eq-body-o-bigop-body h-type 0)
     (logipedia-bigops-eq-body-o-constant-nil-function h-type))))

;; This pointwise clause explicitly exposes the source lambda binders. It is
;; definitionally entailed by the value equality above because APPLY returns
;; NIL-VALUE for the concrete constant-nil function tag.

(defun-sk logipedia-bigops-eq-bigop-body-o-pointwise-p ()
  (forall (h-type p nil-value op f)
    (implies
     (logipedia-bigops-eq-body-o-arguments-p
      h-type p nil-value op f)
     (equal
      (logipedia-bigops-eq-body-o-apply
       h-type
       (logipedia-bigops-eq-body-o-bigop-body h-type 0)
       p
       nil-value
       op
       f)
      nil-value))))

(defun logipedia-bigops-eq-bigop-body-o-statement ()
  (implies
   (logipedia-bigops-eq-body-o-bigop-body-typed-p)
   (and
    (logipedia-bigops-eq-bigop-body-o-leibniz-p)
    (logipedia-bigops-eq-bigop-body-o-pointwise-p))))

(value-triple :itpeval-statement-checked)
:q
