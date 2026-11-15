;; Statement-only formalization of Logipedia corpus artifact
;; bigops.sym_eq_bigop_body_S, catalog title "bigops.sym_eq_bigop_body_S":
;; for every carrier and natural index, the Boolean-controlled four-argument
;; function is Leibniz-equal at its full higher-order function type to the
;; successor bigop body. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify arbitrary source carriers, function
;; arguments, application, bigop, and the higher-order bigop-body values.

(defstub logipedia-bigops-sym-body-s-member-p (h-type value) t)
(defstub logipedia-bigops-sym-body-s-predicate-at
  (predicate index)
  t)
(defstub logipedia-bigops-sym-body-s-operation-at
  (operation left right)
  t)
(defstub logipedia-bigops-sym-body-s-sequence-at
  (sequence index)
  t)

(defstub logipedia-bigops-sym-body-s-bigop
  (h-type index predicate nil-value operation sequence)
  t)

(defstub logipedia-bigops-sym-body-s-generic-apply
  (h-type function-value predicate nil-value operation sequence)
  t)

(defstub logipedia-bigops-sym-body-s-bigop-body
  (h-type index)
  t)

;; This reified value is the source lambda
;; (fun p nil op f =>
;;    if p(n) then op(f(n), bigop(n,p,nil,op,f))
;;    else bigop(n,p,nil,op,f)).

(defun logipedia-bigops-sym-body-s-step-function (h-type index)
  (list 'logipedia-bigops-sym-body-s-step-function h-type index))

(defun logipedia-bigops-sym-body-s-step-function-p
    (h-type function-value)
  (and
   (consp function-value)
   (equal
    (car function-value)
    'logipedia-bigops-sym-body-s-step-function)
   (consp (cdr function-value))
   (equal (cadr function-value) h-type)
   (consp (cddr function-value))
   (natp (caddr function-value))
   (equal (cdddr function-value) nil)))

(defun logipedia-bigops-sym-body-s-apply
    (h-type function-value predicate nil-value operation sequence)
  (if
      (logipedia-bigops-sym-body-s-step-function-p
       h-type function-value)
      (let*
          ((index (caddr function-value))
           (prior
            (logipedia-bigops-sym-body-s-bigop
             h-type index predicate nil-value operation sequence)))
        (if
            (logipedia-bigops-sym-body-s-predicate-at
             predicate index)
            (logipedia-bigops-sym-body-s-operation-at
             operation
             (logipedia-bigops-sym-body-s-sequence-at
              sequence index)
             prior)
          prior))
    (logipedia-bigops-sym-body-s-generic-apply
     h-type function-value predicate nil-value operation sequence)))

(defun-sk logipedia-bigops-sym-body-s-nat-bool-function-p
    (predicate)
  (forall (index)
    (implies
     (natp index)
     (booleanp
      (logipedia-bigops-sym-body-s-predicate-at
       predicate index)))))

(defun-sk logipedia-bigops-sym-body-s-binary-operation-p
    (h-type operation)
  (forall (left right)
    (implies
     (and
      (logipedia-bigops-sym-body-s-member-p h-type left)
      (logipedia-bigops-sym-body-s-member-p h-type right))
     (logipedia-bigops-sym-body-s-member-p
      h-type
      (logipedia-bigops-sym-body-s-operation-at
       operation left right)))))

(defun-sk logipedia-bigops-sym-body-s-nat-sequence-p
    (h-type sequence)
  (forall (index)
    (implies
     (natp index)
     (logipedia-bigops-sym-body-s-member-p
      h-type
      (logipedia-bigops-sym-body-s-sequence-at
       sequence index)))))

(defun logipedia-bigops-sym-body-s-arguments-p
    (h-type predicate nil-value operation sequence)
  (and
   (logipedia-bigops-sym-body-s-nat-bool-function-p predicate)
   (logipedia-bigops-sym-body-s-member-p h-type nil-value)
   (logipedia-bigops-sym-body-s-binary-operation-p
    h-type operation)
   (logipedia-bigops-sym-body-s-nat-sequence-p
    h-type sequence)))

(defun-sk logipedia-bigops-sym-body-s-function-value-p
    (h-type function-value)
  (forall (predicate nil-value operation sequence)
    (implies
     (logipedia-bigops-sym-body-s-arguments-p
      h-type predicate nil-value operation sequence)
     (logipedia-bigops-sym-body-s-member-p
      h-type
      (logipedia-bigops-sym-body-s-apply
       h-type
       function-value
       predicate
       nil-value
       operation
       sequence)))))

(defun-sk logipedia-bigops-sym-body-s-bigop-typed-p ()
  (forall (h-type index predicate nil-value operation sequence)
    (implies
     (and
      (natp index)
      (logipedia-bigops-sym-body-s-arguments-p
       h-type predicate nil-value operation sequence))
     (logipedia-bigops-sym-body-s-member-p
      h-type
      (logipedia-bigops-sym-body-s-bigop
       h-type
       index
       predicate
       nil-value
       operation
       sequence)))))

(defun-sk logipedia-bigops-sym-body-s-bigop-body-typed-p ()
  (forall (h-type index)
    (implies
     (natp index)
     (logipedia-bigops-sym-body-s-function-value-p
      h-type
      (logipedia-bigops-sym-body-s-bigop-body
       h-type index)))))

;; ACL2 equality of the reified values is identity at the complete source
;; function type, and therefore represents the source Leibniz equality rather
;; than merely pointwise agreement.

(defun-sk logipedia-bigops-sym-eq-bigop-body-s-leibniz-p ()
  (forall (h-type index)
    (implies
     (natp index)
     (equal
      (logipedia-bigops-sym-body-s-step-function
       h-type index)
      (logipedia-bigops-sym-body-s-bigop-body
       h-type (+ 1 index))))))

(defun logipedia-bigops-sym-eq-bigop-body-s-statement ()
  (implies
   (and
    (logipedia-bigops-sym-body-s-bigop-typed-p)
    (logipedia-bigops-sym-body-s-bigop-body-typed-p))
   (logipedia-bigops-sym-eq-bigop-body-s-leibniz-p)))

(value-triple :itpeval-statement-checked)
:q
