;; Statement-only formalization of Logipedia corpus artifact
;; bigops.axiom_bigop_body_O: at index zero, the source module's abstract
;; equality relates bigop_body to the function returning its neutral argument.
;; This file contains no proof.

(in-package "ACL2")

(defstub logipedia-bigops-body-o-source-equal-p
  (h-type left-function right-function)
  t)

(defstub logipedia-bigops-body-o-bigop-body-function
  (h-type index)
  t)

(defstub logipedia-bigops-body-o-generic-apply
  (h-type function-value predicate nil-value operation sequence)
  t)

;; Predicates on reified function values expose the source module's
;; equal_leibniz interface. In particular, application-equality predicates
;; make the abstract source equality observably extensional.

(defstub logipedia-bigops-body-o-predicate-holds-p
  (h-type predicate value)
  t)

;; The constructor and application rule faithfully reify
;; (fun predicate nil-value operation sequence => nil-value).

(defun logipedia-bigops-body-o-constant-nil-function (h-type)
  (list 'logipedia-bigops-body-o-constant-nil-function h-type))

(defun logipedia-bigops-body-o-apply
    (h-type function-value predicate nil-value operation sequence)
  (if
      (equal
       function-value
       (logipedia-bigops-body-o-constant-nil-function h-type))
      nil-value
    (logipedia-bigops-body-o-generic-apply
     h-type function-value predicate nil-value operation sequence)))

(defun logipedia-bigops-body-o-application-predicate
    (predicate nil-value operation sequence expected)
  (list
   'logipedia-bigops-body-o-application-equality
   predicate
   nil-value
   operation
   sequence
   expected))

(defun-sk logipedia-bigops-body-o-application-semantics-p ()
  (forall
    (h-type function-value predicate nil-value operation sequence expected)
    (iff
     (logipedia-bigops-body-o-predicate-holds-p
      h-type
      (logipedia-bigops-body-o-application-predicate
       predicate nil-value operation sequence expected)
      function-value)
     (equal
      (logipedia-bigops-body-o-apply
       h-type function-value predicate nil-value operation sequence)
      expected))))

(defun-sk logipedia-bigops-body-o-source-equal-leibniz-p ()
  (forall (h-type left-function right-function predicate)
    (implies
     (logipedia-bigops-body-o-source-equal-p
      h-type left-function right-function)
     (implies
      (logipedia-bigops-body-o-predicate-holds-p
       h-type predicate left-function)
      (logipedia-bigops-body-o-predicate-holds-p
       h-type predicate right-function)))))

(defun-sk logipedia-bigops-body-o-source-equality-p ()
  (forall (h-type)
    (logipedia-bigops-body-o-source-equal-p
     h-type
     (logipedia-bigops-body-o-bigop-body-function h-type 0)
     (logipedia-bigops-body-o-constant-nil-function h-type))))

(defun-sk logipedia-bigops-body-o-pointwise-p ()
  (forall (h-type predicate nil-value operation sequence)
    (equal
     (logipedia-bigops-body-o-apply
      h-type
      (logipedia-bigops-body-o-bigop-body-function h-type 0)
      predicate
      nil-value
      operation
      sequence)
     nil-value)))

(defun logipedia-bigops-axiom-bigop-body-o-statement ()
  (implies
   (and
    (logipedia-bigops-body-o-application-semantics-p)
    (logipedia-bigops-body-o-source-equal-leibniz-p))
   (and
    (logipedia-bigops-body-o-source-equality-p)
    (logipedia-bigops-body-o-pointwise-p))))

(value-triple :itpeval-statement-checked)
:q
