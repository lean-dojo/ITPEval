;; Statement-only formalization of Logipedia corpus artifact
;; bigops.axiom_bigop_body_S: at every natural successor, bigop_body applies
;; the operation to the current sequence value and recursive bigop exactly
;; when the predicate holds at the current index. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-bigops-body-s-predicate-at-raw
  (predicate index)
  t)

(defstub logipedia-bigops-body-s-operation-apply
  (h-type operation left right)
  t)

(defstub logipedia-bigops-body-s-sequence-at
  (h-type sequence index)
  t)

(defstub logipedia-bigops-body-s-bigop
  (h-type index predicate nil-value operation sequence)
  t)

(defstub logipedia-bigops-body-s-bigop-body
  (h-type index predicate nil-value operation sequence)
  t)

;; ACL2 is first order, so the source equality between higher-order function
;; values is stated extensionally over the predicate, neutral value, operation,
;; and sequence arguments. The wrapper makes the predicate result a Boolean,
;; as required by the source type Nat -> Bool.
(defun logipedia-bigops-body-s-predicate-at (predicate index)
  (if
      (logipedia-bigops-body-s-predicate-at-raw
       predicate
       (nfix index))
      t
    nil))

(defun-sk logipedia-bigops-axiom-bigop-body-s-statement ()
  (forall
    (h-type index predicate nil-value operation sequence)
    (implies
     (natp index)
     (equal
      (logipedia-bigops-body-s-bigop-body
       h-type
       (+ index 1)
       predicate
       nil-value
       operation
       sequence)
      (if
          (logipedia-bigops-body-s-predicate-at predicate index)
          (logipedia-bigops-body-s-operation-apply
           h-type
           operation
           (logipedia-bigops-body-s-sequence-at
            h-type sequence index)
           (logipedia-bigops-body-s-bigop
            h-type
            index
            predicate
            nil-value
            operation
            sequence))
        (logipedia-bigops-body-s-bigop
         h-type
         index
         predicate
         nil-value
         operation
         sequence))))))

(value-triple :itpeval-statement-checked)
:q
