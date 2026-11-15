;; Statement-only formalization of VERINA corpus artifact verina_basic_89,
;; catalog title "SetToSeq": a deterministic integer-list fold removes
;; duplicate entries while preserving first-occurrence order and satisfies
;; its membership, uniqueness, and order contract. This file contains no proof.

(in-package "ACL2")

;; Finite Lean List Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-89-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-basic-89-integer-list-p (cdr xs)))
    (equal xs nil)))

;; The source precondition is True. The List Int binder domain remains
;; explicit in the final correctness proposition.

(defun verina-basic-89-set-to-seq-precond (s)
  (declare (ignore s))
  t)

;; This accumulator recursion is exactly the source List.foldl. At each input
;; element, it retains the accumulator when the value is already present and
;; otherwise appends that value at the end.

(defun verina-basic-89-set-to-seq-loop
    (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((x (car remaining)))
        (verina-basic-89-set-to-seq-loop
         (cdr remaining)
         (if (member-equal x accumulator)
             accumulator
           (append accumulator (list x)))))
    accumulator))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. The empty list is the source fold's initial accumulator.

(defun verina-basic-89-set-to-seq (s)
  (verina-basic-89-set-to-seq-loop s nil))

;; This is the Boolean List.all membership condition used in both directions
;; by the source postcondition.

(defun verina-basic-89-all-members-of-p
    (xs container)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (member-equal (car xs) container)
       (verina-basic-89-all-members-of-p
        (cdr xs)
        container))
    (equal xs nil)))

;; List.count under decidable integer equality.

(defun verina-basic-89-count-value
    (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (+
       (if (equal value (car xs)) 1 0)
       (verina-basic-89-count-value
        value
        (cdr xs)))
    0))

;; The full result remains fixed while List.all traverses it, so every
;; traversed value is required to occur exactly once in that full result.

(defun verina-basic-89-every-count-one-p
    (remaining result)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (equal
        (verina-basic-89-count-value
         (car remaining)
         result)
        1)
       (verina-basic-89-every-count-one-p
        (cdr remaining)
        result))
    (equal remaining nil)))

;; Lean's List.idxOf returns the first matching natural index and returns the
;; list length when the value is absent. This recursion has exactly that
;; behavior on proper lists.

(defun verina-basic-89-first-index
    (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (equal value (car xs))
          0
        (+
         1
         (verina-basic-89-first-index
          value
          (cdr xs))))
    0))

;; For one Pairwise head, impose the source implication against every later
;; element. Both idxOf calls use the complete result and complete input list.

(defun verina-basic-89-head-order-preserved-p
    (head later result s)
  (declare (xargs :measure (acl2-count later)))
  (if (consp later)
      (and
       (implies
        (<
         (verina-basic-89-first-index head result)
         (verina-basic-89-first-index
          (car later)
          result))
        (<
         (verina-basic-89-first-index head s)
         (verina-basic-89-first-index
          (car later)
          s)))
       (verina-basic-89-head-order-preserved-p
        head
        (cdr later)
        result
        s))
    (equal later nil)))

;; This is List.Pairwise for the source order-preservation relation.

(defun verina-basic-89-pairwise-order-preserved-p
    (remaining result s)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (verina-basic-89-head-order-preserved-p
        (car remaining)
        (cdr remaining)
        result
        s)
       (verina-basic-89-pairwise-order-preserved-p
        (cdr remaining)
        result
        s))
    (equal remaining nil)))

;; This is the complete source postcondition: equal element membership in both
;; directions, count one for every result element, and the original Pairwise
;; first-index implication. The unused proof-valued precondition is erased.

(defun verina-basic-89-set-to-seq-postcond
    (s result)
  (and
   (verina-basic-89-integer-list-p s)
   (verina-basic-89-integer-list-p result)
   (verina-basic-89-all-members-of-p result s)
   (verina-basic-89-all-members-of-p s result)
   (verina-basic-89-every-count-one-p
    result
    result)
   (verina-basic-89-pairwise-order-preserved-p
    result
    result
    s)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer list, assumes exactly the source True
;; precondition, and applies the complete postcondition to the exact
;; executable SetToSeq result.

(defun-sk
    verina-basic-89-set-to-seq-spec-satisfied-statement
    ()
  (forall (s)
    (implies
     (and
      (verina-basic-89-integer-list-p s)
      (verina-basic-89-set-to-seq-precond s))
     (verina-basic-89-set-to-seq-postcond
      s
      (verina-basic-89-set-to-seq s)))))

(value-triple :itpeval-statement-checked)
:q
