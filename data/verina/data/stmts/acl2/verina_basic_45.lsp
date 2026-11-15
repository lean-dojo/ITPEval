;; Statement-only formalization of VERINA corpus artifact verina_basic_45,
;; catalog title "findProduct": a deterministic scan of an integer list
;; multiplies its first even entry by its first odd entry, with the corresponding
;; precondition, postcondition, and correctness proposition. This file contains no proof.

(in-package "ACL2")

;; Finite Lean List Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-45-int-list-p (lst)
  (declare (xargs :measure (acl2-count lst)))
  (if (consp lst)
      (and
       (integerp (car lst))
       (verina-basic-45-int-list-p (cdr lst)))
    (equal lst nil)))

;; With positive divisor two, ACL2 MOD and Lean Int.emod agree on every
;; integer. These Boolean predicates are exactly the source parity helpers.

(defun verina-basic-45-is-even (n)
  (equal (mod n 2) 0))

(defun verina-basic-45-is-odd (n)
  (not (equal (mod n 2) 0)))

;; These structural searches are exactly the two bounded membership
;; existentials in the source precondition.

(defun verina-basic-45-contains-even-p (lst)
  (declare (xargs :measure (acl2-count lst)))
  (if (consp lst)
      (or
       (verina-basic-45-is-even (car lst))
       (verina-basic-45-contains-even-p (cdr lst)))
    nil))

(defun verina-basic-45-contains-odd-p (lst)
  (declare (xargs :measure (acl2-count lst)))
  (if (consp lst)
      (or
       (verina-basic-45-is-odd (car lst))
       (verina-basic-45-contains-odd-p (cdr lst)))
    nil))

(defun verina-basic-45-find-product-precond (lst)
  (and
   (< 1 (len lst))
   (verina-basic-45-contains-even-p lst)
   (verina-basic-45-contains-odd-p lst)))

;; Option Nat is represented by :none or the tagged dotted pair
;; (:some . index), keeping absence distinct from natural-number index zero.

(defun verina-basic-45-option-nat-some-p (option)
  (and
   (consp option)
   (equal (car option) :some)
   (natp (cdr option))))

;; Each loop is List.findIdx? for the corresponding parity predicate. INDEX
;; is the source Nat index of the first element of REMAINING.

(defun verina-basic-45-find-even-index-loop (remaining index)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (verina-basic-45-is-even (car remaining))
          (cons :some index)
        (verina-basic-45-find-even-index-loop
         (cdr remaining)
         (+ index 1)))
    :none))

(defun verina-basic-45-find-odd-index-loop (remaining index)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (verina-basic-45-is-odd (car remaining))
          (cons :some index)
        (verina-basic-45-find-odd-index-loop
         (cdr remaining)
         (+ index 1)))
    :none))

;; Option (Nat x Nat) is represented by :none or (:some even-index odd-index).
;; This definition performs the same two independent first-index searches and
;; returns a pair exactly when both searches succeed.

(defun verina-basic-45-first-even-odd-indices (lst)
  (let ((even-index
         (verina-basic-45-find-even-index-loop lst 0))
        (odd-index
         (verina-basic-45-find-odd-index-loop lst 0)))
    (if (and
         (verina-basic-45-option-nat-some-p even-index)
         (verina-basic-45-option-nat-some-p odd-index))
        (list :some (cdr even-index) (cdr odd-index))
      :none)))

;; The proof-valued precondition argument is computationally irrelevant and
;; is erased. For a present pair, NTH is applied at exactly the valid indices
;; returned by the two searches; the absent branch returns zero.

(defun verina-basic-45-find-product (lst)
  (let ((indices
         (verina-basic-45-first-even-odd-indices lst)))
    (if (equal indices :none)
        0
      (* (nth (cadr indices) lst)
         (nth (caddr indices) lst)))))

;; This is the complete source match-based postcondition. The typed Lean
;; binders are explicit as ACL2 domain predicates, while the proof-valued
;; precondition argument is erased because it does not occur in the body.

(defun verina-basic-45-find-product-postcond
    (lst result)
  (and
   (verina-basic-45-int-list-p lst)
   (integerp result)
   (let ((indices
          (verina-basic-45-first-even-odd-indices lst)))
     (if (equal indices :none)
         t
       (equal
        result
        (* (nth (cadr indices) lst)
           (nth (caddr indices) lst)))))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer list, assumes exactly the source precondition, and
;; applies the complete postcondition to the exact executable implementation.

(defun-sk
    verina-basic-45-find-product-spec-satisfied-statement
    ()
  (forall (lst)
    (implies
     (and
      (verina-basic-45-int-list-p lst)
      (verina-basic-45-find-product-precond lst))
     (verina-basic-45-find-product-postcond
      lst
      (verina-basic-45-find-product lst)))))

(value-triple :itpeval-statement-checked)
:q
