;; Statement-only formalization of VERINA corpus artifact verina_basic_82,
;; catalog title "remove_front": a deterministic nonempty integer-array
;; program removes the first element by copying the remaining suffix, with its
;; size and pointwise correctness contract. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-82-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-82-int-array-p (cdr a)))
    (equal a nil)))

(defun verina-basic-82-remove-front-precond (a)
  (< 0 (len a)))

;; This is exact natural-number suffix removal. It supplies the source
;; copyFrom helper's unprocessed suffix beginning at index I.

(defun verina-basic-82-drop (i a)
  (declare (xargs :measure (nfix i)))
  (if (zp i)
      a
    (if (consp a)
        (verina-basic-82-drop
         (- i 1)
         (cdr a))
      nil)))

;; Each step performs Array.push on the current accumulator with the next
;; source entry. Consuming REMAINING exactly reproduces copyFrom's guard
;; I < A.size and its recursive advance to I + 1.

(defun verina-basic-82-copy-from-scan
    (remaining acc)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-basic-82-copy-from-scan
       (cdr remaining)
       (append acc (cons (car remaining) nil)))
    acc))

;; This preserves the complete source helper signature and computation on its
;; typed Array Int, Nat, and Array Int arguments.

(defun verina-basic-82-copy-from
    (a i acc)
  (verina-basic-82-copy-from-scan
   (verina-basic-82-drop i a)
   acc))

;; Array.mkEmpty allocates capacity but has no entries, so every natural
;; capacity has the empty list as its represented array contents.

(defun verina-basic-82-array-mk-empty (capacity)
  (declare (ignore capacity))
  nil)

;; Lean Nat subtraction truncates at zero.

(defun verina-basic-82-nat-sub (left right)
  (nfix (- left right)))

;; The proof-valued precondition argument is computationally irrelevant and
;; is erased. The true branch retains the exact source initialization and
;; copyFrom call. Lean panic at Array Int returns the default empty array; that
;; branch is unreachable whenever the source precondition holds.

(defun verina-basic-82-remove-front (a)
  (if (< 0 (len a))
      (let ((c
             (verina-basic-82-copy-from
              a
              1
              (verina-basic-82-array-mk-empty
               (verina-basic-82-nat-sub
                (len a)
                1)))))
        c)
    nil))

;; Array.get! on Array Int returns the indexed entry when present and the
;; inhabited integer default zero otherwise.

(defun verina-basic-82-array-read (i a)
  (if (and
       (natp i)
       (< i (len a)))
      (nth i a)
    0))

;; This predicate preserves the source postcondition's universal Nat binder
;; and its exact strict bound by the result size.

(defun-sk verina-basic-82-elements-shifted-p
    (a result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len result)))
     (equal
      (verina-basic-82-array-read i result)
      (verina-basic-82-array-read
       (+ i 1)
       a)))))

;; This is the complete source postcondition. The proof-valued precondition
;; argument is unused and therefore erased.

(defun verina-basic-82-remove-front-postcond
    (a result)
  (and
   (verina-basic-82-int-array-p a)
   (verina-basic-82-int-array-p result)
   (< 0 (len a))
   (equal
    (len result)
    (verina-basic-82-nat-sub
     (len a)
     1))
   (verina-basic-82-elements-shifted-p
    a
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array, assumes exactly the source nonempty
;; precondition, and applies the complete postcondition to the exact
;; executable result.

(defun-sk
    verina-basic-82-remove-front-spec-satisfied-statement
    ()
  (forall (a)
    (implies
     (and
      (verina-basic-82-int-array-p a)
      (verina-basic-82-remove-front-precond a))
     (verina-basic-82-remove-front-postcond
      a
      (verina-basic-82-remove-front a)))))

(value-triple :itpeval-statement-checked)
:q
