;; Statement-only formalization of VERINA corpus artifact verina_basic_72,
;; catalog title "append": a deterministic integer-array program copies every
;; input element and appends one integer at the end, satisfying the pointwise
;; and size contract. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-72-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-72-int-array-p (cdr a)))
    (equal a nil)))

;; The source precondition is True. The Array Int and Int binder domains
;; remain explicit in the final correctness proposition.

(defun verina-basic-72-append-precond (a b)
  (declare (ignore a b))
  t)

;; Array.push appends one element to the represented finite array.

(defun verina-basic-72-array-push (a value)
  (append a (list value)))

;; This is exact natural-number suffix removal. It supplies the suffix of A
;; beginning at the source helper's current index.

(defun verina-basic-72-drop (count a)
  (declare (xargs :measure (nfix count)))
  (if (and
       (natp count)
       (< 0 count)
       (consp a))
      (verina-basic-72-drop
       (- count 1)
       (cdr a))
    a))

;; Each scan step performs the source helper's accumulator push and advances
;; to the next input element. Exhausting REMAINING is exactly the source guard
;; I < A.size becoming false.

(defun verina-basic-72-copy-scan (remaining acc)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-basic-72-copy-scan
       (cdr remaining)
       (verina-basic-72-array-push
        acc
        (car remaining)))
    acc))

;; This preserves the complete source COPY signature and its computation on
;; typed Array Int, Nat, and Array Int arguments.

(defun verina-basic-72-copy (a i acc)
  (verina-basic-72-copy-scan
   (verina-basic-72-drop i a)
   acc))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. The implementation copies A from index zero into an empty
;; array and then pushes B, exactly as in the source program.

(defun verina-basic-72-append (a b)
  (let ((c-initial
         (verina-basic-72-copy a 0 nil)))
    (verina-basic-72-array-push
     c-initial
     b)))

;; Array.get! on Array Int returns the indexed entry when present and the
;; inhabited integer default zero otherwise.

(defun verina-basic-72-array-read (index a)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp a)
        (if (zp index)
            (car a)
          (verina-basic-72-array-read
           (- index 1)
           (cdr a)))
      0)))

;; List.range' 0 A.size contains exactly the natural indices below A.size.
;; This bounded universal predicate is therefore equivalent to the source
;; List.all clause requiring every original entry to be preserved.

(defun-sk verina-basic-72-original-entries-preserved-p
    (a result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len a)))
     (equal
      (verina-basic-72-array-read i result)
      (verina-basic-72-array-read i a)))))

;; This is the complete source postcondition: every original position is
;; unchanged, index A.size contains B, and the result has one additional
;; element. The unused proof-valued precondition argument is erased.

(defun verina-basic-72-append-postcond
    (a b result)
  (and
   (verina-basic-72-int-array-p a)
   (integerp b)
   (verina-basic-72-int-array-p result)
   (verina-basic-72-original-entries-preserved-p
    a
    result)
   (equal
    (verina-basic-72-array-read (len a) result)
    b)
   (equal
    (len result)
    (+ (len a) 1))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array and integer, assumes exactly the source
;; True precondition, and applies the complete postcondition to the exact
;; executable result.

(defun-sk verina-basic-72-append-spec-satisfied-statement
    ()
  (forall (a b)
    (implies
     (and
      (verina-basic-72-int-array-p a)
      (integerp b)
      (verina-basic-72-append-precond a b))
     (verina-basic-72-append-postcond
      a
      b
      (verina-basic-72-append a b)))))

(value-triple :itpeval-statement-checked)
:q
