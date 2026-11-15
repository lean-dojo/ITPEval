;; Statement-only formalization of VERINA corpus artifact verina_basic_58,
;; catalog title "double_array_elements": a deterministic integer-array
;; program doubles every element while preserving the array size. This file
;; contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-58-int-array-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (integerp (car s))
       (verina-basic-58-int-array-p (cdr s)))
    (equal s nil)))

;; The source precondition is True. The Array Int binder domain remains
;; explicit in the final correctness proposition.

(defun verina-basic-58-double-array-elements-precond (s)
  (declare (ignore s))
  t)

;; Array.get! on Array Int returns the indexed entry when present and the
;; inhabited integer default zero otherwise.

(defun verina-basic-58-array-read (index s)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp s)
        (if (zp index)
            (car s)
          (verina-basic-58-array-read
           (- index 1)
           (cdr s)))
      0)))

;; Array.set! replaces an in-bounds entry and leaves the array unchanged when
;; its natural index is out of bounds.

(defun verina-basic-58-array-set (index value s)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      s
    (if (consp s)
        (if (zp index)
            (cons value (cdr s))
          (cons
           (car s)
           (verina-basic-58-array-set
            (- index 1)
            value
            (cdr s))))
      nil)))

;; This is exact natural-number suffix removal. It supplies the finite suffix
;; beginning at the source helper's current index.

(defun verina-basic-58-drop (count s)
  (declare (xargs :measure (nfix count)))
  (if (and
       (natp count)
       (< 0 count)
       (consp s))
      (verina-basic-58-drop
       (- count 1)
       (cdr s))
    s))

;; REMAINING is the suffix of the current array beginning at INDEX. Each step
;; reads the original array S-OLD, doubles that value, updates the current
;; array at INDEX, and advances to the next index. Array.set! preserves size,
;; so consuming REMAINING is exactly the source guard INDEX < S.size.

(defun verina-basic-58-double-array-elements-aux-scan
    (s-old s index remaining)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-basic-58-double-array-elements-aux-scan
       s-old
       (verina-basic-58-array-set
        index
        (* 2
           (verina-basic-58-array-read
            index
            s-old))
        s)
       (+ index 1)
       (cdr remaining))
    s))

;; This preserves the complete source helper signature and computation on its
;; typed Array Int, Array Int, and Nat arguments.

(defun verina-basic-58-double-array-elements-aux
    (s-old s index)
  (verina-basic-58-double-array-elements-aux-scan
   s-old
   s
   index
   (verina-basic-58-drop index s)))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. Both original and current arrays start as S at index zero,
;; exactly as in the source implementation.

(defun verina-basic-58-double-array-elements (s)
  (verina-basic-58-double-array-elements-aux
   s
   s
   0))

;; This predicate is the source postcondition's universal Nat quantifier over
;; every valid array index.

(defun-sk verina-basic-58-all-elements-doubled-p
    (s result)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index (len s)))
     (equal
      (verina-basic-58-array-read index result)
      (* 2
         (verina-basic-58-array-read index s))))))

;; This is the complete source postcondition, including result size and the
;; pointwise doubling equation. The proof-valued precondition argument is
;; unused and therefore erased.

(defun verina-basic-58-double-array-elements-postcond
    (s result)
  (and
   (verina-basic-58-int-array-p s)
   (verina-basic-58-int-array-p result)
   (equal (len result) (len s))
   (verina-basic-58-all-elements-doubled-p
    s
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array, assumes exactly the source True
;; precondition, and applies the complete postcondition to the exact executable
;; result.

(defun-sk
    verina-basic-58-double-array-elements-spec-satisfied-statement
    ()
  (forall (s)
    (implies
     (and
      (verina-basic-58-int-array-p s)
      (verina-basic-58-double-array-elements-precond s))
     (verina-basic-58-double-array-elements-postcond
      s
      (verina-basic-58-double-array-elements s)))))

(value-triple :itpeval-statement-checked)
:q
