;; Statement-only formalization of VERINA corpus artifact verina_basic_56,
;; catalog title "copy": a deterministic integer-array program copies a
;; specified source segment into a destination segment while preserving every
;; destination entry outside that segment. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-56-integer-array-p (array)
  (declare (xargs :measure (acl2-count array)))
  (if (consp array)
      (and
       (integerp (car array))
       (verina-basic-56-integer-array-p (cdr array)))
    (equal array nil)))

;; This is exactly the source precondition after Array.size is represented by
;; list length.

(defun verina-basic-56-copy-precond
    (src s-start dest d-start copy-len)
  (and
   (<= (+ s-start copy-len) (len src))
   (<= (+ d-start copy-len) (len dest))))

;; Array.get! on Array Int returns the indexed entry when it is present and
;; the inhabited integer default zero otherwise.

(defun verina-basic-56-array-read (index array)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp array)
        (if (zp index)
            (car array)
          (verina-basic-56-array-read
           (- index 1)
           (cdr array)))
      0)))

;; Array.set! replaces an in-bounds entry and leaves the array unchanged when
;; its natural index is out of bounds.

(defun verina-basic-56-array-set
    (index value array)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      array
    (if (consp array)
        (if (zp index)
            (cons value (cdr array))
          (cons
           (car array)
           (verina-basic-56-array-set
            (- index 1)
            value
            (cdr array))))
      nil)))

;; This is the source updateSegment recursion. At positive N it first writes
;; source index S-START + (N - 1) to destination index D-START + (N - 1),
;; then recurses on N - 1, so the same descending sequence of updates is
;; preserved exactly.

(defun verina-basic-56-update-segment
    (result src s-start d-start n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      result
    (let* ((index (- n 1))
           (result-new
            (verina-basic-56-array-set
             (+ d-start index)
             (verina-basic-56-array-read
              (+ s-start index)
              src)
             result)))
      (verina-basic-56-update-segment
       result-new
       src
       s-start
       d-start
       index))))

;; The proof-valued precondition argument is computationally irrelevant and
;; is erased. The zero-length branch and the call to updateSegment reproduce
;; the complete executable copy definition.

(defun verina-basic-56-copy
    (src s-start dest d-start copy-len)
  (if (equal copy-len 0)
      dest
    (verina-basic-56-update-segment
     dest
     src
     s-start
     d-start
     copy-len)))

;; These predicates preserve the three universal Nat binders in the source
;; postcondition, including both default-zero array reads and the original
;; index bounds.

(defun-sk verina-basic-56-before-segment-unchanged-p
    (dest d-start result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i d-start))
     (equal
      (verina-basic-56-array-read i result)
      (verina-basic-56-array-read i dest)))))

(defun-sk verina-basic-56-after-segment-unchanged-p
    (dest d-start copy-len result)
  (forall (i)
    (implies
     (and
      (natp i)
      (<= (+ d-start copy-len) i)
      (< i (len result)))
     (equal
      (verina-basic-56-array-read i result)
      (verina-basic-56-array-read i dest)))))

(defun-sk verina-basic-56-segment-copied-p
    (src s-start d-start copy-len result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i copy-len))
     (equal
      (verina-basic-56-array-read
       (+ d-start i)
       result)
      (verina-basic-56-array-read
       (+ s-start i)
       src)))))

;; This is the complete source postcondition. ACL2 predicates make the typed
;; Array Int and Nat binders explicit; the unused proof-valued precondition
;; argument is erased.

(defun verina-basic-56-copy-postcond
    (src s-start dest d-start copy-len result)
  (and
   (verina-basic-56-integer-array-p src)
   (natp s-start)
   (verina-basic-56-integer-array-p dest)
   (natp d-start)
   (natp copy-len)
   (verina-basic-56-integer-array-p result)
   (equal (len result) (len dest))
   (verina-basic-56-before-segment-unchanged-p
    dest
    d-start
    result)
   (verina-basic-56-after-segment-unchanged-p
    dest
    d-start
    copy-len
    result)
   (verina-basic-56-segment-copied-p
    src
    s-start
    d-start
    copy-len
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every pair of finite integer arrays and all natural start indices and
;; lengths, assumes exactly the source bounds precondition, and applies the
;; complete postcondition to the exact executable result.

(defun-sk
    verina-basic-56-copy-spec-satisfied-statement
    ()
  (forall (src s-start dest d-start copy-len)
    (implies
     (and
      (verina-basic-56-integer-array-p src)
      (natp s-start)
      (verina-basic-56-integer-array-p dest)
      (natp d-start)
      (natp copy-len)
      (verina-basic-56-copy-precond
       src
       s-start
       dest
       d-start
       copy-len))
     (verina-basic-56-copy-postcond
      src
      s-start
      dest
      d-start
      copy-len
      (verina-basic-56-copy
       src
       s-start
       dest
       d-start
       copy-len)))))

(value-triple :itpeval-statement-checked)
:q
