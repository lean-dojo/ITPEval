;; Statement-only formalization of VERINA corpus artifact verina_basic_86,
;; catalog title "rotate": a deterministic integer-array program rotates its
;; entries left by a nonnegative integer offset while preserving the array
;; size and the indexed modulo relationship. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-86-integer-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-86-integer-array-p
        (cdr a)))
    (equal a nil)))

;; This is exactly the source precondition on its typed Int offset.

(defun verina-basic-86-rotate-precond
    (a offset)
  (declare (ignore a))
  (<= 0 offset))

;; Array.get! on Array Int returns the indexed entry when present and the
;; inhabited integer default zero otherwise.

(defun verina-basic-86-array-read
    (index a)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp a)
        (if (zp index)
            (car a)
          (verina-basic-86-array-read
           (- index 1)
           (cdr a)))
      0)))

;; Array.set! replaces an in-bounds entry and leaves the array unchanged when
;; its natural index is outside the array.

(defun verina-basic-86-array-set
    (index value a)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      a
    (if (consp a)
        (if (zp index)
            (cons value (cdr a))
          (cons
           (car a)
           (verina-basic-86-array-set
            (- index 1)
            value
            (cdr a))))
      nil)))

;; This is Array.mkArray: a list containing exactly N copies of VALUE.

(defun verina-basic-86-make-array
    (n value)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons
     value
     (verina-basic-86-make-array
      (- n 1)
      value))))

;; Whenever the source evaluates its modulo expression, LENGTH is positive.
;; ACL2 MOD with a positive integer divisor is Lean Int.emod, hence IDX-INT is
;; already nonnegative. Retaining the conditional adjustment and final
;; nonnegative conversion mirrors the source bindings exactly.

(defun verina-basic-86-rotated-index
    (i offset length)
  (if (and
       (natp i)
       (integerp offset)
       (natp length)
       (< 0 length))
      (let* ((idx-int
              (mod (+ i offset) length))
             (idx-int-adjusted
              (if (< idx-int 0)
                  (+ idx-int length)
                idx-int)))
        (if (< idx-int-adjusted 0)
            0
          idx-int-adjusted))
    0))

;; For typed Nat I and LENGTH, the initial fuel LENGTH-I is exactly the number
;; of recursive source calls while I < LENGTH. Each step computes the same
;; modulo index, defaulting array read, set! update, and increment as rotateAux.

(defun verina-basic-86-rotate-aux-fuel
    (a offset i length b fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or
       (zp fuel)
       (not (natp i))
       (not (natp length))
       (not (< i length)))
      b
    (let* ((idx-nat
            (verina-basic-86-rotated-index
             i
             offset
             length))
           (new-b
            (verina-basic-86-array-set
             i
             (verina-basic-86-array-read
              idx-nat
              a)
             b)))
      (verina-basic-86-rotate-aux-fuel
       a
       offset
       (+ i 1)
       length
       new-b
       (- fuel 1)))))

;; This preserves the complete rotateAux helper signature and exact
;; computation on its Array Int, Int, Nat, Nat, and Array Int arguments.

(defun verina-basic-86-rotate-aux
    (a offset i length b)
  (verina-basic-86-rotate-aux-fuel
   a
   offset
   i
   length
   b
   (nfix (- length i))))

;; The proof-valued precondition argument is computationally irrelevant and
;; is erased. The bindings preserve the source size, default initializer,
;; mkArray call, and invocation of rotateAux at index zero.

(defun verina-basic-86-rotate
    (a offset)
  (let* ((length (len a))
         (default-value
          (if (< 0 length)
              (verina-basic-86-array-read 0 a)
            0))
         (b0
          (verina-basic-86-make-array
           length
           default-value)))
    (verina-basic-86-rotate-aux
     a
     offset
     0
     length
     b0)))

;; This predicate preserves the source postcondition's universal Nat binder,
;; strict size bound, defaulting reads, and exact Int-to-Nat modulo index.

(defun-sk verina-basic-86-rotated-entries-p
    (a offset result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len a)))
     (equal
      (verina-basic-86-array-read
       i
       result)
      (verina-basic-86-array-read
       (verina-basic-86-rotated-index
        i
        offset
        (len a))
       a)))))

;; This is the complete source postcondition. The Array Int and Int domains
;; are explicit, and the unused proof-valued precondition argument is erased.

(defun verina-basic-86-rotate-postcond
    (a offset result)
  (and
   (verina-basic-86-integer-array-p a)
   (integerp offset)
   (verina-basic-86-integer-array-p result)
   (equal (len result) (len a))
   (verina-basic-86-rotated-entries-p
    a
    offset
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array and integer offset, assumes exactly the
;; source nonnegativity precondition, and applies the complete postcondition
;; to the exact executable result.

(defun-sk
    verina-basic-86-rotate-spec-satisfied-statement
    ()
  (forall (a offset)
    (implies
     (and
      (verina-basic-86-integer-array-p a)
      (integerp offset)
      (verina-basic-86-rotate-precond
       a
       offset))
     (verina-basic-86-rotate-postcond
      a
      offset
      (verina-basic-86-rotate
       a
       offset)))))

(value-triple :itpeval-statement-checked)
:q
