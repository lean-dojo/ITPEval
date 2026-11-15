;; Statement-only formalization of VERINA corpus artifact verina_basic_83,
;; catalog title "concat": a deterministic integer-array program concatenates
;; two arrays and satisfies the complete size and pointwise segment contract.
;; This file contains no proof.

(in-package "ACL2")

;; A Lean Array Int is represented exactly by its finite sequence of entries:
;; a proper ACL2 list whose elements range over all integers.

(defun verina-basic-83-integer-array-p (array)
  (declare (xargs :measure (acl2-count array)))
  (if (consp array)
      (and
       (integerp (car array))
       (verina-basic-83-integer-array-p
        (cdr array)))
    (equal array nil)))

;; The source precondition is True. Both Array Int binder domains remain
;; explicit in the final correctness proposition.

(defun verina-basic-83-concat-precond (a b)
  (declare (ignore a b))
  t)

;; Array.get! returns the indexed entry when present and the inhabited integer
;; default zero otherwise.

(defun verina-basic-83-array-read
    (index array)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp array)
        (if (zp index)
            (car array)
          (verina-basic-83-array-read
           (- index 1)
           (cdr array)))
      0)))

;; Array.set! replaces an in-bounds entry and leaves the array unchanged when
;; its natural index is outside the array.

(defun verina-basic-83-array-set
    (index value array)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      array
    (if (consp array)
        (if (zp index)
            (cons value (cdr array))
          (cons
           (car array)
           (verina-basic-83-array-set
            (- index 1)
            value
            (cdr array))))
      nil)))

;; Array.mkArray LENGTH 0 is the proper list containing exactly LENGTH
;; integer zeroes.

(defun verina-basic-83-zero-array (length)
  (declare (xargs :measure (nfix length)))
  (if (zp length)
      nil
    (cons
     0
     (verina-basic-83-zero-array
      (- length 1)))))

;; FUEL is exactly N - I. Every recursive step preserves the source loop:
;; choose A[I] while I < A.size and otherwise B[I - A.size], update C at I,
;; and advance to I + 1.

(defun verina-basic-83-concat-loop-fuel
    (a b n i c fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      c
    (if (and
         (natp n)
         (natp i)
         (< i n))
        (let* ((value
                (if (< i (len a))
                    (verina-basic-83-array-read
                     i
                     a)
                  (verina-basic-83-array-read
                   (- i (len a))
                   b)))
               (new-c
                (verina-basic-83-array-set
                 i
                 value
                 c)))
          (verina-basic-83-concat-loop-fuel
           a
           b
           n
           (+ i 1)
           new-c
           (- fuel 1)))
      c)))

;; This preserves the source local loop's index, accumulator, closed bound N,
;; and exact computation on their natural and Array Int domains.

(defun verina-basic-83-concat-loop
    (a b n i c)
  (verina-basic-83-concat-loop-fuel
   a
   b
   n
   i
   c
   (nfix (- n i))))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. The bound, zero-filled initializer, and call at index zero
;; reproduce the complete source implementation.

(defun verina-basic-83-concat (a b)
  (let ((n (+ (len a) (len b))))
    (verina-basic-83-concat-loop
     a
     b
     n
     0
     (verina-basic-83-zero-array n))))

;; These predicates preserve the two universal Nat binders in the source
;; postcondition, including their exact bounds and result indices.

(defun-sk verina-basic-83-first-segment-correct-p
    (a result)
  (forall (k)
    (implies
     (and
      (natp k)
      (< k (len a)))
     (equal
      (verina-basic-83-array-read k result)
      (verina-basic-83-array-read k a)))))

(defun-sk verina-basic-83-second-segment-correct-p
    (a b result)
  (forall (k)
    (implies
     (and
      (natp k)
      (< k (len b)))
     (equal
      (verina-basic-83-array-read
       (+ k (len a))
       result)
      (verina-basic-83-array-read k b)))))

;; This is the complete source postcondition: the result has the sum of the
;; input sizes, followed pointwise by all entries of A and then all entries of
;; B. The unused proof-valued precondition argument is erased.

(defun verina-basic-83-concat-postcond
    (a b result)
  (and
   (verina-basic-83-integer-array-p a)
   (verina-basic-83-integer-array-p b)
   (verina-basic-83-integer-array-p result)
   (equal
    (len result)
    (+ (len a) (len b)))
   (verina-basic-83-first-segment-correct-p
    a
    result)
   (verina-basic-83-second-segment-correct-p
    a
    b
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every pair of finite integer arrays, assumes exactly the source True
;; precondition, and applies the complete postcondition to the exact
;; executable result.

(defun-sk
    verina-basic-83-concat-spec-satisfied-statement
    ()
  (forall (a b)
    (implies
     (and
      (verina-basic-83-integer-array-p a)
      (verina-basic-83-integer-array-p b)
      (verina-basic-83-concat-precond a b))
     (verina-basic-83-concat-postcond
      a
      b
      (verina-basic-83-concat a b)))))

(value-triple :itpeval-statement-checked)
:q
