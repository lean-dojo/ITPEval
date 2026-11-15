;; Statement-only formalization of VERINA corpus artifact verina_basic_85,
;; catalog title "reverse": a deterministic integer-array program swaps
;; symmetric entries through the first half of the array and returns its
;; pointwise reversal with unchanged size. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-85-integer-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-85-integer-array-p
        (cdr a)))
    (equal a nil)))

;; The source precondition is True. The Array Int binder domain remains
;; explicit in the final correctness proposition.

(defun verina-basic-85-reverse-precond (a)
  (declare (ignore a))
  t)

;; Array.get! on Array Int returns the indexed entry when present and the
;; inhabited integer default zero otherwise.

(defun verina-basic-85-array-read
    (index a)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp a)
        (if (zp index)
            (car a)
          (verina-basic-85-array-read
           (- index 1)
           (cdr a)))
      0)))

;; Array.set! replaces an in-bounds entry and leaves the array unchanged when
;; its natural index is outside the array.

(defun verina-basic-85-array-set
    (index value a)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      a
    (if (consp a)
        (if (zp index)
            (cons value (cdr a))
          (cons
           (car a)
           (verina-basic-85-array-set
            (- index 1)
            value
            (cdr a))))
      nil)))

;; For a natural index I, floor(len(A)/2)-I fuel units are exactly the number
;; of source recursive calls while I < floor(len(A)/2). Every reached I and
;; symmetric J are in bounds, so both set! operations preserve the length and
;; the fuel cannot expire before the source guard becomes false.

(defun verina-basic-85-reverse-core-fuel
    (a i fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or
       (zp fuel)
       (not (natp i))
       (not (< i (floor (len a) 2))))
      a
    (let* ((j (- (- (len a) 1) i))
           (temp
            (verina-basic-85-array-read i a))
           (a-prime
            (verina-basic-85-array-set
             i
             (verina-basic-85-array-read j a)
             a))
           (a-double-prime
            (verina-basic-85-array-set
             j
             temp
             a-prime)))
      (verina-basic-85-reverse-core-fuel
       a-double-prime
       (+ i 1)
       (- fuel 1)))))

;; This preserves the complete source reverse_core helper signature and exact
;; computation on its typed Array Int and Nat arguments.

(defun verina-basic-85-reverse-core (a i)
  (verina-basic-85-reverse-core-fuel
   a
   i
   (nfix (- (floor (len a) 2) i))))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. Calling reverse_core at index zero exactly reproduces the
;; source reverse implementation.

(defun verina-basic-85-reverse (a)
  (verina-basic-85-reverse-core a 0))

;; This predicate preserves the source postcondition's universal Nat
;; quantifier and its exact reversed-index equation at every valid index.

(defun-sk verina-basic-85-pointwise-reversal-p
    (a result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len a)))
     (equal
      (verina-basic-85-array-read i result)
      (verina-basic-85-array-read
       (- (- (len a) 1) i)
       a)))))

;; This is the complete source postcondition: the result is an integer array
;; of the same size as the input and has exactly the source element at the
;; symmetric index. The unused proof-valued precondition argument is erased.

(defun verina-basic-85-reverse-postcond
    (a result)
  (and
   (verina-basic-85-integer-array-p a)
   (verina-basic-85-integer-array-p result)
   (equal (len result) (len a))
   (verina-basic-85-pointwise-reversal-p
    a
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array, assumes exactly the source True
;; precondition, and applies the complete postcondition to the exact
;; executable result.

(defun-sk
    verina-basic-85-reverse-spec-satisfied-statement
    ()
  (forall (a)
    (implies
     (and
      (verina-basic-85-integer-array-p a)
      (verina-basic-85-reverse-precond a))
     (verina-basic-85-reverse-postcond
      a
      (verina-basic-85-reverse a)))))

(value-triple :itpeval-statement-checked)
:q
