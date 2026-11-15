;; Statement-only formalization of VERINA corpus artifact verina_basic_106,
;; catalog title "arraySum": a deterministic integer-array program computes
;; the element-wise sums of two equal-length arrays, with its complete size
;; and pointwise correctness contract. This file contains no proof.

(in-package "ACL2")

;; A Lean Array Int is represented exactly by its finite sequence of entries:
;; a proper ACL2 list whose elements are integers.

(defun verina-basic-106-integer-array-p (array)
  (declare (xargs :measure (acl2-count array)))
  (if (consp array)
      (and
       (integerp (car array))
       (verina-basic-106-integer-array-p
        (cdr array)))
    (equal array nil)))

(defun verina-basic-106-array-sum-precond (a b)
  (equal (len a) (len b)))

;; Array.get! returns the in-bounds entry and the inhabited integer default
;; zero otherwise. The source loop also makes its bounds checks explicit.

(defun verina-basic-106-nth-default-zero
    (index array)
  (if (and
       (natp index)
       (< index (len array)))
      (nth index array)
    0))

;; This total list update agrees with Array.set!: it replaces an in-bounds
;; entry and leaves the represented array unchanged when the index is outside
;; its bounds.

(defun verina-basic-106-set-at
    (index value array)
  (declare (xargs :measure (nfix index)))
  (if (consp array)
      (if (zp index)
          (cons value (cdr array))
        (cons
         (car array)
         (verina-basic-106-set-at
          (- index 1)
          value
          (cdr array))))
    nil))

;; Array.mkArray LEN 0 is the proper list containing exactly LEN integer
;; zeroes.

(defun verina-basic-106-zero-array (length)
  (declare (xargs :measure (nfix length)))
  (if (zp length)
      nil
    (cons
     0
     (verina-basic-106-zero-array
      (- length 1)))))

;; FUEL is exactly LEN - I. Each recursive step performs the source loop body
;; at index I, including both default-zero reads and the Array.set! update,
;; before advancing to I + 1.

(defun verina-basic-106-loop-fuel
    (a b length i c fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      c
    (if (and
         (natp length)
         (natp i)
         (< i length))
        (let* ((a-value
                (verina-basic-106-nth-default-zero
                 i
                 a))
               (b-value
                (verina-basic-106-nth-default-zero
                 i
                 b))
               (new-c
                (verina-basic-106-set-at
                 i
                 (+ a-value b-value)
                 c)))
          (verina-basic-106-loop-fuel
           a
           b
           length
           (+ i 1)
           new-c
           (- fuel 1)))
      c)))

(defun verina-basic-106-loop
    (a b length i c)
  (verina-basic-106-loop-fuel
   a
   b
   length
   i
   c
   (nfix (- length i))))

;; The proof-valued precondition argument has no computational effect and is
;; erased. Under that precondition the mismatch panic branch is unreachable;
;; these bindings preserve the source initialization and exact call to LOOP.

(defun verina-basic-106-array-sum (a b)
  (let* ((length (len a))
         (c
          (verina-basic-106-zero-array
           length)))
    (verina-basic-106-loop
     a
     b
     length
     0
     c)))

;; This predicate preserves the source postcondition's universal Nat index
;; binder and its default-zero array reads.

(defun-sk verina-basic-106-sums-at-every-index-p
    (a b result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len a)))
     (equal
      (+
       (verina-basic-106-nth-default-zero i a)
       (verina-basic-106-nth-default-zero i b))
      (verina-basic-106-nth-default-zero
       i
       result)))))

(defun verina-basic-106-array-sum-postcond
    (a b result)
  (and
   (equal (len result) (len a))
   (verina-basic-106-sums-at-every-index-p
    a
    b
    result)))

;; This predicate is the unproved final correctness proposition. It preserves
;; both arbitrary Array Int inputs and the equal-length precondition, and
;; applies the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-106-array-sum-spec-satisfied-statement
    ()
  (forall (a b)
    (implies
     (and
      (verina-basic-106-integer-array-p a)
      (verina-basic-106-integer-array-p b)
      (verina-basic-106-array-sum-precond
       a
       b))
     (verina-basic-106-array-sum-postcond
      a
      b
      (verina-basic-106-array-sum
       a
       b)))))

(value-triple :itpeval-statement-checked)
:q
