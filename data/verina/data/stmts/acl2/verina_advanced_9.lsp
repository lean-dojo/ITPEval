;; Statement-only formalization of VERINA corpus artifact verina_advanced_9,
;; catalog title countSumDivisibleBy: the executable descending count of
;; naturals below n whose decimal digit sum is divisible by positive d,
;; together with its filtered-range correctness contract. This file contains
;; no proof.

(in-package "ACL2")

;; Lean's Nat.mod returns its left operand when the divisor is zero.  The
;; positive-divisor precondition governs the final program call, but retaining
;; this branch also preserves the separately defined source helper on all
;; natural inputs.

(defun verina-advanced-9-nat-mod (x d)
  (if (and (natp x) (natp d))
      (if (zp d)
          x
        (mod x d))
    0))

;; Fuel starts at X.  Each nonzero decimal-stripping step replaces N by
;; floor(N/10), which is strictly smaller than positive N, so the fuel cannot
;; expire before N reaches zero.  Thus this is the exact source tail recursion
;; on natural inputs, rather than a bounded approximation.

(defun verina-advanced-9-sum-of-digits-go
    (n accumulator fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp n)
      accumulator
    (if (zp fuel)
        accumulator
      (verina-advanced-9-sum-of-digits-go
       (floor n 10)
       (+ accumulator
          (verina-advanced-9-nat-mod n 10))
       (- fuel 1)))))

(defun verina-advanced-9-sum-of-digits (x)
  (verina-advanced-9-sum-of-digits-go
   (nfix x) 0 (nfix x)))

(defun verina-advanced-9-count-sum-divisible-by-precond
    (n d)
  (and
   (natp n)
   (natp d)
   (< 0 d)))

(defun verina-advanced-9-is-sum-divisible-by (x d)
  (equal
   (verina-advanced-9-nat-mod
    (verina-advanced-9-sum-of-digits x)
    d)
   0))

;; This is the source-local GO implementation.  For positive I it tests I-1,
;; updates the natural accumulator, and descends, thereby visiting exactly
;; n-1, ..., 1, 0.

(defun verina-advanced-9-count-go (i accumulator d)
  (declare (xargs :measure (nfix i)))
  (if (zp i)
      accumulator
    (let* ((previous (- i 1))
           (next-accumulator
            (if
             (verina-advanced-9-is-sum-divisible-by
              previous d)
             (+ accumulator 1)
              accumulator)))
      (verina-advanced-9-count-go
       previous next-accumulator d))))

;; The proof-valued Lean precondition argument is computationally irrelevant;
;; its Boolean content remains explicit in the final correctness predicate.

(defun verina-advanced-9-count-sum-divisible-by (n d)
  (verina-advanced-9-count-go (nfix n) 0 d))

;; The following definitions preserve List.range n, its filter by
;; x < n and digit-sum divisibility, and List.length independently of the
;; descending executable loop above.

(defun verina-advanced-9-range-from (start remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     start
     (verina-advanced-9-range-from
      (+ start 1)
      (- remaining 1)))))

(defun verina-advanced-9-range (n)
  (verina-advanced-9-range-from 0 (nfix n)))

(defun verina-advanced-9-filter-sum-divisible
    (xs n d)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if
       (and
        (< (car xs) n)
        (equal
         (verina-advanced-9-nat-mod
          (verina-advanced-9-sum-of-digits (car xs))
          d)
         0))
       (cons
        (car xs)
        (verina-advanced-9-filter-sum-divisible
         (cdr xs) n d))
        (verina-advanced-9-filter-sum-divisible
         (cdr xs) n d))
    nil))

;; NFIX of an integer difference is Lean's truncated subtraction on naturals.

(defun verina-advanced-9-nat-sub (left right)
  (if (and (natp left) (natp right))
      (nfix (- left right))
    0))

(defun verina-advanced-9-count-sum-divisible-by-postcond
    (n d result)
  (let*
      ((range
        (verina-advanced-9-range n))
       (filtered
        (verina-advanced-9-filter-sum-divisible
         range n d))
       (matching-count
        (len filtered)))
    (and
     (natp n)
     (natp d)
     (natp result)
     (equal
      (verina-advanced-9-nat-sub
       matching-count result)
      0)
     (<= result matching-count))))

;; This predicate is the unproved final correctness proposition, with the
;; exact executable result explicitly supplied to the complete postcondition.

(defun
    verina-advanced-9-count-sum-divisible-by-spec-satisfied-statement
    (n d)
  (implies
   (verina-advanced-9-count-sum-divisible-by-precond n d)
   (verina-advanced-9-count-sum-divisible-by-postcond
    n
    d
    (verina-advanced-9-count-sum-divisible-by n d))))

(value-triple :itpeval-statement-checked)
:q
