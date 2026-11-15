;; Statement-only formalization of VERINA corpus artifact verina_basic_18,
;; catalog title "sumOfDigits": a deterministic natural-number program sums
;; the decimal digits of its input, with correctness stated against the
;; independent digit sum of its decimal representation. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The Nat input domain remains explicit in
;; the final correctness statement.

(defun verina-basic-18-sum-of-digits-precond (n)
  (declare (ignore n))
  t)

;; Fuel starts at N. Every nonzero source step replaces N by floor(N/10), so
;; on natural inputs the recursion reaches zero before the fuel can expire.
;; The fuel is therefore only an ACL2 termination device and adds no cutoff.

(defun verina-basic-18-loop-go (n acc fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp n)
      acc
    (if (zp fuel)
        acc
      (verina-basic-18-loop-go
       (floor n 10)
       (+ acc (mod n 10))
       (- fuel 1)))))

;; This wrapper preserves the source-local loop on its Nat arguments. The
;; proof-valued True precondition argument to sumOfDigits is computationally
;; irrelevant and is erased.

(defun verina-basic-18-loop (n acc)
  (verina-basic-18-loop-go
   (nfix n)
   (nfix acc)
   (nfix n)))

(defun verina-basic-18-sum-of-digits (n)
  (verina-basic-18-loop n 0))

;; Nat.repr yields the one-digit representation "0" for zero and otherwise
;; the ordinary most-significant-first decimal representation. Replacing each
;; character by Char.toNat(c) - Char.toNat('0') gives exactly this digit list.
;; This computation is kept separate from the executable loop, as in the
;; source postcondition.

(defun verina-basic-18-decimal-digits-positive-aux (n fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or
       (not (natp n))
       (zp n)
       (zp fuel))
      nil
    (let ((quotient (floor n 10))
          (digit (mod n 10)))
      (if (equal quotient 0)
          (list digit)
        (append
         (verina-basic-18-decimal-digits-positive-aux
          quotient
          (- fuel 1))
         (list digit))))))

(defun verina-basic-18-decimal-digits (n)
  (if (not (natp n))
      nil
    (if (equal n 0)
        (list 0)
      (verina-basic-18-decimal-digits-positive-aux
       n
       n))))

(defun verina-basic-18-list-sum (digits)
  (declare (xargs :measure (acl2-count digits)))
  (if (consp digits)
      (+ (car digits)
         (verina-basic-18-list-sum (cdr digits)))
    0))

;; Lean Nat subtraction truncates at zero.

(defun verina-basic-18-nat-sub (left right)
  (nfix (- left right)))

(defun verina-basic-18-sum-of-digits-postcond
    (n result)
  (let ((represented-digit-sum
         (verina-basic-18-list-sum
          (verina-basic-18-decimal-digits n))))
    (and
     (natp n)
     (natp result)
     (equal
      (verina-basic-18-nat-sub
       result
       represented-digit-sum)
      0)
     (equal
      (verina-basic-18-nat-sub
       represented-digit-sum
       result)
      0))))

;; This predicate is the unproved final correctness proposition. It preserves
;; the arbitrary Nat input and True precondition, and applies the complete
;; postcondition to the exact executable result.

(defun-sk
    verina-basic-18-sum-of-digits-spec-satisfied-statement
    ()
  (forall (n)
    (implies
     (and
      (natp n)
      (verina-basic-18-sum-of-digits-precond n))
     (verina-basic-18-sum-of-digits-postcond
      n
      (verina-basic-18-sum-of-digits n)))))

(value-triple :itpeval-statement-checked)
:q
