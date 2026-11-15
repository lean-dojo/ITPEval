;; Statement-only formalization of VERINA corpus artifact verina_advanced_52,
;; "minOperations": a deterministic scan from the end of a natural-number
;; list returns the minimum prefix length of that scan containing every
;; target from 1 through k. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-52-nat-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (natp (car xs))
       (verina-advanced-52-nat-listp (cdr xs)))
    (equal xs nil)))

;; Recursing downward from K checks exactly the source target list
;; (List.range k).map (· + 1), namely 1,...,k. For k = 0 the target list is
;; empty, so List.all is true.

(defun verina-advanced-52-targets-present-p (k xs)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      t
    (and
     (member-equal k xs)
     (verina-advanced-52-targets-present-p
      (- k 1)
      xs))))

(defun verina-advanced-52-min-operations-precond
    (nums k)
  (verina-advanced-52-targets-present-p k nums))

;; This is the source local LOOP. REMAINING is nums.reverse, COLLECTED stores
;; the distinct relevant values seen so far, COLLECTED-COUNT is its source Nat
;; counter, and OPS is incremented for every inspected element. The function
;; returns immediately when the newly collected count reaches k.

(defun verina-advanced-52-loop
    (remaining collected collected-count ops k)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let* ((head (car remaining))
             (tail (cdr remaining))
             (ops-prime (+ ops 1)))
        (if (and
             (< 0 head)
             (<= head k)
             (not (member-equal head collected)))
            (let* ((collected-prime
                    (cons head collected))
                   (collected-count-prime
                    (+ collected-count 1)))
              (if (equal collected-count-prime k)
                  ops-prime
                (verina-advanced-52-loop
                 tail
                 collected-prime
                 collected-count-prime
                 ops-prime
                 k)))
          (verina-advanced-52-loop
           tail
           collected
           collected-count
           ops-prime
           k)))
    ops))

;; The source proof-valued precondition argument is computationally
;; irrelevant. This definition preserves the k = 0 branch and otherwise calls
;; LOOP on nums.reverse with the same empty collection and zero counters.

(defun verina-advanced-52-min-operations (nums k)
  (if (equal k 0)
      0
    (verina-advanced-52-loop
     (reverse nums)
     nil
     0
     0
     k)))

;; This is List.take on a natural count.

(defun verina-advanced-52-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (if (consp xs)
        (cons
         (car xs)
         (verina-advanced-52-take
          (- count 1)
          (cdr xs)))
      nil)))

;; The two conjuncts are the source postcondition: all targets occur in the
;; processed prefix of nums.reverse, and either one fewer operation is
;; insufficient or the zero-result edge case has k = 0.

(defun verina-advanced-52-min-operations-postcond
    (nums k result)
  (let* ((processed
          (verina-advanced-52-take
           result
           (reverse nums)))
         (collected-all
          (verina-advanced-52-targets-present-p
           k
           processed))
         (is-minimal
          (if (< 0 result)
              (not
               (verina-advanced-52-targets-present-p
                k
                (verina-advanced-52-take
                 (- result 1)
                 (reverse nums))))
            (equal k 0))))
    (and
     (verina-advanced-52-nat-listp nums)
     (natp k)
     (natp result)
     collected-all
     is-minimal)))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Nat and Nat binder domains together with the
;; complete source precondition; its conclusion applies the complete
;; postcondition to the exact executable result.

(defun verina-advanced-52-min-operations-spec-satisfied-statement
    (nums k)
  (implies
   (and
    (verina-advanced-52-nat-listp nums)
    (natp k)
    (verina-advanced-52-min-operations-precond
     nums
     k))
   (verina-advanced-52-min-operations-postcond
    nums
    k
    (verina-advanced-52-min-operations nums k))))

(value-triple :itpeval-statement-checked)
:q
