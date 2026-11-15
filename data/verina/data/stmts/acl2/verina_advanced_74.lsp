;; Statement-only formalization of VERINA corpus artifact verina_advanced_74,
;; "solution": the deterministic natural-list program sums the squares of the
;; distinct-element counts of all nonempty contiguous subarrays, with its full
;; precondition, postcondition, and correctness contract. This file contains
;; no proof.

(in-package "ACL2")

;; Lean's List Nat domain is represented by proper ACL2 lists of naturals.

(defun verina-advanced-74-natural-listp (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (natp (car nums))
       (verina-advanced-74-natural-listp (cdr nums)))
    (equal nums nil)))

;; This is nums.all (fun x => 1 <= x /\ x <= 100), including the proper-list
;; empty case.

(defun verina-advanced-74-all-elements-bounded-p (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (natp (car nums))
       (<= 1 (car nums))
       (<= (car nums) 100)
       (verina-advanced-74-all-elements-bounded-p
        (cdr nums)))
    (equal nums nil)))

(defun verina-advanced-74-solution-precond (nums)
  (and
   (verina-advanced-74-natural-listp nums)
   (<= 1 (len nums))
   (<= (len nums) 100)
   (verina-advanced-74-all-elements-bounded-p nums)))

;; These are exact total representations of List.drop and List.take on the
;; natural counts used by both the executable program and its postcondition.

(defun verina-advanced-74-drop (count nums)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nums
    (if (consp nums)
        (verina-advanced-74-drop
         (- count 1)
         (cdr nums))
      nil)))

(defun verina-advanced-74-take (count nums)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (if (consp nums)
        (cons
         (car nums)
         (verina-advanced-74-take
          (- count 1)
          (cdr nums)))
      nil)))

(defun verina-advanced-74-subarray (nums i j)
  (verina-advanced-74-take
   (+ (nfix (- j i)) 1)
   (verina-advanced-74-drop i nums)))

;; A duplicate-free ACL2 list is an exact extensional representation of the
;; source HashSet Nat for the only observation made by the program, its size.
;; Inserting an existing natural leaves the set unchanged; inserting a fresh
;; natural increases its cardinality by one.

(defun verina-advanced-74-hashset-insert (value set)
  (if (member-equal value set)
      set
    (cons value set)))

(defun verina-advanced-74-hashset-fold (remaining set)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-74-hashset-fold
       (cdr remaining)
       (verina-advanced-74-hashset-insert
        (car remaining)
        set))
    set))

(defun verina-advanced-74-executable-distinct-count (nums)
  (len (verina-advanced-74-hashset-fold nums nil)))

;; D and REMAINING reproduce List.range (n - i) in increasing order. Each
;; iteration uses j = i + d and accumulates the square of the HashSet size.

(defun verina-advanced-74-solution-inner-fold
    (nums i d remaining accumulator)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      accumulator
    (let* ((j (+ i d))
           (subarr
            (verina-advanced-74-subarray nums i j))
           (count
            (verina-advanced-74-executable-distinct-count
             subarr)))
      (verina-advanced-74-solution-inner-fold
       nums
       i
       (+ d 1)
       (- remaining 1)
       (+ accumulator (* count count))))))

;; I and REMAINING reproduce List.range n. The accumulator nesting is exactly
;; the source's outer and inner left folds, both initialized at zero.

(defun verina-advanced-74-solution-outer-fold
    (nums n i remaining accumulator)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      accumulator
    (let ((inner-sum
           (verina-advanced-74-solution-inner-fold
            nums
            i
            0
            (nfix (- n i))
            0)))
      (verina-advanced-74-solution-outer-fold
       nums
       n
       (+ i 1)
       (- remaining 1)
       (+ accumulator inner-sum)))))

(defun verina-advanced-74-solution (nums)
  (let ((n (len nums)))
    (verina-advanced-74-solution-outer-fold
     nums
     n
     0
     n
     0)))

;; The postcondition deliberately has its own distinct-count implementation,
;; matching the source local fold: a fresh value is prepended to SEEN, while
;; an already-seen value leaves the accumulator unchanged.

(defun verina-advanced-74-seen-insert (seen value)
  (if (member-equal value seen)
      seen
    (cons value seen)))

(defun verina-advanced-74-seen-fold (remaining seen)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-74-seen-fold
       (cdr remaining)
       (verina-advanced-74-seen-insert
        seen
        (car remaining)))
    seen))

(defun verina-advanced-74-postcondition-distinct-count (nums)
  (len (verina-advanced-74-seen-fold nums nil)))

;; These two folds reproduce the postcondition's expectedSum independently of
;; the executable folds, including both List.range traversal orders.

(defun verina-advanced-74-expected-inner-fold
    (nums i d remaining accumulator)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      accumulator
    (let* ((j (+ i d))
           (subarr
            (verina-advanced-74-subarray nums i j))
           (count
            (verina-advanced-74-postcondition-distinct-count
             subarr)))
      (verina-advanced-74-expected-inner-fold
       nums
       i
       (+ d 1)
       (- remaining 1)
       (+ accumulator (* count count))))))

(defun verina-advanced-74-expected-outer-fold
    (nums n i remaining accumulator)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      accumulator
    (let ((inner-sum
           (verina-advanced-74-expected-inner-fold
            nums
            i
            0
            (nfix (- n i))
            0)))
      (verina-advanced-74-expected-outer-fold
       nums
       n
       (+ i 1)
       (- remaining 1)
       (+ accumulator inner-sum)))))

(defun verina-advanced-74-expected-sum (nums)
  (let ((n (len nums)))
    (verina-advanced-74-expected-outer-fold
     nums
     n
     0
     n
     0)))

;; The source postcondition is itself conditional on the input constraints.
;; RESULT >= 0 remains explicit even though RESULT's Nat domain entails it.

(defun verina-advanced-74-solution-postcond (nums result)
  (and
   (verina-advanced-74-natural-listp nums)
   (natp result)
   (implies
    (verina-advanced-74-solution-precond nums)
    (and
     (<= 0 result)
     (equal
      result
      (verina-advanced-74-expected-sum nums))))))

;; This predicate is the unproved final correctness proposition. The Lean
;; theorem ranges over every List Nat; it does not assume the precondition
;; externally, because that condition is the implication antecedent inside
;; solution_postcond.

(defun verina-advanced-74-solution-spec-satisfied-statement
    (nums)
  (implies
   (verina-advanced-74-natural-listp nums)
   (verina-advanced-74-solution-postcond
    nums
    (verina-advanced-74-solution nums))))

(value-triple :itpeval-statement-checked)
:q
