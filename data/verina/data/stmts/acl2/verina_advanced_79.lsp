;; Statement-only formalization of VERINA corpus artifact verina_advanced_79,
;; catalog title "twoSum": a deterministic nested search on an integer list
;; returns the lexicographically first increasing pair of indices whose values
;; sum to the target, or none when no such pair exists. This file contains no
;; proof.

(in-package "ACL2")

;; Lean's List Int domain is represented by proper ACL2 lists of integers.

(defun verina-advanced-79-integer-listp (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (integerp (car nums))
       (verina-advanced-79-integer-listp (cdr nums)))
    (equal nums nil)))

;; The source precondition is True.

(defun verina-advanced-79-two-sum-precond (nums target)
  (declare (ignore nums target))
  t)

;; Option (Nat x Nat) is represented by :none or by
;; (:some . (first-index . second-index)).

(defun verina-advanced-79-option-index-pair-p (result)
  (or
   (equal result :none)
   (and
    (consp result)
    (equal (car result) :some)
    (consp (cdr result))
    (natp (car (cdr result)))
    (natp (cdr (cdr result))))))

(defun verina-advanced-79-some-index (index)
  (cons :some index))

(defun verina-advanced-79-some-index-pair
    (first-index second-index)
  (cons :some (cons first-index second-index)))

;; This is the source-local inner recursion. It scans the suffix from left to
;; right and returns the first index whose value forms the target sum with X.

(defun verina-advanced-79-inner
    (remaining x target index)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (equal (+ x (car remaining)) target)
          (verina-advanced-79-some-index index)
        (verina-advanced-79-inner
         (cdr remaining)
         x
         target
         (+ index 1)))
    :none))

;; This is the source-local outer recursion. For each list position it runs
;; INNER on exactly the later positions, then advances only if no partner was
;; found. Thus its traversal order is lexicographic in the two indices.

(defun verina-advanced-79-outer
    (remaining target index)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((inner-result
             (verina-advanced-79-inner
              (cdr remaining)
              (car remaining)
              target
              (+ index 1))))
        (if (and
             (consp inner-result)
             (equal (car inner-result) :some))
            (verina-advanced-79-some-index-pair
             index
             (cdr inner-result))
          (verina-advanced-79-outer
           (cdr remaining)
           target
           (+ index 1))))
    :none))

;; The proof-valued True precondition argument is computationally irrelevant
;; in Lean and is erased here. The remaining call is exactly outer nums 0.

(defun verina-advanced-79-two-sum (nums target)
  (verina-advanced-79-outer nums target 0))

;; These are exact total representations of List.drop and List.take on natural
;; counts.

(defun verina-advanced-79-drop (count nums)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nums
    (if (consp nums)
        (verina-advanced-79-drop
         (- count 1)
         (cdr nums))
      nil)))

(defun verina-advanced-79-take (count nums)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (if (consp nums)
        (cons
         (car nums)
         (verina-advanced-79-take
          (- count 1)
          (cdr nums)))
      nil)))

;; This is List.all for the predicate that a fixed value does not sum with
;; any element of NUMS to TARGET.

(defun verina-advanced-79-no-sum-with-all-p
    (value nums target)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (not (equal (+ value (car nums)) target))
       (verina-advanced-79-no-sum-with-all-p
        value
        (cdr nums)
        target))
    (equal nums nil)))

;; These two predicates exactly render
;; List.Pairwise (fun left right => left + right != target).

(defun verina-advanced-79-pairwise-no-sum-p
    (nums target)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (verina-advanced-79-no-sum-with-all-p
        (car nums)
        (cdr nums)
        target)
       (verina-advanced-79-pairwise-no-sum-p
        (cdr nums)
        target))
    (equal nums nil)))

;; PREFIX is nums.take i. Attaching INDEX = 0 and advancing it reproduces
;; zipIdx. For every earlier first index i', DROP checks all possible later
;; partners, exactly matching the first lexicographic-minimality clause.

(defun verina-advanced-79-no-earlier-pair-p
    (prefix whole index target)
  (declare (xargs :measure (acl2-count prefix)))
  (if (consp prefix)
      (and
       (verina-advanced-79-no-sum-with-all-p
        (car prefix)
        (verina-advanced-79-drop
         (+ index 1)
         whole)
        target)
       (verina-advanced-79-no-earlier-pair-p
        (cdr prefix)
        whole
        (+ index 1)
        target))
    (equal prefix nil)))

;; Lean's natural expression j - i - 1 uses truncated subtraction at each
;; step.

(defun verina-advanced-79-partners-before-count (i j)
  (nfix (- (nfix (- j i)) 1)))

(defun verina-advanced-79-two-sum-postcond
    (nums target result)
  (and
   (verina-advanced-79-integer-listp nums)
   (integerp target)
   (verina-advanced-79-option-index-pair-p result)
   (if (equal result :none)
       (verina-advanced-79-pairwise-no-sum-p
        nums
        target)
     (let* ((index-pair (cdr result))
            (i (car index-pair))
            (j (cdr index-pair)))
       (and
        (< i j)
        (< j (len nums))
        (equal
         (+ (nth i nums) (nth j nums))
         target)
        (verina-advanced-79-no-earlier-pair-p
         (verina-advanced-79-take i nums)
         nums
         0
         target)
        (verina-advanced-79-no-sum-with-all-p
         (nth i nums)
         (verina-advanced-79-take
          (verina-advanced-79-partners-before-count i j)
          (verina-advanced-79-drop
           (+ i 1)
           nums))
         target))))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int and Int binder domains and the True
;; precondition; its conclusion connects the complete postcondition to the
;; exact executable result.

(defun
    verina-advanced-79-two-sum-spec-satisfied-statement
    (nums target)
  (implies
   (and
    (verina-advanced-79-integer-listp nums)
    (integerp target)
    (verina-advanced-79-two-sum-precond
     nums
     target))
   (verina-advanced-79-two-sum-postcond
    nums
    target
    (verina-advanced-79-two-sum
     nums
     target))))

(value-triple :itpeval-statement-checked)
:q
