;; Statement-only formalization of VERINA corpus artifact verina_basic_102,
;; catalog title "twoSum": under the existence precondition, a deterministic
;; nested scan of an integer array returns the lexicographically first
;; increasing pair of indices whose entries sum to the target. This file
;; contains no proof.

(in-package "ACL2")

;; A Lean Array Int is represented exactly by its finite sequence of entries:
;; a proper ACL2 list whose elements are integers.

(defun verina-basic-102-integer-array-p (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (integerp (car nums))
       (verina-basic-102-integer-array-p (cdr nums)))
    (equal nums nil)))

;; Array.get! returns the in-bounds entry and the inhabited integer default
;; zero otherwise.

(defun verina-basic-102-nth-default-zero (index nums)
  (if (and
       (natp index)
       (< index (len nums)))
      (nth index nums)
    0))

;; This is List.all for the predicate that VALUE does not sum with any entry
;; of NUMS to TARGET.

(defun verina-basic-102-no-sum-with-all-p
    (value nums target)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (not (equal (+ value (car nums)) target))
       (verina-basic-102-no-sum-with-all-p
        value
        (cdr nums)
        target))
    (equal nums nil)))

;; These recursive clauses exactly render
;; List.Pairwise (fun left right => left + right != target).

(defun verina-basic-102-pairwise-no-sum-p
    (nums target)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (verina-basic-102-no-sum-with-all-p
        (car nums)
        (cdr nums)
        target)
       (verina-basic-102-pairwise-no-sum-p
        (cdr nums)
        target))
    (equal nums nil)))

(defun verina-basic-102-two-sum-precond (nums target)
  (and
   (< 1 (len nums))
   (not
    (verina-basic-102-pairwise-no-sum-p
     nums
     target))))

;; Option (Nat x Nat) is represented by :none or by
;; (:some . (first-index . second-index)).

(defun verina-basic-102-some-index-pair
    (first-index second-index)
  (cons :some (cons first-index second-index)))

(defun verina-basic-102-option-index-pair-p (result)
  (or
   (equal result :none)
   (and
    (consp result)
    (equal (car result) :some)
    (consp (cdr result))
    (natp (car (cdr result)))
    (natp (cdr (cdr result))))))

;; FUEL is exactly nums.size - j. This is the source-local INNER recursion:
;; it checks j, j+1, ... in order and returns the first matching pair.

(defun verina-basic-102-inner
    (nums target i j fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      :none
    (if
        (equal
         (+
          (verina-basic-102-nth-default-zero i nums)
          (verina-basic-102-nth-default-zero j nums))
         target)
        (verina-basic-102-some-index-pair i j)
      (verina-basic-102-inner
       nums
       target
       i
       (+ j 1)
       (- fuel 1)))))

;; FUEL is exactly nums.size - 1 - i. This is the source-local OUTER
;; recursion: for each increasing i it runs INNER on precisely the later
;; indices, advancing i only when that scan finds no matching partner.

(defun verina-basic-102-outer
    (nums target i fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      :none
    (let ((inner-result
           (verina-basic-102-inner
            nums
            target
            i
            (+ i 1)
            fuel)))
      (if (and
           (consp inner-result)
           (equal (car inner-result) :some))
          inner-result
        (verina-basic-102-outer
         nums
         target
         (+ i 1)
         (- fuel 1))))))

;; The source initializes OUTER at zero. The proof-valued precondition
;; argument has no computational effect and is erased.

(defun verina-basic-102-two-sum-option (nums target)
  (verina-basic-102-outer
   nums
   target
   0
   (nfix (- (len nums) 1))))

;; Lean panic at this inhabited pair type returns its default value (0, 0).
;; Under the source precondition the :none branch is unreachable.

(defun verina-basic-102-two-sum (nums target)
  (let ((search-result
         (verina-basic-102-two-sum-option
          nums
          target)))
    (if (and
         (consp search-result)
         (equal (car search-result) :some))
        (cdr search-result)
      (cons 0 0))))

;; These are exact total representations of List.drop and List.take on
;; natural counts.

(defun verina-basic-102-drop (count nums)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nums
    (if (consp nums)
        (verina-basic-102-drop
         (- count 1)
         (cdr nums))
      nil)))

(defun verina-basic-102-take (count nums)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (if (consp nums)
        (cons
         (car nums)
         (verina-basic-102-take
          (- count 1)
          (cdr nums)))
      nil)))

;; PREFIX is nums.toList.take i. Starting INDEX at zero reproduces zipIdx;
;; for every earlier first index i', DROP checks every possible later partner.

(defun verina-basic-102-no-earlier-pair-p
    (prefix whole index target)
  (declare (xargs :measure (acl2-count prefix)))
  (if (consp prefix)
      (and
       (verina-basic-102-no-sum-with-all-p
        (car prefix)
        (verina-basic-102-drop
         (+ index 1)
         whole)
        target)
       (verina-basic-102-no-earlier-pair-p
        (cdr prefix)
        whole
        (+ index 1)
        target))
    (equal prefix nil)))

;; Lean's natural expression j - i - 1 truncates after each subtraction.

(defun verina-basic-102-partners-before-count (i j)
  (nfix (- (nfix (- j i)) 1)))

(defun verina-basic-102-index-pair-p (result)
  (and
   (consp result)
   (natp (car result))
   (natp (cdr result))))

(defun verina-basic-102-two-sum-postcond
    (nums target result)
  (and
   (verina-basic-102-integer-array-p nums)
   (integerp target)
   (verina-basic-102-index-pair-p result)
   (let ((i (car result))
         (j (cdr result)))
     (and
      (< i j)
      (< j (len nums))
      (equal
       (+
        (verina-basic-102-nth-default-zero i nums)
        (verina-basic-102-nth-default-zero j nums))
       target)
      (verina-basic-102-no-earlier-pair-p
       (verina-basic-102-take i nums)
       nums
       0
       target)
      (verina-basic-102-no-sum-with-all-p
       (verina-basic-102-nth-default-zero i nums)
       (verina-basic-102-take
        (verina-basic-102-partners-before-count i j)
        (verina-basic-102-drop
         (+ i 1)
         nums))
       target)))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the Array Int and Int domains and the complete source
;; precondition; its conclusion applies the complete postcondition to the
;; exact executable result.

(defun
    verina-basic-102-two-sum-spec-satisfied-statement
    (nums target)
  (implies
   (and
    (verina-basic-102-integer-array-p nums)
    (integerp target)
    (verina-basic-102-two-sum-precond
     nums
     target))
   (verina-basic-102-two-sum-postcond
    nums
    target
    (verina-basic-102-two-sum
     nums
     target))))

(value-triple :itpeval-statement-checked)
:q
