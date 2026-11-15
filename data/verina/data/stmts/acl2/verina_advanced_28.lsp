;; Statement-only formalization of VERINA corpus artifact verina_advanced_28,
;; "longestConsecutive": a deterministic set-backed scan computes the maximum
;; length of a consecutive-integer streak in a duplicate-free integer list,
;; together with its exhaustive sorted-sublist contract. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-28-integer-listp (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (integerp (car nums))
       (verina-advanced-28-integer-listp (cdr nums)))
    (equal nums nil)))

;; This is List.Nodup: every head is absent from its tail, recursively.

(defun verina-advanced-28-no-duplicates-p (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (not (member-equal (car nums) (cdr nums)))
       (verina-advanced-28-no-duplicates-p (cdr nums)))
    (equal nums nil)))

(defun verina-advanced-28-longest-consecutive-precond (nums)
  (verina-advanced-28-no-duplicates-p nums))

;; The source HashSet is observed only through insertion and membership.
;; A duplicate-free association list therefore gives an exact extensional
;; representation of the source set, independently of hash-table layout.

(defun verina-advanced-28-set-insert (x set)
  (if (member-equal x set)
      set
    (cons x set)))

(defun verina-advanced-28-build-set (remaining set)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-28-build-set
       (cdr remaining)
       (verina-advanced-28-set-insert
        (car remaining)
        set))
    set))

;; This is the bounded inner for-loop. A failed membership test implements
;; break; a successful test advances curr and length exactly once.

(defun verina-advanced-28-extend-run
    (curr length remaining-steps set)
  (declare (xargs :measure (nfix remaining-steps)))
  (if (zp remaining-steps)
      length
    (if (member-equal (+ curr 1) set)
        (verina-advanced-28-extend-run
         (+ curr 1)
         (+ length 1)
         (- remaining-steps 1)
         set)
      length)))

(defun verina-advanced-28-nat-max (left right)
  (if (< left right) right left))

;; Scanning REMAINING in input order is the source outer for-loop. A run is
;; considered only when x - 1 is absent from the completed set.

(defun verina-advanced-28-scan
    (remaining set inner-step-count max-length)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let* ((x (car remaining))
             (candidate-length
              (if (member-equal (- x 1) set)
                  max-length
                (verina-advanced-28-extend-run
                 x
                 1
                 inner-step-count
                 set)))
             (next-max
              (verina-advanced-28-nat-max
               max-length
               candidate-length)))
        (verina-advanced-28-scan
         (cdr remaining)
         set
         inner-step-count
         next-max))
    max-length))

;; The proof-valued precondition argument is computationally irrelevant.
;; These folds preserve set construction, both bounded loops, and Nat.max.

(defun verina-advanced-28-longest-consecutive (nums)
  (let ((set
         (verina-advanced-28-build-set nums nil)))
    (verina-advanced-28-scan
     nums
     set
     (len nums)
     0)))

;; Insertion sorting an integer list is extensionally identical to the
;; source's mergeSort result: both return the unique nondecreasing permutation.

(defun verina-advanced-28-insert-sorted (x sorted)
  (declare (xargs :measure (acl2-count sorted)))
  (if (consp sorted)
      (if (<= x (car sorted))
          (cons x sorted)
        (cons
         (car sorted)
         (verina-advanced-28-insert-sorted
          x
          (cdr sorted))))
    (list x)))

(defun verina-advanced-28-sort (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (verina-advanced-28-insert-sorted
       (car nums)
       (verina-advanced-28-sort (cdr nums)))
    nil))

;; DROP, TAKE, and EXTRACT reproduce List.extract start stop, including
;; truncated natural subtraction and truncation at the end of the list.

(defun verina-advanced-28-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      xs
    (if (consp xs)
        (verina-advanced-28-drop
         (- count 1)
         (cdr xs))
      nil)))

(defun verina-advanced-28-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (if (consp xs)
        (cons
         (car xs)
         (verina-advanced-28-take
          (- count 1)
          (cdr xs)))
      nil)))

(defun verina-advanced-28-extract (xs start stop)
  (verina-advanced-28-take
   (nfix (- stop start))
   (verina-advanced-28-drop start xs)))

;; Starting with the first element, EXPECTED increases by one at each
;; zero-based zip index. Together with the empty-list branch, this is exactly
;; isConsecutive's length-zero disjunction and zipIdx.all test.

(defun verina-advanced-28-consecutive-from-p
    (seq expected)
  (declare (xargs :measure (acl2-count seq)))
  (if (consp seq)
      (and
       (equal (car seq) expected)
       (verina-advanced-28-consecutive-from-p
        (cdr seq)
        (+ expected 1)))
    (equal seq nil)))

(defun verina-advanced-28-is-consecutive-p (seq)
  (or
   (equal seq nil)
   (verina-advanced-28-consecutive-from-p
    seq
    (car seq))))

;; This loop maps lengths 0,...,nums.length-start to extracts at one start,
;; filters by isConsecutive, and maps each survivor to its actual length.

(defun verina-advanced-28-lengths-at-start
    (sorted start length remaining-lengths)
  (declare (xargs :measure (nfix remaining-lengths)))
  (if (zp remaining-lengths)
      nil
    (let* ((sublist
            (verina-advanced-28-extract
             sorted
             start
             (+ start length)))
           (rest
            (verina-advanced-28-lengths-at-start
             sorted
             start
             (+ length 1)
             (- remaining-lengths 1))))
      (if (verina-advanced-28-is-consecutive-p sublist)
          (cons (len sublist) rest)
        rest))))

;; Increasing START over exactly nums.length positions and appending each
;; per-start list is the source List.range/flatMap traversal.

(defun verina-advanced-28-consecutive-sublist-lengths-from
    (sorted start remaining-starts total-length)
  (declare (xargs :measure (nfix remaining-starts)))
  (if (zp remaining-starts)
      nil
    (append
     (verina-advanced-28-lengths-at-start
      sorted
      start
      0
      (+ (nfix (- total-length start)) 1))
     (verina-advanced-28-consecutive-sublist-lengths-from
      sorted
      (+ start 1)
      (- remaining-starts 1)
      total-length))))

(defun verina-advanced-28-consecutive-sublist-lengths (nums)
  (let* ((sorted (verina-advanced-28-sort nums))
         (length (len nums)))
    (verina-advanced-28-consecutive-sublist-lengths-from
     sorted
     0
     length
     length)))

(defun verina-advanced-28-contains-length-p
    (lengths result)
  (declare (xargs :measure (acl2-count lengths)))
  (if (consp lengths)
      (or
       (equal (car lengths) result)
       (verina-advanced-28-contains-length-p
        (cdr lengths)
        result))
    nil))

(defun verina-advanced-28-all-lengths-at-most-p
    (lengths result)
  (declare (xargs :measure (acl2-count lengths)))
  (if (consp lengths)
      (and
       (<= (car lengths) result)
       (verina-advanced-28-all-lengths-at-most-p
        (cdr lengths)
        result))
    t))

(defun verina-advanced-28-longest-consecutive-postcond
    (nums result)
  (let ((consecutive-sublist-lengths
         (verina-advanced-28-consecutive-sublist-lengths
          nums)))
    (and
     (verina-advanced-28-integer-listp nums)
     (natp result)
     (implies
      (equal nums nil)
      (equal result 0))
     (implies
      (not (equal nums nil))
      (and
       (verina-advanced-28-contains-length-p
        consecutive-sublist-lengths
        result)
       (verina-advanced-28-all-lengths-at-most-p
        consecutive-sublist-lengths
        result))))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and List.Nodup precondition, while
;; its conclusion applies the full postcondition to the executable result.

(defun
    verina-advanced-28-longest-consecutive-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-28-integer-listp nums)
    (verina-advanced-28-longest-consecutive-precond nums))
   (verina-advanced-28-longest-consecutive-postcond
    nums
    (verina-advanced-28-longest-consecutive nums))))

(value-triple :itpeval-statement-checked)
:q
