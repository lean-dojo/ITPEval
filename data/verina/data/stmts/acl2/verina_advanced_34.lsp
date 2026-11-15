;; Statement-only formalization of VERINA corpus artifact verina_advanced_34,
;; "longestIncreasingSubsequence": a deterministic patience-sorting scan with
;; lower-bound binary search returns the length of a longest strictly
;; increasing subsequence of an integer list. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-34-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-34-integer-listp (cdr xs)))
    (equal xs nil)))

;; The source precondition is True. The List Int binder domain is explicit in
;; the final correctness statement.

(defun verina-advanced-34-longest-increasing-subsequence-precond
    (nums)
  (declare (ignore nums))
  t)

;; Lean Array Int is represented by the corresponding proper ACL2 list.
;; Array.get! returns the inhabited integer default 0 outside its bounds.

(defun verina-advanced-34-array-read (index array)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp array)
        (if (zp index)
            (car array)
          (verina-advanced-34-array-read
           (- index 1)
           (cdr array)))
      0)))

;; This internal recursion evaluates the source binarySearchLeft. Its initial
;; fuel is right-left. On natural endpoints with left < right, each source
;; call strictly reduces that width, so fuel cannot expire before the source
;; base case and does not change the computed result.

(defun verina-advanced-34-binary-search-left-fuel
    (sub num left right fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or
       (zp fuel)
       (not (and (natp left) (natp right)))
       (<= right left))
      left
    (let* ((mid
            (floor (+ left right) 2))
           (mid-value
            (verina-advanced-34-array-read mid sub)))
      (if (equal mid-value num)
          (verina-advanced-34-binary-search-left-fuel
           sub
           num
           left
           mid
           (- fuel 1))
        (if (< mid-value num)
            (verina-advanced-34-binary-search-left-fuel
             sub
             num
             (+ mid 1)
             right
             (- fuel 1))
          (verina-advanced-34-binary-search-left-fuel
           sub
           num
           left
           mid
           (- fuel 1)))))))

(defun verina-advanced-34-binary-search-left
    (sub num left right)
  (verina-advanced-34-binary-search-left-fuel
   sub
   num
   left
   right
   (nfix (- right left))))

;; Array.set! at a valid index replaces exactly that entry. This total
;; definition also leaves the array unchanged if the index is out of bounds.

(defun verina-advanced-34-array-set
    (index value array)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      array
    (if (consp array)
        (if (zp index)
            (cons value (cdr array))
          (cons
           (car array)
           (verina-advanced-34-array-set
            (- index 1)
            value
            (cdr array))))
      nil)))

;; This recursion is the source for-loop over nums.tail. SUB is the mutable
;; array state: a larger element is pushed, otherwise the lower-bound position
;; returned by binarySearchLeft is replaced.

(defun verina-advanced-34-scan
    (remaining sub)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let* ((num (car remaining))
             (last-index
              (nfix (- (len sub) 1)))
             (last-value
              (verina-advanced-34-array-read
               last-index
               sub))
             (next-sub
              (if (> num last-value)
                  (append sub (list num))
                (let ((left
                       (verina-advanced-34-binary-search-left
                        sub
                        num
                        0
                        last-index)))
                  (verina-advanced-34-array-set
                   left
                   num
                   sub)))))
        (verina-advanced-34-scan
         (cdr remaining)
         next-sub))
    sub))

;; The proof-valued True precondition argument is computationally irrelevant.
;; Empty input returns zero. Otherwise the singleton head array is scanned
;; through the tail and its final size is embedded into Int.

(defun verina-advanced-34-longest-increasing-subsequence
    (nums)
  (if (endp nums)
      0
    (len
     (verina-advanced-34-scan
      (cdr nums)
      (list (car nums))))))

;; The following fold, prepend-map, and final reversal reproduce the
;; postcondition's local allSubseq expression, including order and
;; multiplicity.

(defun verina-advanced-34-prepend-to-each
    (value subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (cons value (car subsequences))
       (verina-advanced-34-prepend-to-each
        value
        (cdr subsequences)))
    nil))

(defun verina-advanced-34-all-subseq-fold
    (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-34-all-subseq-fold
       (cdr remaining)
       (append
        accumulator
        (verina-advanced-34-prepend-to-each
         (car remaining)
         accumulator)))
    accumulator))

(defun verina-advanced-34-reverse-each
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (reverse (car subsequences))
       (verina-advanced-34-reverse-each
        (cdr subsequences)))
    nil))

(defun verina-advanced-34-all-subseq (nums)
  (verina-advanced-34-reverse-each
   (verina-advanced-34-all-subseq-fold
    nums
    (list nil))))

;; These predicates exactly represent List.Pairwise (fun x y => x < y):
;; every head is less than every later element, recursively.

(defun verina-advanced-34-head-less-than-all-p
    (head tail)
  (declare (xargs :measure (acl2-count tail)))
  (if (consp tail)
      (and
       (< head (car tail))
       (verina-advanced-34-head-less-than-all-p
        head
        (cdr tail)))
    (equal tail nil)))

(defun verina-advanced-34-strictly-increasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (verina-advanced-34-head-less-than-all-p
        (car xs)
        (cdr xs))
       (verina-advanced-34-strictly-increasing-p
        (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-34-filter-increasing
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (if (verina-advanced-34-strictly-increasing-p
           (car subsequences))
          (cons
           (car subsequences)
           (verina-advanced-34-filter-increasing
            (cdr subsequences)))
        (verina-advanced-34-filter-increasing
         (cdr subsequences)))
    nil))

(defun verina-advanced-34-map-lengths
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (len (car subsequences))
       (verina-advanced-34-map-lengths
        (cdr subsequences)))
    nil))

(defun verina-advanced-34-contains-length-p
    (lengths result)
  (declare (xargs :measure (acl2-count lengths)))
  (if (consp lengths)
      (or
       (equal (car lengths) result)
       (verina-advanced-34-contains-length-p
        (cdr lengths)
        result))
    nil))

(defun verina-advanced-34-all-lengths-at-most-p
    (lengths result)
  (declare (xargs :measure (acl2-count lengths)))
  (if (consp lengths)
      (and
       (<= (car lengths) result)
       (verina-advanced-34-all-lengths-at-most-p
        (cdr lengths)
        result))
    t))

(defun verina-advanced-34-longest-increasing-subsequence-postcond
    (nums result)
  (let* ((all-subseq
          (verina-advanced-34-all-subseq nums))
         (increasing-subseq
          (verina-advanced-34-filter-increasing
           all-subseq))
         (increasing-subseq-lengths
          (verina-advanced-34-map-lengths
           increasing-subseq)))
    (and
     (verina-advanced-34-integer-listp nums)
     (integerp result)
     (verina-advanced-34-contains-length-p
      increasing-subseq-lengths
      result)
     (verina-advanced-34-all-lengths-at-most-p
      increasing-subseq-lengths
      result))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and True precondition, while its
;; conclusion applies the full postcondition to the executable result.

(defun
    verina-advanced-34-longest-increasing-subsequence-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-34-integer-listp nums)
    (verina-advanced-34-longest-increasing-subsequence-precond
     nums))
   (verina-advanced-34-longest-increasing-subsequence-postcond
    nums
    (verina-advanced-34-longest-increasing-subsequence
     nums))))

(value-triple :itpeval-statement-checked)
:q
