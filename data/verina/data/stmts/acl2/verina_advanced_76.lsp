;; Statement-only formalization of VERINA corpus artifact verina_advanced_76,
;; catalog title "topKFrequent": a deterministic integer-list program returns
;; k distinct highest-frequency elements in non-increasing frequency order.
;; This file contains no proof.

(in-package "ACL2")

;; Lean's List Int domain is represented by proper ACL2 lists of integers.

(defun verina-advanced-76-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-76-integer-listp (cdr xs)))
    (equal xs nil)))

;; Only the length of eraseDups is observed by the source precondition.
;; Keeping the last occurrence yields exactly the same distinct-element count.

(defun verina-advanced-76-erase-dups (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (member-equal (car xs) (cdr xs))
          (verina-advanced-76-erase-dups (cdr xs))
        (cons
         (car xs)
         (verina-advanced-76-erase-dups (cdr xs))))
    nil))

(defun verina-advanced-76-top-k-frequent-precond (nums k)
  (<= k (len (verina-advanced-76-erase-dups nums))))

;; Frequency-list entries are dotted pairs (integer . natural-count).
;; The following lookup is the source acc.find? key test.

(defun verina-advanced-76-frequency-key-present-p
    (key frequency-list)
  (declare (xargs :measure (acl2-count frequency-list)))
  (if (consp frequency-list)
      (or
       (equal key (car (car frequency-list)))
       (verina-advanced-76-frequency-key-present-p
        key
        (cdr frequency-list)))
    nil))

;; When find? succeeds, the source maps over the complete accumulator and
;; increments every entry with the matching key.

(defun verina-advanced-76-increment-matching
    (key frequency-list)
  (declare (xargs :measure (acl2-count frequency-list)))
  (if (consp frequency-list)
      (let ((entry (car frequency-list)))
        (cons
         (if (equal key (car entry))
             (cons (car entry) (+ (cdr entry) 1))
           entry)
         (verina-advanced-76-increment-matching
          key
          (cdr frequency-list))))
    nil))

(defun verina-advanced-76-frequency-step
    (frequency-list value)
  (if (verina-advanced-76-frequency-key-present-p
       value
       frequency-list)
      (verina-advanced-76-increment-matching
       value
       frequency-list)
    (append frequency-list (list (cons value 1)))))

;; This accumulator recursion is nums.foldl with initial value [].

(defun verina-advanced-76-build-frequency-list-fold
    (remaining frequency-list)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-76-build-frequency-list-fold
       (cdr remaining)
       (verina-advanced-76-frequency-step
        frequency-list
        (car remaining)))
    frequency-list))

(defun verina-advanced-76-build-frequency-list (nums)
  (verina-advanced-76-build-frequency-list-fold nums nil))

;; This is the source local insertSorted. A strictly larger count is inserted
;; before the current entry; equal counts pass it, preserving stable order.

(defun verina-advanced-76-insert-frequency-entry
    (entry sorted)
  (declare (xargs :measure (acl2-count sorted)))
  (if (consp sorted)
      (if (> (cdr entry) (cdr (car sorted)))
          (cons entry sorted)
        (cons
         (car sorted)
         (verina-advanced-76-insert-frequency-entry
          entry
          (cdr sorted))))
    (list entry)))

;; This accumulator recursion is freqList.foldl with initial value [].

(defun verina-advanced-76-sort-frequency-list-fold
    (remaining sorted)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-76-sort-frequency-list-fold
       (cdr remaining)
       (verina-advanced-76-insert-frequency-entry
        (car remaining)
        sorted))
    sorted))

(defun verina-advanced-76-sort-frequency-list
    (frequency-list)
  (verina-advanced-76-sort-frequency-list-fold
   frequency-list
   nil))

(defun verina-advanced-76-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (if (consp xs)
        (cons
         (car xs)
         (verina-advanced-76-take
          (- count 1)
          (cdr xs)))
      nil)))

(defun verina-advanced-76-frequency-keys (frequency-list)
  (declare (xargs :measure (acl2-count frequency-list)))
  (if (consp frequency-list)
      (cons
       (car (car frequency-list))
       (verina-advanced-76-frequency-keys
        (cdr frequency-list)))
    nil))

;; The proof-valued precondition argument is computationally erased. The two
;; left folds, stable insertion sort, take, and projection otherwise reproduce
;; the complete source implementation.

(defun verina-advanced-76-top-k-frequent (nums k)
  (let* ((frequency-list
          (verina-advanced-76-build-frequency-list nums))
         (sorted
          (verina-advanced-76-sort-frequency-list
           frequency-list)))
    (verina-advanced-76-frequency-keys
     (verina-advanced-76-take k sorted))))

(defun verina-advanced-76-count-equal (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (+
       (if (equal value (car xs)) 1 0)
       (verina-advanced-76-count-equal
        value
        (cdr xs)))
    0))

;; This is result.all (fun x => x in nums).

(defun verina-advanced-76-all-members-p (result nums)
  (declare (xargs :measure (acl2-count result)))
  (if (consp result)
      (and
       (member-equal (car result) nums)
       (verina-advanced-76-all-members-p
        (cdr result)
        nums))
    t))

;; This is List.Pairwise (fun x y => x != y) result.

(defun verina-advanced-76-pairwise-distinct-p (result)
  (declare (xargs :measure (acl2-count result)))
  (if (consp result)
      (and
       (not (member-equal (car result) (cdr result)))
       (verina-advanced-76-pairwise-distinct-p
        (cdr result)))
    t))

;; These predicates reproduce the nested result.all / nums.all frequency
;; comparison, including its membership disjunction for each source element.

(defun verina-advanced-76-all-source-elements-dominated-p
    (x remaining-nums nums result)
  (declare (xargs :measure (acl2-count remaining-nums)))
  (if (consp remaining-nums)
      (let ((y (car remaining-nums)))
        (and
         (or
          (member-equal y result)
          (>=
           (verina-advanced-76-count-equal x nums)
           (verina-advanced-76-count-equal y nums)))
         (verina-advanced-76-all-source-elements-dominated-p
          x
          (cdr remaining-nums)
          nums
          result)))
    t))

(defun verina-advanced-76-all-result-elements-dominant-p
    (remaining-result nums result)
  (declare (xargs :measure (acl2-count remaining-result)))
  (if (consp remaining-result)
      (and
       (verina-advanced-76-all-source-elements-dominated-p
        (car remaining-result)
        nums
        nums
        result)
       (verina-advanced-76-all-result-elements-dominant-p
        (cdr remaining-result)
        nums
        result))
    t))

;; Each entry is (value . zero-based-index), exactly representing List.zipIdx.

(defun verina-advanced-76-zip-index-from (xs index)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (cons
       (cons (car xs) index)
       (verina-advanced-76-zip-index-from
        (cdr xs)
        (+ index 1)))
    nil))

(defun verina-advanced-76-zip-index (xs)
  (verina-advanced-76-zip-index-from xs 0))

;; These predicates exactly reproduce List.Pairwise on result.zipIdx with the
;; implication i < j -> count x >= count y.

(defun verina-advanced-76-ordered-after-first-p
    (first remaining-indexed nums)
  (declare (xargs :measure (acl2-count remaining-indexed)))
  (if (consp remaining-indexed)
      (let ((later (car remaining-indexed)))
        (and
         (implies
          (< (cdr first) (cdr later))
          (>=
           (verina-advanced-76-count-equal
            (car first)
            nums)
           (verina-advanced-76-count-equal
            (car later)
            nums)))
         (verina-advanced-76-ordered-after-first-p
          first
          (cdr remaining-indexed)
          nums)))
    t))

(defun verina-advanced-76-pairwise-frequency-ordered-p
    (indexed-result nums)
  (declare (xargs :measure (acl2-count indexed-result)))
  (if (consp indexed-result)
      (and
       (verina-advanced-76-ordered-after-first-p
        (car indexed-result)
        (cdr indexed-result)
        nums)
       (verina-advanced-76-pairwise-frequency-ordered-p
        (cdr indexed-result)
        nums))
    t))

(defun verina-advanced-76-top-k-frequent-postcond
    (nums k result)
  (and
   (verina-advanced-76-integer-listp nums)
   (natp k)
   (verina-advanced-76-integer-listp result)
   (equal (len result) k)
   (verina-advanced-76-all-members-p result nums)
   (verina-advanced-76-pairwise-distinct-p result)
   (verina-advanced-76-all-result-elements-dominant-p
    result
    nums
    result)
   (verina-advanced-76-pairwise-frequency-ordered-p
    (verina-advanced-76-zip-index result)
    nums)))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int and Nat binders and the distinct-count
;; precondition; its conclusion applies the full postcondition to the exact
;; executable result.

(defun
    verina-advanced-76-top-k-frequent-spec-satisfied-statement
    (nums k)
  (implies
   (and
    (verina-advanced-76-integer-listp nums)
    (natp k)
    (verina-advanced-76-top-k-frequent-precond nums k))
   (verina-advanced-76-top-k-frequent-postcond
    nums
    k
    (verina-advanced-76-top-k-frequent nums k))))

(value-triple :itpeval-statement-checked)
:q
