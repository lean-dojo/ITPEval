;; Statement-only formalization of VERINA corpus artifact verina_advanced_29,
;; "longestGoodSubarray": a deterministic frequency-map sliding-window
;; computation returns the maximum length specified by an exhaustive
;; contiguous-subarray frequency contract. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-29-nat-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (natp (car xs))
       (verina-advanced-29-nat-listp (cdr xs)))
    (equal xs nil)))

;; The source precondition is k > 0. The List Nat and Nat binder domains are
;; made explicit in the final correctness statement.

(defun verina-advanced-29-longest-good-subarray-precond
    (nums k)
  (declare (ignore nums))
  (and
   (natp k)
   (< 0 k)))

;; A source HashMap Nat Nat is represented extensionally by a duplicate-free
;; association list. Only getD, insert, erase, and inspection of stored values
;; are observable, so association-list order and hash layout are irrelevant.

(defun verina-advanced-29-freq-get (key frequencies)
  (let ((entry (assoc-equal key frequencies)))
    (if entry
        (cdr entry)
      0)))

(defun verina-advanced-29-freq-put
    (key value frequencies)
  (declare (xargs :measure (acl2-count frequencies)))
  (if (consp frequencies)
      (if (equal key (car (car frequencies)))
          (cons
           (cons key value)
           (cdr frequencies))
        (cons
         (car frequencies)
         (verina-advanced-29-freq-put
          key
          value
          (cdr frequencies))))
    (list (cons key value))))

(defun verina-advanced-29-freq-erase
    (key frequencies)
  (declare (xargs :measure (acl2-count frequencies)))
  (if (consp frequencies)
      (if (equal key (car (car frequencies)))
          (cdr frequencies)
        (cons
         (car frequencies)
         (verina-advanced-29-freq-erase
          key
          (cdr frequencies))))
    nil))

(defun verina-advanced-29-freq-increment
    (key frequencies)
  (verina-advanced-29-freq-put
   key
   (+ 1
      (verina-advanced-29-freq-get
       key
       frequencies))
   frequencies))

(defun verina-advanced-29-freq-decrement
    (key frequencies)
  (let ((count
         (verina-advanced-29-freq-get
          key
          frequencies)))
    (if (equal count 1)
        (verina-advanced-29-freq-erase
         key
         frequencies)
      (verina-advanced-29-freq-put
       key
       (nfix (- count 1))
       frequencies))))

(defun verina-advanced-29-any-frequency-above-k-p
    (frequencies k)
  (declare (xargs :measure (acl2-count frequencies)))
  (if (consp frequencies)
      (or
       (> (cdr (car frequencies)) k)
       (verina-advanced-29-any-frequency-above-k-p
        (cdr frequencies)
        k))
    nil))

;; Array indexing with ! returns the inhabited Nat default 0 out of bounds.
;; Reachable indices under the positive-k precondition are in bounds, while
;; this definition also preserves the source operation's total default.

(defun verina-advanced-29-array-read (index nums)
  (if (and
       (natp index)
       (< index (len nums)))
      (nth index nums)
    0))

;; The returned pair is (left . frequencies). FUEL is nums.length, exactly the
;; number of source List.range iterations. A good map implements break; a bad
;; map removes the current left element and advances left once.

(defun verina-advanced-29-shrink-loop
    (left frequencies nums k fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (cons left frequencies)
    (if (verina-advanced-29-any-frequency-above-k-p
         frequencies
         k)
        (let* ((left-value
                (verina-advanced-29-array-read
                 left
                 nums))
               (next-frequencies
                (verina-advanced-29-freq-decrement
                 left-value
                 frequencies)))
          (verina-advanced-29-shrink-loop
           (+ left 1)
           next-frequencies
           nums
           k
           (- fuel 1)))
      (cons left frequencies))))

(defun verina-advanced-29-nat-max (left right)
  (if (< left right)
      right
    left))

;; REMAINING traverses the source array in increasing right-index order.
;; Natural subtraction is truncated with NFIX before adding one, exactly as
;; in the source expression right - left + 1.

(defun verina-advanced-29-scan-right
    (remaining nums k right left max-length frequencies inner-fuel)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let* ((next-frequencies
              (verina-advanced-29-freq-increment
               (car remaining)
               frequencies))
             (shrink-result
              (verina-advanced-29-shrink-loop
               left
               next-frequencies
               nums
               k
               inner-fuel))
             (next-left
              (car shrink-result))
             (shrunk-frequencies
              (cdr shrink-result))
             (window-length
              (+ 1
                 (nfix (- right next-left))))
             (next-max-length
              (verina-advanced-29-nat-max
               max-length
               window-length)))
        (verina-advanced-29-scan-right
         (cdr remaining)
         nums
         k
         (+ right 1)
         next-left
         next-max-length
         shrunk-frequencies
         inner-fuel))
    max-length))

;; The proof-valued precondition argument is computationally irrelevant.
;; These definitions preserve Array conversion, mutable state initialization,
;; both bounded loops, HashMap updates, and Nat.max.

(defun verina-advanced-29-longest-good-subarray
    (nums k)
  (verina-advanced-29-scan-right
   nums
   nums
   k
   0
   0
   0
   nil
   (len nums)))

;; DROP and TAKE reproduce the source List.drop and List.take operations.

(defun verina-advanced-29-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      xs
    (if (consp xs)
        (verina-advanced-29-drop
         (- count 1)
         (cdr xs))
      nil)))

(defun verina-advanced-29-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (if (consp xs)
        (cons
         (car xs)
         (verina-advanced-29-take
          (- count 1)
          (cdr xs)))
      nil)))

;; This loop maps lengths 0,...,nums.length-start to drop/take subarrays at
;; one start. The outer loop covers starts 0,...,nums.length, reproducing the
;; source List.range/flatMap traversal including every empty subarray.

(defun verina-advanced-29-subarrays-at-start
    (nums start length remaining-lengths)
  (declare (xargs :measure (nfix remaining-lengths)))
  (if (zp remaining-lengths)
      nil
    (cons
     (verina-advanced-29-take
      length
      (verina-advanced-29-drop start nums))
     (verina-advanced-29-subarrays-at-start
      nums
      start
      (+ length 1)
      (- remaining-lengths 1)))))

(defun verina-advanced-29-all-subarrays-from
    (nums start remaining-starts total-length)
  (declare (xargs :measure (nfix remaining-starts)))
  (if (zp remaining-starts)
      nil
    (append
     (verina-advanced-29-subarrays-at-start
      nums
      start
      0
      (+ 1
         (nfix (- total-length start))))
     (verina-advanced-29-all-subarrays-from
      nums
      (+ start 1)
      (- remaining-starts 1)
      total-length))))

(defun verina-advanced-29-all-subarrays (nums)
  (let ((length (len nums)))
    (verina-advanced-29-all-subarrays-from
     nums
     0
     (+ length 1)
     length)))

;; These definitions reproduce arr.map (fun x => arr.count x) for every
;; subarray, then filter precisely those count lists whose entries are <= k.

(defun verina-advanced-29-list-count (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (+
       (if (equal value (car xs)) 1 0)
       (verina-advanced-29-list-count
        value
        (cdr xs)))
    0))

(defun verina-advanced-29-subarray-frequency-list
    (remaining whole)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (cons
       (verina-advanced-29-list-count
        (car remaining)
        whole)
       (verina-advanced-29-subarray-frequency-list
        (cdr remaining)
        whole))
    nil))

(defun verina-advanced-29-map-subarray-frequencies
    (subarrays)
  (declare (xargs :measure (acl2-count subarrays)))
  (if (consp subarrays)
      (cons
       (verina-advanced-29-subarray-frequency-list
        (car subarrays)
        (car subarrays))
       (verina-advanced-29-map-subarray-frequencies
        (cdr subarrays)))
    nil))

(defun verina-advanced-29-all-counts-at-most-k-p
    (counts k)
  (declare (xargs :measure (acl2-count counts)))
  (if (consp counts)
      (and
       (<= (car counts) k)
       (verina-advanced-29-all-counts-at-most-k-p
        (cdr counts)
        k))
    t))

(defun verina-advanced-29-filter-valid-frequency-lists
    (frequency-lists k)
  (declare (xargs :measure (acl2-count frequency-lists)))
  (if (consp frequency-lists)
      (if (verina-advanced-29-all-counts-at-most-k-p
           (car frequency-lists)
           k)
          (cons
           (car frequency-lists)
           (verina-advanced-29-filter-valid-frequency-lists
            (cdr frequency-lists)
            k))
        (verina-advanced-29-filter-valid-frequency-lists
         (cdr frequency-lists)
         k))
    nil))

(defun verina-advanced-29-contains-length-p
    (frequency-lists result)
  (declare (xargs :measure (acl2-count frequency-lists)))
  (if (consp frequency-lists)
      (or
       (equal (len (car frequency-lists)) result)
       (verina-advanced-29-contains-length-p
        (cdr frequency-lists)
        result))
    nil))

(defun verina-advanced-29-all-lengths-at-most-p
    (frequency-lists result)
  (declare (xargs :measure (acl2-count frequency-lists)))
  (if (consp frequency-lists)
      (and
       (<= (len (car frequency-lists)) result)
       (verina-advanced-29-all-lengths-at-most-p
        (cdr frequency-lists)
        result))
    t))

(defun verina-advanced-29-longest-good-subarray-postcond
    (nums k result)
  (let* ((subarrays
          (verina-advanced-29-all-subarrays nums))
         (subarray-frequencies
          (verina-advanced-29-map-subarray-frequencies
           subarrays))
         (valid-subarray-frequencies
          (verina-advanced-29-filter-valid-frequency-lists
           subarray-frequencies
           k)))
    (and
     (verina-advanced-29-nat-listp nums)
     (natp k)
     (natp result)
     (or
      (and
       (equal nums nil)
       (equal result 0))
      (and
       (not (equal nums nil))
       (verina-advanced-29-contains-length-p
        valid-subarray-frequencies
        result)
       (verina-advanced-29-all-lengths-at-most-p
        valid-subarray-frequencies
        result))))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves both source binder domains and k > 0, while its
;; conclusion applies the complete postcondition to the executable result.

(defun
    verina-advanced-29-longest-good-subarray-spec-satisfied-statement
    (nums k)
  (implies
   (and
    (verina-advanced-29-nat-listp nums)
    (natp k)
    (verina-advanced-29-longest-good-subarray-precond
     nums
     k))
   (verina-advanced-29-longest-good-subarray-postcond
    nums
    k
    (verina-advanced-29-longest-good-subarray
     nums
     k))))

(value-triple :itpeval-statement-checked)
:q
