;; Statement-only formalization of VERINA corpus artifact verina_advanced_57,
;; "nextGreaterElement": a monotonic-stack computation returns, for each
;; requested distinct integer, its first greater value to the right in the
;; containing distinct integer list, or -1. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-57-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-57-integer-listp (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-57-no-duplicates-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (not (member-equal (car xs) (cdr xs)))
       (verina-advanced-57-no-duplicates-p (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-57-all-members-p (xs ys)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (member-equal (car xs) ys)
       (verina-advanced-57-all-members-p (cdr xs) ys))
    (equal xs nil)))

(defun verina-advanced-57-next-greater-element-precond
    (nums1 nums2)
  (and
   (verina-advanced-57-no-duplicates-p nums1)
   (verina-advanced-57-no-duplicates-p nums2)
   (verina-advanced-57-all-members-p nums1 nums2)))

;; List.get! on List Int returns the default integer 0 outside the list.

(defun verina-advanced-57-nth-default-zero (index xs)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp xs)
        (if (zp index)
            (car xs)
          (verina-advanced-57-nth-default-zero
           (- index 1)
           (cdr xs)))
      0)))

;; A map entry (Int x Int) is represented by a cons pair. This is the source
;; stack.foldl finalization, including its accumulator order.

(defun verina-advanced-57-finalize-stack
    (stack map nums2)
  (declare (xargs :measure (acl2-count stack)))
  (if (consp stack)
      (verina-advanced-57-finalize-stack
       (cdr stack)
       (cons
        (cons
         (verina-advanced-57-nth-default-zero
          (car stack)
          nums2)
         -1)
        map)
       nums2)
    map))

;; The return value is the pair (newStack, newMap), represented by a cons whose
;; car is the stack and whose cdr is the association-list map.

(defun verina-advanced-57-process-stack
    (stack map current-value nums2)
  (declare (xargs :measure (acl2-count stack)))
  (if (consp stack)
      (let* ((top-index (car stack))
             (top-value
              (verina-advanced-57-nth-default-zero
               top-index
               nums2)))
        (if (> current-value top-value)
            (verina-advanced-57-process-stack
             (cdr stack)
             (cons
              (cons top-value current-value)
              map)
             current-value
             nums2)
          (cons stack map)))
    (cons nil map)))

;; REMAINING is nums2.length - INDEX. This reparameterizes the source guard
;; INDEX >= nums2.length without changing any reachable computation.

(defun verina-advanced-57-map-loop
    (index remaining stack map nums2)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (verina-advanced-57-finalize-stack
       stack
       map
       nums2)
    (let* ((current-value
            (verina-advanced-57-nth-default-zero
             index
             nums2))
           (processed
            (verina-advanced-57-process-stack
             stack
             map
             current-value
             nums2))
           (new-stack (car processed))
           (new-map (cdr processed)))
      (verina-advanced-57-map-loop
       (+ index 1)
       (- remaining 1)
       (cons index new-stack)
       new-map
       nums2))))

(defun verina-advanced-57-build-next-greater-map (nums2)
  (verina-advanced-57-map-loop
   0
   (len nums2)
   nil
   nil
   nums2))

(defun verina-advanced-57-find-in-map (value map)
  (declare (xargs :measure (acl2-count map)))
  (if (consp map)
      (if (equal (car (car map)) value)
          (cdr (car map))
        (verina-advanced-57-find-in-map
         value
         (cdr map)))
    -1))

;; Traversing NUMS1 directly is equivalent to the source index loop on a
;; proper list. The accumulator and final reverse are preserved exactly.

(defun verina-advanced-57-result-loop
    (remaining map result)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-57-result-loop
       (cdr remaining)
       map
       (cons
        (verina-advanced-57-find-in-map
         (car remaining)
         map)
        result))
    (reverse result)))

(defun verina-advanced-57-next-greater-element
    (nums1 nums2)
  (verina-advanced-57-result-loop
   nums1
   (verina-advanced-57-build-next-greater-map nums2)
   nil))

;; These option-valued searches reproduce findIdx? and find?. NIL is none;
;; (T . value) is some value, so index or offset zero remains distinguishable.

(defun verina-advanced-57-find-index-option
    (value index xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (equal (car xs) value)
          (cons t index)
        (verina-advanced-57-find-index-option
         value
         (+ index 1)
         (cdr xs)))
    nil))

(defun verina-advanced-57-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      xs
    (if (consp xs)
        (verina-advanced-57-drop
         (- count 1)
         (cdr xs))
      nil)))

(defun verina-advanced-57-find-greater-offset-option
    (value offset xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (> (car xs) value)
          (cons t offset)
        (verina-advanced-57-find-greater-offset-option
         value
         (+ offset 1)
         (cdr xs)))
    nil))

;; This is List.range nums1.length followed by List.all in the source
;; postcondition. For each index it separately performs the source findIdx?
;; and the bounded first-greater search to its right.

(defun verina-advanced-57-all-indices-correct-p
    (index remaining nums1 nums2 result)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let* ((value
            (verina-advanced-57-nth-default-zero
             index
             nums1))
           (result-value
            (verina-advanced-57-nth-default-zero
             index
             result))
           (location
            (verina-advanced-57-find-index-option
             value
             0
             nums2)))
      (and
       (consp location)
       (let* ((found-index (cdr location))
              (right-suffix
               (cdr
                (verina-advanced-57-drop
                 found-index
                 nums2)))
              (next-greater
               (verina-advanced-57-find-greater-offset-option
                value
                0
                right-suffix)))
         (if (consp next-greater)
             (equal
              result-value
              (verina-advanced-57-nth-default-zero
               (+ found-index
                  (cdr next-greater)
                  1)
               nums2))
           (equal result-value -1)))
       (verina-advanced-57-all-indices-correct-p
        (+ index 1)
        (- remaining 1)
        nums1
        nums2
        result)))))

(defun verina-advanced-57-result-values-valid-p
    (result nums2)
  (declare (xargs :measure (acl2-count result)))
  (if (consp result)
      (and
       (or
        (equal (car result) -1)
        (member-equal (car result) nums2))
       (verina-advanced-57-result-values-valid-p
        (cdr result)
        nums2))
    (equal result nil)))

(defun verina-advanced-57-next-greater-element-postcond
    (nums1 nums2 result)
  (and
   (verina-advanced-57-integer-listp nums1)
   (verina-advanced-57-integer-listp nums2)
   (verina-advanced-57-integer-listp result)
   (equal (len result) (len nums1))
   (verina-advanced-57-all-indices-correct-p
    0
    (len nums1)
    nums1
    nums2
    result)
   (verina-advanced-57-result-values-valid-p
    result
    nums2)))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves both List Int binders and the complete precondition;
;; its conclusion applies the complete postcondition to the exact executable
;; monotonic-stack result.

(defun
    verina-advanced-57-next-greater-element-spec-satisfied-statement
    (nums1 nums2)
  (implies
   (and
    (verina-advanced-57-integer-listp nums1)
    (verina-advanced-57-integer-listp nums2)
    (verina-advanced-57-next-greater-element-precond
     nums1
     nums2))
   (verina-advanced-57-next-greater-element-postcond
    nums1
    nums2
    (verina-advanced-57-next-greater-element
     nums1
     nums2))))

(value-triple :itpeval-statement-checked)
:q
