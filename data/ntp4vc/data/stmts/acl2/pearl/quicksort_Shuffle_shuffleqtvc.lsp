;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/quicksort_Shuffle_shuffleqtvc: the shuffle-loop verification
;; condition preserving permutation through every admissible array swap.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite true lists of integers represent the source
;; integers and finite integer arrays without restricting either domain.

(defun shuffle-vc-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (shuffle-vc-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Removing one matching occurrence at each step gives exact finite-list
;; multiset equality, including multiplicities, and hence List.Perm.

(defun shuffle-vc-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (shuffle-vc-remove-first value (cdr xs))))))

(defun shuffle-vc-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (shuffle-vc-permutation-p
      (cdr left)
      (shuffle-vc-remove-first (car left) right)))))

;; Int.toNat maps negative integers to zero. Integer list indexing is total,
;; with the source's inhabited integer default zero outside the list.

(defun shuffle-vc-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun shuffle-vc-nth-int (index xs)
  (let ((natural-index
         (shuffle-vc-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      0)))

;; This total update is List.set: an in-bounds entry is replaced and an
;; out-of-bounds update leaves the finite list unchanged.

(defun shuffle-vc-list-set (xs index value)
  (declare (xargs :measure (nfix index)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (shuffle-vc-list-set
        (cdr xs)
        (- index 1)
        value)))))

;; This is the exact forward array swap from OLD to NEW.  Both replacement
;; values are read from OLD, so equal indices leave the array unchanged.

(defun shuffle-vc-array-exchange-p
    (old new first second)
  (equal
   new
   (shuffle-vc-list-set
    (shuffle-vc-list-set
     old
     (shuffle-vc-int-to-nat first)
     (shuffle-vc-nth-int second old))
    (shuffle-vc-int-to-nat second)
    (shuffle-vc-nth-int first old))))

;; Preserve the innermost universal continuation over every same-length
;; integer array related to the current array by the selected exchange.

(defun-sk shuffle-vc-all-exchange-results-p
    (original current index random-index)
  (forall (next)
    (implies
     (shuffle-vc-integer-list-p next)
     (implies
      (equal (len next) (len current))
      (implies
       (shuffle-vc-array-exchange-p
        current next index random-index)
       (shuffle-vc-permutation-p
        original next))))))

;; This is the universally quantified random-index obligation for one loop
;; index. The bounds and exchange continuation are conjoined exactly as in
;; the generated verification condition.

(defun-sk shuffle-vc-all-random-indices-p
    (original current index upper-random-bound)
  (forall (random-index)
    (implies
     (integerp random-index)
     (implies
      (and
       (<= 0 random-index)
       (< random-index upper-random-bound))
      (and
       (and
        (<= 0 index)
        (< index (len current)))
       (and
        (<= 0 random-index)
        (< random-index (len current)))
       (shuffle-vc-all-exchange-results-p
        original current index random-index))))))

(defun shuffle-vc-loop-index-result-p
    (original current index)
  (let ((upper-random-bound (+ index 1)))
    (and
     (< 0 upper-random-bound)
     (shuffle-vc-all-random-indices-p
      original current index upper-random-bound))))

;; Preserve the universal integer loop index and its full invariant
;; antecedent: 1 <= index <= final-index and current permutes original.

(defun-sk shuffle-vc-all-loop-indices-p
    (original current final-index)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (and
        (<= 1 index)
        (<= index final-index))
       (shuffle-vc-permutation-p
        original current))
      (shuffle-vc-loop-index-result-p
       original current index)))))

;; Preserve the universal same-length integer-array state binder surrounding
;; the loop-index obligation.

(defun-sk shuffle-vc-all-array-states-p
    (original final-index)
  (forall (current)
    (implies
     (shuffle-vc-integer-list-p current)
     (implies
      (equal (len current) (len original))
      (shuffle-vc-all-loop-indices-p
       original current final-index)))))

;; This predicate is the complete unproved verification condition.

(defun
    ntp4vc-pearl-quicksort-shuffle-shuffleqtvc-statement
    (array)
  (implies
   (shuffle-vc-integer-list-p array)
   (let ((final-index (- (len array) 1)))
     (and
      (implies
       (<= 1 (+ final-index 1))
       (and
        (shuffle-vc-permutation-p array array)
        (shuffle-vc-all-array-states-p
         array final-index)))
      (implies
       (< (+ final-index 1) 1)
       (shuffle-vc-permutation-p array array))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
