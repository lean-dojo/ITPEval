;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2021_shearsort_ShearSort_sort_all_rowsqtvc: the
;; verification condition for sorting every matrix row in alternating
;; ascending and descending order while preserving each row's multiset.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Why3 integer matrices remain arbitrary objects observed through total
;; row, column, and entry operations.  This predicate recovers the source
;; matrix invariant and integer entry type without bounding dimensions or
;; values.

(defstub sar-rows (matrix) t)
(defstub sar-columns (matrix) t)
(defstub sar-elt (matrix row column) t)

(defun-sk sar-matrix-p (matrix)
  (forall
   (row column)
   (and
    (integerp (sar-rows matrix))
    (integerp (sar-columns matrix))
    (<= 0 (sar-rows matrix))
    (<= 0 (sar-columns matrix))
    (implies
     (and
      (integerp row)
      (integerp column))
     (integerp (sar-elt matrix row column))))))

;; MapPermut.permut is equality of every integer value's occurrence count on
;; a half-open interval.  The recursive count is exact for arbitrary finite
;; integer intervals and does not impose a bound on entries.

(defun sar-row-value-count (matrix row value lower upper)
  (declare (xargs :measure (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (if (equal (sar-elt matrix row lower) value) 1 0)
     (sar-row-value-count
      matrix row value (+ lower 1) upper))))

(defun-sk sar-row-permut-p
  (left left-row right right-row lower upper)
  (forall
   (value)
   (implies
    (integerp value)
    (equal
     (sar-row-value-count
      left left-row value lower upper)
     (sar-row-value-count
      right right-row value lower upper)))))

(defun-sk sar-all-row-permutations-p
  (current original row-upper column-upper)
  (forall
   (row)
   (implies
    (and
     (integerp row)
     (<= 0 row)
     (< row row-upper))
    (sar-row-permut-p
     current row original row 0 column-upper))))

;; Rows below ROW-UPPER are ordered in the ShearSort snake direction: even
;; rows ascend and odd rows descend.

(defun-sk sar-snake-prefix-order-p
  (matrix row-upper column-upper)
  (forall
   (row left-column right-column)
   (implies
    (and
     (integerp row)
     (integerp left-column)
     (integerp right-column)
     (<= 0 row)
     (< row row-upper)
     (<= 0 left-column)
     (<= left-column right-column)
     (< right-column column-upper))
    (if (equal (mod row 2) 0)
        (<=
         (sar-elt matrix row left-column)
         (sar-elt matrix row right-column))
      (<=
       (sar-elt matrix row right-column)
       (sar-elt matrix row left-column))))))

(defun-sk sar-row-unchanged-except-p
  (new old selected)
  (forall
   (row column)
   (implies
    (and
     (integerp row)
     (integerp column)
     (<= 0 row)
     (< row (sar-rows new))
     (<= 0 column)
     (< column (sar-columns new))
     (not (equal row selected)))
    (equal
     (sar-elt new row column)
     (sar-elt old row column)))))

(defun-sk sar-selected-row-snake-sorted-p
  (matrix selected)
  (forall
   (left-column right-column)
   (implies
    (and
     (integerp left-column)
     (integerp right-column)
     (<= 0 left-column)
     (<= left-column right-column)
     (< right-column (sar-columns matrix)))
    (if (equal (mod selected 2) 0)
        (<=
         (sar-elt matrix selected left-column)
         (sar-elt matrix selected right-column))
      (<=
       (sar-elt matrix selected right-column)
       (sar-elt matrix selected left-column))))))

(defun sar-same-dimensions-p (left right)
  (and
   (equal (sar-rows left) (sar-rows right))
   (equal (sar-columns left) (sar-columns right))))

(defun sar-final-contract-p (current original)
  (and
   (sar-all-row-permutations-p
    current original
    (sar-rows current)
    (sar-columns current))
   (sar-snake-prefix-order-p
    current
    (sar-rows current)
    (sar-columns current))))

;; Every post-state satisfying SORT_ROW's frame, ordering, and permutation
;; postconditions must establish the next loop invariant.

(defun sar-loop-step-post-p (after original tid)
  (and
   (sar-all-row-permutations-p
    after original
    (sar-rows after)
    (sar-columns after))
   (sar-snake-prefix-order-p
    after
    (+ tid 1)
    (sar-columns after))))

(defun-sk sar-all-row-sort-results-p
  (before original tid)
  (forall
   (after)
   (implies
    (and
     (sar-matrix-p after)
     (sar-same-dimensions-p after before))
    (implies
     (and
      (sar-row-unchanged-except-p after before tid)
      (sar-selected-row-snake-sorted-p after tid)
      (sar-row-permut-p
       after tid before tid 0 (sar-columns after)))
     (sar-loop-step-post-p after original tid)))))

(defun sar-loop-premise-p
  (current original tid o1)
  (and
   (integerp tid)
   (<= 0 tid)
   (<= tid o1)
   (sar-all-row-permutations-p
    current original
    (sar-rows current)
    (sar-columns current))
   (sar-snake-prefix-order-p
    current tid (sar-columns current))))

(defun-sk sar-all-loop-indices-p
  (current original o1)
  (forall
   (tid)
   (implies
    (sar-loop-premise-p current original tid o1)
    (and
     (not (equal 2 0))
     (<= 0 tid)
     (< tid (sar-rows current))
     (sar-all-row-sort-results-p
      current original tid)))))

(defun sar-loop-exit-p (current original o1)
  (implies
   (and
    (sar-all-row-permutations-p
     current original
     (sar-rows current)
     (sar-columns current))
    (sar-snake-prefix-order-p
     current
     (+ o1 1)
     (sar-columns current)))
   (sar-final-contract-p current original)))

(defun-sk sar-all-loop-matrices-p (original o1)
  (forall
   (current)
   (implies
    (and
     (sar-matrix-p current)
     (sar-same-dimensions-p current original))
    (and
     (sar-all-loop-indices-p current original o1)
     (sar-loop-exit-p current original o1)))))

(defun sar-initial-invariant-p (matrix)
  (and
   (sar-all-row-permutations-p
    matrix matrix
    (sar-rows matrix)
    (sar-columns matrix))
   (sar-snake-prefix-order-p
    matrix 0 (sar-columns matrix))))

(defun
    ntp4vc-pearl-verifythis-2021-shearsort-shearsort-sort-all-rowsqtvc-statement
    (matrix)
  (implies
   (sar-matrix-p matrix)
   (let ((o1 (- (sar-rows matrix) 1)))
     (and
      (implies
       (<= 0 (+ o1 1))
       (and
        (sar-initial-invariant-p matrix)
        (sar-all-loop-matrices-p matrix o1)))
      (implies
       (< (+ o1 1) 0)
       (sar-final-contract-p matrix matrix))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
