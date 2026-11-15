;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2021_shearsort_ShearSort_sort_columnqtvc: the
;; verification condition for copying one matrix column into an array,
;; sorting it, and writing it back while preserving all other columns.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Why3 integer matrices remain arbitrary objects observed through total
;; dimension and entry operations.  This predicate supplies the source
;; matrix invariant and integer element type without bounding dimensions or
;; entries.

(defstub sc-rows (matrix) t)
(defstub sc-columns (matrix) t)
(defstub sc-elt (matrix row column) t)

(defun-sk sc-matrix-p (matrix)
  (forall
   (row column)
   (and
    (integerp (sc-rows matrix))
    (integerp (sc-columns matrix))
    (<= 0 (sc-rows matrix))
    (<= 0 (sc-columns matrix))
    (implies
     (and (integerp row) (integerp column))
     (integerp (sc-elt matrix row column))))))

(defun sc-same-dimensions-p (left right)
  (and
   (equal (sc-rows left) (sc-rows right))
   (equal (sc-columns left) (sc-columns right))))

(defun sc-valid-index-p (matrix row column)
  (and
   (integerp row)
   (integerp column)
   (<= 0 row)
   (< row (sc-rows matrix))
   (<= 0 column)
   (< column (sc-columns matrix))))

;; ACL2 finite true lists of integers represent Why3 arrays and the exported
;; integer lists.  Int.toNat maps negative integers to zero, and source list
;; indexing returns the inhabited integer default zero outside the list.

(defun sc-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (sc-integer-list-p (cdr xs)))
    (equal xs nil)))

(defun sc-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun sc-nth-int (index xs)
  (let ((natural-index (sc-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      0)))

;; Unlike ACL2's update-nth, List.set leaves an out-of-range list unchanged.

(defun sc-list-set-natural (xs index value)
  (declare (xargs :measure (nfix index)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (sc-list-set-natural
        (cdr xs) (- index 1) value)))))

(defun sc-list-set-int (xs index value)
  (sc-list-set-natural xs (sc-int-to-nat index) value))

;; MapPermut.permut is equality of all integer-value occurrence counts on a
;; half-open integer interval.

(defun sc-list-value-count (xs value lower upper)
  (declare (xargs :measure (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (if (equal (sc-nth-int lower xs) value) 1 0)
     (sc-list-value-count xs value (+ lower 1) upper))))

(defun sc-column-value-count (matrix column value lower upper)
  (declare (xargs :measure (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (if (equal (sc-elt matrix lower column) value) 1 0)
     (sc-column-value-count
      matrix column value (+ lower 1) upper))))

(defun-sk sc-list-permut-p (left right lower upper)
  (forall
   (value)
   (implies
    (integerp value)
    (equal
     (sc-list-value-count left value lower upper)
     (sc-list-value-count right value lower upper)))))

(defun-sk sc-column-permut-p
  (left right column lower upper)
  (forall
   (value)
   (implies
    (integerp value)
    (equal
     (sc-column-value-count left column value lower upper)
     (sc-column-value-count right column value lower upper)))))

;; Extensional predicates represent the source equalities between total
;; integer-indexed functions.

(defun-sk sc-list-set-update-law-p (xs index value)
  (forall
   (argument)
   (implies
    (integerp argument)
    (equal
     (sc-nth-int
      argument
      (sc-list-set-int xs index value))
     (if (equal argument index)
         value
       (sc-nth-int argument xs))))))

(defun-sk sc-matrix-single-update-p
  (new old selected-row selected-column value)
  (forall
   (row column)
   (implies
    (and (integerp row) (integerp column))
    (equal
     (sc-elt new row column)
     (if (equal row selected-row)
         (if (equal column selected-column)
             value
           (sc-elt old selected-row column))
       (sc-elt old row column))))))

;; Array and matrix predicates used directly by the generated verification
;; condition.

(defun-sk sc-zero-array-p (array length)
  (forall
   (index)
   (and
    (equal (len array) length)
    (implies
     (integerp index)
     (implies
      (and (<= 0 index) (< index length))
      (equal (sc-nth-int index array) 0))))))

(defun-sk sc-column-prefix-p (array matrix column upper)
  (forall
   (index)
   (implies
    (integerp index)
    (implies
     (and (<= 0 index) (< index upper))
     (equal
      (sc-nth-int index array)
      (sc-elt matrix index column))))))

(defun-sk sc-list-sorted-p (array)
  (forall
   (left right)
   (implies
    (and (integerp left) (integerp right))
    (implies
     (and
      (<= 0 left)
      (<= left right)
      (< right (len array)))
     (<=
      (sc-nth-int left array)
      (sc-nth-int right array))))))

(defun-sk sc-unchanged-except-column-p
  (current original selected-column)
  (forall
   (row column)
   (implies
    (and
     (integerp row)
     (integerp column)
     (<= 0 row)
     (< row (sc-rows current))
     (<= 0 column)
     (< column (sc-columns current))
     (not (equal column selected-column)))
    (equal
     (sc-elt current row column)
     (sc-elt original row column)))))

(defun-sk sc-column-sorted-p (matrix selected-column)
  (forall
   (left right)
   (implies
    (and (integerp left) (integerp right))
    (implies
     (and
      (<= 0 left)
      (<= left right)
      (< right (sc-rows matrix)))
     (<=
      (sc-elt matrix left selected-column)
      (sc-elt matrix right selected-column))))))

(defun sc-final-contract-p
  (current original selected-column)
  (and
   (sc-unchanged-except-column-p
    current original selected-column)
   (sc-column-sorted-p current selected-column)
   (sc-column-permut-p
    current original selected-column 0 (sc-rows current))))

(defun sc-original-negative-contract-p
  (matrix selected-column)
  (and
   (sc-column-sorted-p matrix selected-column)
   (sc-column-permut-p
    matrix matrix selected-column 0 (sc-rows matrix))))

;; Write-back loop: every matrix state and every loop index retain the exact
;; loop invariant and update obligations from the source VC.

(defun-sk sc-all-single-update-results-p
  (array original current selected-column index value)
  (forall
   (next)
   (implies
    (sc-matrix-p next)
    (implies
     (sc-same-dimensions-p next current)
     (implies
      (sc-matrix-single-update-p
       next current index selected-column value)
      (and
       (sc-column-prefix-p
        array next selected-column (+ index 1))
       (sc-unchanged-except-column-p
        next original selected-column)))))))

(defun sc-write-index-result-p
  (array original current selected-column index)
  (and
   (<= 0 index)
   (< index (len array))
   (sc-valid-index-p current index selected-column)
   (sc-all-single-update-results-p
    array
    original
    current
    selected-column
    index
    (sc-nth-int index array))))

(defun-sk sc-all-write-indices-p
  (array original current selected-column upper)
  (forall
   (index)
   (implies
    (integerp index)
    (implies
     (and
      (<= 0 index)
      (<= index upper)
      (sc-column-prefix-p
       array current selected-column index)
      (sc-unchanged-except-column-p
       current original selected-column))
     (sc-write-index-result-p
      array original current selected-column index)))))

(defun sc-write-exit-p
  (array original current selected-column upper)
  (implies
   (and
    (sc-column-prefix-p
     array current selected-column (+ upper 1))
    (sc-unchanged-except-column-p
     current original selected-column))
   (sc-final-contract-p
    current original selected-column)))

(defun-sk sc-all-write-loop-matrices-p
  (array original selected-column upper)
  (forall
   (current)
   (implies
    (sc-matrix-p current)
    (implies
     (sc-same-dimensions-p current original)
     (and
      (sc-all-write-indices-p
       array original current selected-column upper)
      (sc-write-exit-p
       array original current selected-column upper))))))

(defun sc-write-back-vc-p
  (array original selected-column)
  (let ((upper (- (sc-rows original) 1)))
    (and
     (implies
      (<= 0 (+ upper 1))
      (and
       (sc-column-prefix-p
        array original selected-column 0)
       (sc-all-write-loop-matrices-p
        array original selected-column upper)))
     (implies
      (< (+ upper 1) 0)
      (sc-original-negative-contract-p
       original selected-column)))))

;; Sorting is specified by universal post-state quantification, matching the
;; source call to the abstract array-sort procedure.

(defun-sk sc-all-sorted-results-p
  (before original selected-column)
  (forall
   (after)
   (implies
    (sc-integer-list-p after)
    (implies
     (equal (len after) (len before))
     (implies
      (and
       (sc-list-sorted-p after)
       (sc-list-permut-p
        after before 0 (len after)))
      (sc-write-back-vc-p
       after original selected-column))))))

;; Copy loop: List.set's length and extensional update properties remain
;; explicit antecedents, exactly as in the generated VC.

(defun sc-copy-index-result-p
  (array matrix selected-column index)
  (let ((value (sc-elt matrix index selected-column)))
    (and
     (sc-valid-index-p matrix index selected-column)
     (<= 0 index)
     (< index (len array))
     (implies
      (equal
       (len (sc-list-set-int array index value))
       (len array))
      (implies
       (sc-list-set-update-law-p array index value)
       (sc-column-prefix-p
        (sc-list-set-int array index value)
        matrix
        selected-column
        (+ index 1)))))))

(defun-sk sc-all-copy-indices-p
  (array matrix selected-column upper)
  (forall
   (index)
   (implies
    (integerp index)
    (implies
     (and
      (<= 0 index)
      (<= index upper)
      (sc-column-prefix-p
       array matrix selected-column index))
     (sc-copy-index-result-p
      array matrix selected-column index)))))

(defun sc-copy-exit-p
  (array matrix selected-column upper)
  (implies
   (sc-column-prefix-p
    array matrix selected-column (+ upper 1))
   (sc-all-sorted-results-p
    array matrix selected-column)))

(defun-sk sc-all-copy-loop-arrays-p
  (initial matrix selected-column upper)
  (forall
   (current)
   (implies
    (sc-integer-list-p current)
    (implies
     (equal (len current) (len initial))
     (and
      (sc-all-copy-indices-p
       current matrix selected-column upper)
      (sc-copy-exit-p
       current matrix selected-column upper))))))

(defun-sk sc-all-negative-copy-results-p
  (initial matrix selected-column)
  (forall
   (current)
   (implies
    (sc-integer-list-p current)
    (implies
     (equal (len current) (len initial))
     (implies
      (and
       (sc-list-sorted-p current)
       (sc-list-permut-p
        current initial 0 (len current)))
      (sc-write-back-vc-p
       current matrix selected-column))))))

(defun sc-copy-and-sort-vc-p
  (initial matrix selected-column)
  (let ((upper (- (sc-rows matrix) 1)))
    (and
     (implies
      (<= 0 (+ upper 1))
      (and
       (sc-column-prefix-p
        initial matrix selected-column 0)
       (sc-all-copy-loop-arrays-p
        initial matrix selected-column upper)))
     (implies
      (< (+ upper 1) 0)
      (sc-all-negative-copy-results-p
       initial matrix selected-column)))))

(defun-sk sc-all-initial-arrays-p
  (matrix selected-column rows)
  (forall
   (initial)
   (implies
    (sc-integer-list-p initial)
    (implies
     (sc-zero-array-p initial rows)
     (sc-copy-and-sort-vc-p
      initial matrix selected-column)))))

;; The complete unproved verification condition.

(defun
    ntp4vc-pearl-verifythis-2021-shearsort-shearsort-sort-columnqtvc-statement
    (selected-column matrix)
  (implies
   (and
    (integerp selected-column)
    (sc-matrix-p matrix)
    (<= 0 selected-column)
    (< selected-column (sc-columns matrix)))
   (let ((rows (sc-rows matrix)))
     (and
      (<= 0 rows)
      (sc-all-initial-arrays-p
       matrix selected-column rows)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
