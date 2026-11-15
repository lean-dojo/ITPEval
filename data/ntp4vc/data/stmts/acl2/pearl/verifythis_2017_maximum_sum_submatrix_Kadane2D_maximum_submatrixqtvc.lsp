;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2017_maximum_sum_submatrix_Kadane2D_maximum_submatrixqtvc:
;; the generated verification condition for the nested-loop two-dimensional
;; Kadane maximum-sum submatrix algorithm. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source finite integer arrays are represented by proper ACL2 lists of
;; integers. Valid nonnegative indices select list entries; negative and
;; out-of-range indices return the inhabited default zero without aliasing
;; natural index zero.

(defun kadane2d-int-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (kadane2d-int-list-p (cdr xs)))
    (equal xs nil)))

(defun kadane2d-array-read (array index)
  (if (and
       (integerp index)
       (<= 0 index)
       (< index (len array)))
      (nth index array)
    0))

(defun kadane2d-array-set-nat (array index value)
  (declare (xargs :measure (acl2-count array)))
  (if (endp array)
      nil
    (if (zp index)
        (cons value (cdr array))
      (cons
       (car array)
       (kadane2d-array-set-nat
        (cdr array)
        (- index 1)
        value)))))

(defun kadane2d-array-set (array index value)
  (if (and
       (integerp index)
       (<= 0 index))
      (kadane2d-array-set-nat
       array index value)
    array))

;; A finite rectangular integer matrix is encoded as
;; (:MATRIX ROWS COLUMNS FLAT-ROW-MAJOR-ENTRIES).  This represents every
;; source matrix extensionally, including zero-row matrices with arbitrary
;; nonnegative column count.

(defun kadane2d-matrix-p (matrix)
  (and
   (true-listp matrix)
   (equal (len matrix) 4)
   (equal (car matrix) :matrix)
   (natp (cadr matrix))
   (natp (caddr matrix))
   (kadane2d-int-list-p (cadddr matrix))
   (equal
    (len (cadddr matrix))
    (* (cadr matrix)
       (caddr matrix)))))

(defun kadane2d-rows (matrix)
  (cadr matrix))

(defun kadane2d-columns (matrix)
  (caddr matrix))

(defun kadane2d-valid-index-p (matrix row column)
  (and
   (integerp row)
   (integerp column)
   (<= 0 row)
   (< row (kadane2d-rows matrix))
   (<= 0 column)
   (< column (kadane2d-columns matrix))))

(defun kadane2d-matrix-read (matrix row column)
  (if (kadane2d-valid-index-p matrix row column)
      (nth
       (+ (* row (kadane2d-columns matrix))
          column)
       (cadddr matrix))
    0))

;; These count-recursive definitions are exactly the source half-open integer
;; sums.  When HIGH <= LOW the count is zero; otherwise every index in
;; [LOW,HIGH) occurs once.

(defun kadane2d-array-sum-loop (array index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (kadane2d-array-read array index)
     (kadane2d-array-sum-loop
      array
      (+ index 1)
      (- remaining 1)))))

(defun kadane2d-array-sum (array low high)
  (kadane2d-array-sum-loop
   array
   low
   (nfix (- high low))))

(defun kadane2d-column-sum-loop
    (matrix column row remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (kadane2d-matrix-read matrix row column)
     (kadane2d-column-sum-loop
      matrix
      column
      (+ row 1)
      (- remaining 1)))))

(defun kadane2d-column-sum
    (matrix column row-low row-high)
  (kadane2d-column-sum-loop
   matrix
   column
   row-low
   (nfix (- row-high row-low))))

(defun kadane2d-matrix-sum-loop
    (matrix row-low row-high column remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (kadane2d-column-sum
      matrix column row-low row-high)
     (kadane2d-matrix-sum-loop
      matrix
      row-low
      row-high
      (+ column 1)
      (- remaining 1)))))

(defun kadane2d-matrix-sum
    (matrix row-low row-high column-low column-high)
  (kadane2d-matrix-sum-loop
   matrix
   row-low
   row-high
   column-low
   (nfix (- column-high column-low))))

;; Quantified array and matrix invariants used by the generated VC.

(defun-sk kadane2d-zero-array-p (array length)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index length))
      (equal
       (kadane2d-array-read array index)
       0)))))

(defun-sk kadane2d-fill-frame-p
    (old-array new-array filled-length)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (and
        (<= 0 index)
        (< index 0))
       (and
        (<= (+ 0 filled-length) index)
        (< index (len new-array))))
      (equal
       (kadane2d-array-read new-array index)
       (kadane2d-array-read old-array index))))))

(defun-sk kadane2d-array-split-p
    (matrix array row-low row-high split)
  (forall (column)
    (implies
     (integerp column)
     (and
      (implies
       (and
        (<= 0 column)
        (< column split))
       (equal
        (kadane2d-array-read array column)
        (kadane2d-column-sum
         matrix column row-low row-high)))
      (implies
       (and
        (<= split column)
        (< column (kadane2d-columns matrix)))
       (equal
        (kadane2d-array-read array column)
        (kadane2d-column-sum
         matrix column row-low (- row-high 1))))))))

(defun-sk kadane2d-before-row-bound-p
    (matrix row-limit maximum)
  (forall (row-low row-high column-low column-high)
    (implies
     (and
      (integerp row-low)
      (integerp row-high)
      (integerp column-low)
      (integerp column-high))
     (implies
      (and
       (<= 0 row-low)
       (< row-low row-limit))
      (implies
       (and
        (<= row-low row-high)
        (<= row-high (kadane2d-rows matrix)))
       (implies
        (and
         (<= 0 column-low)
         (<= column-low column-high)
         (<= column-high
             (kadane2d-columns matrix)))
        (<=
         (kadane2d-matrix-sum
          matrix
          row-low
          row-high
          column-low
          column-high)
         maximum)))))))

(defun-sk kadane2d-lexicographic-bound-p
    (matrix current-row row-high-limit maximum)
  (forall (row-low row-high column-low column-high)
    (implies
     (and
      (integerp row-low)
      (integerp row-high)
      (integerp column-low)
      (integerp column-high))
     (implies
      (and
       (<= 0 row-low)
       (<= row-low row-high)
       (<= row-high (kadane2d-rows matrix)))
      (implies
       (or
        (< row-low current-row)
        (and
         (equal row-low current-row)
         (< row-high row-high-limit)))
       (implies
        (and
         (<= 0 column-low)
         (<= column-low column-high)
         (<= column-high
             (kadane2d-columns matrix)))
        (<=
         (kadane2d-matrix-sum
          matrix
          row-low
          row-high
          column-low
          column-high)
         maximum)))))))

(defun-sk kadane2d-all-submatrices-bound-p
    (matrix maximum)
  (forall (row-low row-high column-low column-high)
    (implies
     (and
      (integerp row-low)
      (integerp row-high)
      (integerp column-low)
      (integerp column-high))
     (implies
      (and
       (<= 0 row-low)
       (<= row-low row-high)
       (<= row-high (kadane2d-rows matrix)))
      (implies
       (and
        (<= 0 column-low)
        (<= column-low column-high)
        (<= column-high
            (kadane2d-columns matrix)))
       (<=
        (kadane2d-matrix-sum
         matrix
         row-low
         row-high
         column-low
         column-high)
        maximum))))))

(defun kadane2d-rectangle-value-p
    (matrix row-low row-high column-low column-high value)
  (and
   (<= 0 row-low)
   (<= row-low row-high)
   (<= row-high (kadane2d-rows matrix))
   (<= 0 column-low)
   (<= column-low column-high)
   (<= column-high (kadane2d-columns matrix))
   (equal
    value
    (kadane2d-matrix-sum
     matrix
     row-low
     row-high
     column-low
     column-high))))

(defun kadane2d-selected-state-p
    (matrix row-low row-high column-low column-high value)
  (and
   (kadane2d-rectangle-value-p
    matrix
    row-low
    row-high
    column-low
    column-high
    value)
   (<=
    0
    (kadane2d-matrix-sum
     matrix
     row-low
     row-high
     column-low
     column-high))))

(defun kadane2d-final-correct-p
    (matrix row-low row-high column-low column-high value)
  (and
   (kadane2d-rectangle-value-p
    matrix
    row-low
    row-high
    column-low
    column-high
    value)
   (kadane2d-all-submatrices-bound-p
    matrix value)))

;; This is the extensional equality between the source post-update accessor
;; and Function.update. Negative queries remain outside the finite array, so
;; an update at natural index zero cannot affect them. The equality is retained
;; as an antecedent rather than discharged.

(defun-sk kadane2d-set-update-law-p
    (array index value)
  (forall (query)
    (implies
     (integerp query)
     (equal
      (kadane2d-array-read
       (kadane2d-array-set array index value)
       query)
      (if (equal query index)
          value
        (kadane2d-array-read array query))))))

;; The assumed maximum-subarray result and the subsequent conditional update
;; of the best rectangle.

(defun-sk kadane2d-array-maximum-p
    (array low high)
  (forall (other-low other-high)
    (implies
     (and
      (integerp other-low)
      (integerp other-high))
     (implies
      (and
       (<= 0 other-low)
       (<= other-low other-high)
       (<= other-high (len array)))
      (<=
       (kadane2d-array-sum
        array other-low other-high)
       (kadane2d-array-sum
        array low high))))))

(defun kadane2d-maximum-subarray-post-p
    (array low high)
  (and
   (<= 0 low)
   (<= low high)
   (<= high (len array))
   (kadane2d-array-maximum-p
    array low high)))

(defun kadane2d-maximum-update-p
    (matrix
     array
     row-low
     row-high
     saved-row-low
     saved-row-high
     saved-column-low
     saved-column-high
     saved-maximum
     low
     high)
  (if (<
       saved-maximum
       (kadane2d-array-sum array low high))
      (and
       (kadane2d-selected-state-p
        matrix
        row-low
        row-high
        low
        high
        (kadane2d-array-sum array low high))
       (kadane2d-lexicographic-bound-p
        matrix
        row-low
        (+ row-high 1)
        (kadane2d-array-sum array low high))
       (kadane2d-array-split-p
        matrix
        array
        row-low
        (- (+ row-high 1) 1)
        (kadane2d-columns matrix)))
    (and
     (kadane2d-selected-state-p
      matrix
      saved-row-low
      saved-row-high
      saved-column-low
      saved-column-high
      saved-maximum)
     (kadane2d-lexicographic-bound-p
      matrix
      row-low
      (+ row-high 1)
      saved-maximum)
     (kadane2d-array-split-p
      matrix
      array
      row-low
      (- (+ row-high 1) 1)
      (kadane2d-columns matrix)))))

(defun-sk kadane2d-all-maximum-subarrays-p
    (matrix
     array
     row-low
     row-high
     saved-row-low
     saved-row-high
     saved-column-low
     saved-column-high
     saved-maximum)
  (forall (low high)
    (implies
     (and
      (integerp low)
      (integerp high))
     (implies
      (kadane2d-maximum-subarray-post-p
       array low high)
      (kadane2d-maximum-update-p
       matrix
       array
       row-low
       row-high
       saved-row-low
       saved-row-high
       saved-column-low
       saved-column-high
       saved-maximum
       low
       high)))))

;; One column update and the generated accessor/length obligations.

(defun kadane2d-column-step-p
    (matrix array row-low row-high column)
  (let* ((matrix-row (- row-high 1))
         (updated-value
          (+
           (kadane2d-array-read array column)
           (kadane2d-matrix-read
            matrix matrix-row column)))
         (updated-array
          (kadane2d-array-set
           array column updated-value)))
    (and
     (kadane2d-valid-index-p
      matrix matrix-row column)
     (<= 0 column)
     (< column (len array))
     (<= 0 column)
     (< column (len array))
     (implies
      (equal
       (len updated-array)
       (len array))
      (implies
       (kadane2d-set-update-law-p
        array column updated-value)
       (kadane2d-array-split-p
        matrix
        updated-array
        row-low
        row-high
        (+ column 1)))))))

(defun-sk kadane2d-all-column-steps-p
    (matrix array row-low row-high column-upper)
  (forall (column)
    (implies
     (integerp column)
     (implies
      (and
       (<= 0 column)
       (<= column column-upper)
       (kadane2d-array-split-p
        matrix
        array
        row-low
        row-high
        column))
      (kadane2d-column-step-p
       matrix
       array
       row-low
       row-high
       column)))))

(defun kadane2d-column-run-p
    (matrix
     array
     row-low
     row-high
     column-upper
     saved-row-low
     saved-row-high
     saved-column-low
     saved-column-high
     saved-maximum)
  (and
   (kadane2d-all-column-steps-p
    matrix
    array
    row-low
    row-high
    column-upper)
   (implies
    (kadane2d-array-split-p
     matrix
     array
     row-low
     row-high
     (+ column-upper 1))
    (kadane2d-all-maximum-subarrays-p
     matrix
     array
     row-low
     row-high
     saved-row-low
     saved-row-high
     saved-column-low
     saved-column-high
     saved-maximum))))

(defun-sk kadane2d-all-column-arrays-p
    (matrix
     old-array
     row-low
     row-high
     column-upper
     saved-row-low
     saved-row-high
     saved-column-low
     saved-column-high
     saved-maximum)
  (forall (array)
    (implies
     (kadane2d-int-list-p array)
     (implies
      (equal
       (len array)
       (len old-array))
      (kadane2d-column-run-p
       matrix
       array
       row-low
       row-high
       column-upper
       saved-row-low
       saved-row-high
       saved-column-low
       saved-column-high
       saved-maximum)))))

;; Exit from the column loop, including its empty-range branch.

(defun kadane2d-column-loop-result-p
    (matrix
     array
     row-low
     row-high
     saved-row-low
     saved-row-high
     saved-column-low
     saved-column-high
     saved-maximum)
  (let ((column-upper
         (- (kadane2d-columns matrix) 1)))
    (and
     (implies
      (<= 0 (+ column-upper 1))
      (and
       (kadane2d-array-split-p
        matrix array row-low row-high 0)
       (kadane2d-all-column-arrays-p
        matrix
        array
        row-low
        row-high
        column-upper
        saved-row-low
        saved-row-high
        saved-column-low
        saved-column-high
        saved-maximum)))
     (implies
      (< (+ column-upper 1) 0)
      (kadane2d-all-maximum-subarrays-p
       matrix
       array
       row-low
       row-high
       saved-row-low
       saved-row-high
       saved-column-low
       saved-column-high
       saved-maximum)))))

;; The inner loop's completed state is a sibling of the quantified
;; per-row obligations in the generated VC.

(defun kadane2d-inner-finish-p
    (matrix
     array
     row-low
     inner-high
     saved-row-low
     saved-row-high
     saved-column-low
     saved-column-high
     saved-maximum)
  (implies
   (and
    (kadane2d-selected-state-p
     matrix
     saved-row-low
     saved-row-high
     saved-column-low
     saved-column-high
     saved-maximum)
    (kadane2d-lexicographic-bound-p
     matrix
     row-low
     (+ inner-high 1)
     saved-maximum)
    (kadane2d-array-split-p
     matrix
     array
     row-low
     (- (+ inner-high 1) 1)
     (kadane2d-columns matrix)))
   (and
    (kadane2d-selected-state-p
     matrix
     saved-row-low
     saved-row-high
     saved-column-low
     saved-column-high
     saved-maximum)
    (kadane2d-before-row-bound-p
     matrix
     (+ row-low 1)
     saved-maximum))))

;; The inner row-high loop packages its arbitrary state and array exactly as
;; in the VC.

(defun kadane2d-inner-iteration-p
    (matrix
     array
     row-low
     row-high
     inner-low
     inner-high
     saved-row-low
     saved-row-high
     saved-column-low
     saved-column-high
     saved-maximum)
  (implies
   (and
    (<= inner-low row-high)
    (<= row-high inner-high)
    (kadane2d-selected-state-p
     matrix
     saved-row-low
     saved-row-high
     saved-column-low
     saved-column-high
     saved-maximum)
    (kadane2d-lexicographic-bound-p
     matrix
     row-low
     row-high
     saved-maximum)
    (kadane2d-array-split-p
     matrix
     array
     row-low
     (- row-high 1)
     (kadane2d-columns matrix)))
   (kadane2d-column-loop-result-p
    matrix
    array
    row-low
    row-high
    saved-row-low
    saved-row-high
    saved-column-low
    saved-column-high
    saved-maximum)))

(defun-sk kadane2d-all-inner-rows-p
    (matrix
     array
     row-low
     inner-low
     inner-high
     saved-row-low
     saved-row-high
     saved-column-low
     saved-column-high
     saved-maximum)
  (forall (row-high)
    (implies
     (integerp row-high)
     (kadane2d-inner-iteration-p
      matrix
      array
      row-low
      row-high
      inner-low
      inner-high
      saved-row-low
      saved-row-high
      saved-column-low
      saved-column-high
      saved-maximum))))

(defun-sk kadane2d-all-inner-states-p
    (matrix
     old-array
     row-low
     inner-low
     inner-high)
  (forall
    (saved-column-high
     saved-column-low
     saved-row-high
     saved-row-low
     saved-maximum
     array)
    (implies
     (and
      (integerp saved-column-high)
      (integerp saved-column-low)
      (integerp saved-row-high)
      (integerp saved-row-low)
      (integerp saved-maximum)
      (kadane2d-int-list-p array))
     (implies
     (equal
       (len array)
       (len old-array))
      (and
       (kadane2d-all-inner-rows-p
        matrix
        array
        row-low
        inner-low
        inner-high
        saved-row-low
        saved-row-high
        saved-column-low
        saved-column-high
        saved-maximum)
       (kadane2d-inner-finish-p
        matrix
        array
        row-low
        inner-high
        saved-row-low
        saved-row-high
        saved-column-low
        saved-column-high
        saved-maximum))))))

(defun kadane2d-inner-loop-result-p
    (matrix
     array
     row-low
     old-row-low
     old-row-high
     old-column-low
     old-column-high
     old-maximum)
  (let* ((inner-high
          (kadane2d-rows matrix))
         (inner-low
          (+ row-low 1)))
    (and
     (implies
      (<= inner-low (+ inner-high 1))
      (and
       (kadane2d-selected-state-p
        matrix
        old-row-low
        old-row-high
        old-column-low
        old-column-high
        old-maximum)
       (kadane2d-lexicographic-bound-p
        matrix
        row-low
        inner-low
        old-maximum)
       (kadane2d-array-split-p
        matrix
        array
        row-low
        (- inner-low 1)
        (kadane2d-columns matrix))
       (kadane2d-all-inner-states-p
        matrix
        array
        row-low
        inner-low
        inner-high)))
     (implies
      (< (+ inner-high 1) inner-low)
      (and
       (kadane2d-selected-state-p
        matrix
        old-row-low
        old-row-high
        old-column-low
        old-column-high
        old-maximum)
       (kadane2d-before-row-bound-p
        matrix
        (+ row-low 1)
        old-maximum))))))

;; Array.fill and the outer row-low loop.

(defun-sk kadane2d-all-filled-arrays-p
    (matrix
     old-array
     filled-length
     row-low
     old-row-low
     old-row-high
     old-column-low
     old-column-high
     old-maximum)
  (forall (array)
    (implies
     (kadane2d-int-list-p array)
     (implies
      (equal
       (len array)
       (len old-array))
      (implies
       (and
        (kadane2d-fill-frame-p
         old-array array filled-length)
        (kadane2d-zero-array-p
         array (+ 0 filled-length)))
       (kadane2d-inner-loop-result-p
        matrix
        array
        row-low
        old-row-low
        old-row-high
        old-column-low
        old-column-high
        old-maximum))))))

(defun kadane2d-outer-iteration-p
    (matrix
     array
     row-low
     old-row-low
     old-row-high
     old-column-low
     old-column-high
     old-maximum)
  (let ((filled-length
         (kadane2d-columns matrix)))
    (and
     (<= 0 0)
     (<= 0 filled-length)
     (<= (+ 0 filled-length)
         (len array))
     (kadane2d-all-filled-arrays-p
      matrix
      array
      filled-length
      row-low
      old-row-low
      old-row-high
      old-column-low
      old-column-high
      old-maximum))))

(defun-sk kadane2d-all-outer-rows-p
    (matrix
     array
     outer-upper
     saved-row-low
     saved-row-high
     saved-column-low
     saved-column-high
     saved-maximum)
  (forall (row-low)
    (implies
     (integerp row-low)
     (implies
      (and
       (<= 0 row-low)
       (<= row-low outer-upper)
       (kadane2d-selected-state-p
        matrix
        saved-row-low
        saved-row-high
        saved-column-low
        saved-column-high
        saved-maximum)
       (kadane2d-before-row-bound-p
        matrix
        row-low
        saved-maximum))
      (kadane2d-outer-iteration-p
       matrix
       array
       row-low
       saved-row-low
       saved-row-high
       saved-column-low
       saved-column-high
       saved-maximum)))))

(defun-sk kadane2d-all-outer-states-p
    (matrix initial-array outer-upper)
  (forall
    (saved-column-high
     saved-column-low
     saved-row-high
     saved-row-low
     saved-maximum
     array)
    (implies
     (and
      (integerp saved-column-high)
      (integerp saved-column-low)
      (integerp saved-row-high)
      (integerp saved-row-low)
      (integerp saved-maximum)
      (kadane2d-int-list-p array))
     (implies
      (equal
       (len array)
       (len initial-array))
      (kadane2d-all-outer-rows-p
       matrix
       array
       outer-upper
       saved-row-low
       saved-row-high
       saved-column-low
       saved-column-high
       saved-maximum)))))

(defun kadane2d-after-initial-array-p
    (matrix initial-array)
  (let ((outer-upper
         (- (kadane2d-rows matrix) 1)))
    (and
     (implies
      (<= 0 (+ outer-upper 1))
      (and
       (kadane2d-selected-state-p
        matrix 0 0 0 0 0)
       (kadane2d-before-row-bound-p
        matrix 0 0)
       (kadane2d-all-outer-states-p
        matrix
        initial-array
        outer-upper)))
     (implies
      (< (+ outer-upper 1) 0)
      (kadane2d-final-correct-p
       matrix 0 0 0 0 0)))))

(defun-sk kadane2d-all-initial-arrays-p
    (matrix column-count)
  (forall (array)
    (implies
     (kadane2d-int-list-p array)
     (implies
      (and
       (kadane2d-zero-array-p
        array column-count)
       (equal
        (len array)
        column-count))
      (kadane2d-after-initial-array-p
       matrix array)))))

;; This is the complete unproved verification condition.  The matrix-domain
;; guard is exactly the source Matrix type and its nonnegative-dimension
;; invariant; all remaining binders retain their source integer or
;; integer-array domains.

(defun-sk
    ntp4vc-pearl-verifythis-2017-maximum-sum-submatrix-kadane2d-maximum-submatrixqtvc-statement
    ()
  (forall (matrix)
    (implies
     (kadane2d-matrix-p matrix)
     (let ((column-count
            (kadane2d-columns matrix)))
       (and
        (<= 0 column-count)
        (kadane2d-all-initial-arrays-p
         matrix column-count))))))

(value-triple :itpeval-statement-checked)
:q
