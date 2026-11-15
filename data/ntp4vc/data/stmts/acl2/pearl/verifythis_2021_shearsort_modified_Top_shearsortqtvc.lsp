;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2021_shearsort_modified_Top_shearsortqtvc: the
;; verification condition for alternating snake-ordered row sorts and
;; sorted column passes while preserving matrix multiplicities and
;; decreasing the inversion count. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Why3 integer matrices remain arbitrary objects observed through total
;; dimension and entry operations. The predicate supplies exactly the
;; nonnegative dimensions and integer entries of the source matrix type.

(defstub sm-rows (matrix) t)
(defstub sm-columns (matrix) t)
(defstub sm-elt (matrix row column) t)

(defun-sk sm-matrix-p (matrix)
  (forall
   (row column)
   (and
    (integerp (sm-rows matrix))
    (integerp (sm-columns matrix))
    (<= 0 (sm-rows matrix))
    (<= 0 (sm-columns matrix))
    (implies
     (and (integerp row) (integerp column))
     (integerp (sm-elt matrix row column))))))

(defun sm-same-dimensions-p (left right)
  (and
   (equal (sm-rows left) (sm-rows right))
   (equal (sm-columns left) (sm-columns right))))

;; Why3 ComputerDivision is truncation toward zero.

(defun sm-tdiv (numerator denominator)
  (if (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (let ((quotient (floor (abs numerator) (abs denominator))))
        (if (or
             (and (< numerator 0) (< 0 denominator))
             (and (< 0 numerator) (< denominator 0)))
            (- quotient)
          quotient))
    0))

(defun sm-tmod (numerator denominator)
  (if (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (- numerator
         (* denominator (sm-tdiv numerator denominator)))
    0))

(defun sm-snake-lt-p (i j k l)
  (or
   (< i k)
   (and
    (equal i k)
    (if (equal (sm-tmod i 2) 0)
        (< j l)
      (< l j)))))

;; Exact finite occurrence sums over the half-open matrix ranges.

(defun sm-row-occurrences
  (matrix value row column columns)
  (declare (xargs :measure (nfix (- columns column))))
  (if (or
       (not (integerp column))
       (not (integerp columns))
       (<= columns column))
      0
    (+
     (if (equal (sm-elt matrix row column) value) 1 0)
     (sm-row-occurrences
      matrix value row (+ column 1) columns))))

(defun sm-mocc-rows (matrix value row rows columns)
  (declare (xargs :measure (nfix (- rows row))))
  (if (or
       (not (integerp row))
       (not (integerp rows))
       (<= rows row))
      0
    (+
     (sm-row-occurrences matrix value row 0 columns)
     (sm-mocc-rows
      matrix value (+ row 1) rows columns))))

(defun sm-mocc (value matrix)
  (sm-mocc-rows
   matrix value 0 (sm-rows matrix) (sm-columns matrix)))

;; Exact four-index inversion sum from the Why3 definition.

(defun sm-inversion-l-count
  (matrix i j k l columns)
  (declare (xargs :measure (nfix (- columns l))))
  (if (or
       (not (integerp l))
       (not (integerp columns))
       (<= columns l))
      0
    (+
     (if (and
          (sm-snake-lt-p i j k l)
          (< (sm-elt matrix k l)
             (sm-elt matrix i j)))
         1
       0)
     (sm-inversion-l-count
      matrix i j k (+ l 1) columns))))

(defun sm-inversion-k-sum
  (matrix i j k rows columns)
  (declare (xargs :measure (nfix (- rows k))))
  (if (or
       (not (integerp k))
       (not (integerp rows))
       (<= rows k))
      0
    (+
     (sm-inversion-l-count matrix i j k 0 columns)
     (sm-inversion-k-sum
      matrix i j (+ k 1) rows columns))))

(defun sm-inversion-j-sum
  (matrix i j rows columns)
  (declare (xargs :measure (nfix (- columns j))))
  (if (or
       (not (integerp j))
       (not (integerp columns))
       (<= columns j))
      0
    (+
     (sm-inversion-k-sum matrix i j 0 rows columns)
     (sm-inversion-j-sum
      matrix i (+ j 1) rows columns))))

(defun sm-inversion-i-sum
  (matrix i rows columns)
  (declare (xargs :measure (nfix (- rows i))))
  (if (or
       (not (integerp i))
       (not (integerp rows))
       (<= rows i))
      0
    (+
     (sm-inversion-j-sum matrix i 0 rows columns)
     (sm-inversion-i-sum
      matrix (+ i 1) rows columns))))

(defun sm-inversions (matrix)
  (sm-inversion-i-sum
   matrix 0 (sm-rows matrix) (sm-columns matrix)))

;; Source ordering and multiplicity predicates.

(defun-sk sm-mocc-preserved-p (current original)
  (forall
   (value)
   (implies
    (integerp value)
    (equal
     (sm-mocc value current)
     (sm-mocc value original)))))

(defun-sk sm-sorted-row-p (matrix row ascending)
  (forall
   (j l)
   (and
    (<= 0 row)
    (< row (sm-rows matrix))
    (implies
     (and
      (integerp j)
      (integerp l)
      (<= 0 j)
      (<= j l)
      (< l (sm-columns matrix)))
     (if ascending
         (<= (sm-elt matrix row j)
             (sm-elt matrix row l))
       (<= (sm-elt matrix row l)
           (sm-elt matrix row j)))))))

(defun-sk sm-sorted-column-p (matrix column)
  (forall
   (i k)
   (and
    (<= 0 column)
    (< column (sm-columns matrix))
    (implies
     (and
      (integerp i)
      (integerp k)
      (<= 0 i)
      (<= i k)
      (< k (sm-rows matrix)))
     (<= (sm-elt matrix i column)
         (sm-elt matrix k column))))))

(defun-sk sm-rows-sorted-before-p (matrix upper)
  (forall
   (row)
   (implies
    (integerp row)
    (implies
     (and (<= 0 row) (< row upper))
     (sm-sorted-row-p
      matrix row
      (equal (sm-tmod row 2) 0))))))

(defun-sk sm-columns-sorted-before-p (matrix upper)
  (forall
   (column)
   (implies
    (integerp column)
    (implies
     (and (<= 0 column) (< column upper))
     (sm-sorted-column-p matrix column)))))

(defun-sk sm-snake-order-p (matrix)
  (forall
   (i j k l)
   (implies
    (and
     (integerp i)
     (integerp j)
     (integerp k)
     (integerp l)
     (<= 0 i)
     (< i (sm-rows matrix))
     (<= 0 j)
     (< j (sm-columns matrix))
     (<= 0 k)
     (< k (sm-rows matrix))
     (<= 0 l)
     (< l (sm-columns matrix))
     (sm-snake-lt-p i j k l))
    (<= (sm-elt matrix i j)
        (sm-elt matrix k l)))))

;; This is the auxiliary ordered assertion emitted after the loop. The
;; generated VC deliberately bounds all four indices by columns(m).

(defun-sk sm-square-order-p (matrix bound)
  (forall
   (i j k l)
   (implies
    (and
     (integerp i)
     (integerp j)
     (integerp k)
     (integerp l)
     (<= 0 i)
     (< i bound)
     (<= 0 j)
     (< j bound)
     (<= 0 k)
     (< k bound)
     (<= 0 l)
     (< l bound)
     (sm-snake-lt-p i j k l))
    (<= (sm-elt matrix i j)
        (sm-elt matrix k l)))))

;; Frame predicates from the sort_row and sort_column contracts.

(defun-sk sm-row-frame-p (after before selected-row)
  (forall
   (row column)
   (implies
    (and
     (integerp row)
     (integerp column)
     (<= 0 row)
     (< row (sm-rows after))
     (<= 0 column)
     (< column (sm-columns after))
     (not (equal row selected-row)))
    (equal
     (sm-elt after row column)
     (sm-elt before row column)))))

(defun-sk sm-column-frame-p (after before selected-column)
  (forall
   (row column)
   (implies
    (and
     (integerp row)
     (integerp column)
     (<= 0 row)
     (< row (sm-rows after))
     (<= 0 column)
     (< column (sm-columns after))
     (not (equal column selected-column)))
    (equal
     (sm-elt after row column)
     (sm-elt before row column)))))

(defun-sk sm-matrices-equal-on-range-p (left right)
  (forall
   (row column)
   (implies
    (and
     (integerp row)
     (integerp column)
     (<= 0 row)
     (< row (sm-rows left))
     (<= 0 column)
     (< column (sm-columns left)))
    (equal
     (sm-elt left row column)
     (sm-elt right row column)))))

(defun-sk sm-selected-column-unchanged-p
  (after before selected-column)
  (forall
   (row)
   (implies
    (and
     (integerp row)
     (<= 0 row)
     (< row (sm-rows after)))
    (equal
     (sm-elt after row selected-column)
     (sm-elt before row selected-column)))))

;; Column-pass continuations, ordered inside-out for ACL2 admission.

(defun sm-column-sort-post-p
  (after before selected-column nochange)
  (and
   (sm-column-frame-p after before selected-column)
   (sm-mocc-preserved-p after before)
   (implies
    nochange
    (sm-selected-column-unchanged-p
     after before selected-column))
   (sm-sorted-column-p after selected-column)
   (<= (sm-inversions after)
       (sm-inversions before))
   (implies
    (not nochange)
    (< (sm-inversions after)
       (sm-inversions before)))))

(defun sm-column-updated-state-p
  (original phase-start new-nochange after next-column)
  (and
   (implies
    new-nochange
    (sm-matrices-equal-on-range-p after phase-start))
   (sm-columns-sorted-before-p after next-column)
   (sm-mocc-preserved-p after original)
   (<= (sm-inversions after)
       (sm-inversions phase-start))
   (implies
    (not new-nochange)
    (< (sm-inversions after)
       (sm-inversions phase-start)))))

(defun-sk sm-all-column-return-flags-p
  (original phase-start old-nochange before after selected-column)
  (forall
   (returned-nochange)
   (implies
    (or
     (equal returned-nochange t)
     (equal returned-nochange nil))
    (implies
     (sm-column-sort-post-p
      after before selected-column returned-nochange)
     (sm-column-updated-state-p
      original
      phase-start
      (if (not returned-nochange) nil old-nochange)
      after
      (+ selected-column 1))))))

(defun-sk sm-all-column-sort-results-p
  (original phase-start old-nochange before selected-column)
  (forall
   (after)
   (implies
    (sm-matrix-p after)
    (implies
     (sm-same-dimensions-p after before)
     (sm-all-column-return-flags-p
      original
      phase-start
      old-nochange
      before
      after
      selected-column)))))

(defun sm-column-loop-state-p
  (original phase-start nochange current column last-column)
  (and
   (integerp column)
   (<= 0 column)
   (<= column last-column)
   (implies
    nochange
    (sm-matrices-equal-on-range-p current phase-start))
   (sm-columns-sorted-before-p current column)
   (sm-mocc-preserved-p current original)
   (<= (sm-inversions current)
       (sm-inversions phase-start))
   (implies
    (not nochange)
    (< (sm-inversions current)
       (sm-inversions phase-start)))))

(defun sm-column-index-obligation-p
  (original phase-start nochange current column)
  (and
   (<= 0 column)
   (< column (sm-columns current))
   (sm-all-column-sort-results-p
    original phase-start nochange current column)))

(defun-sk sm-all-column-indices-p
  (original phase-start nochange current last-column)
  (forall
   (column)
   (implies
    (integerp column)
    (implies
     (sm-column-loop-state-p
      original
      phase-start
      nochange
      current
      column
      last-column)
     (sm-column-index-obligation-p
      original
      phase-start
      nochange
      current
      column)))))

(defun sm-column-loop-exit-state-p
  (original phase-start nochange current upper)
  (and
   (implies
    nochange
    (sm-matrices-equal-on-range-p current phase-start))
   (sm-columns-sorted-before-p current upper)
   (sm-mocc-preserved-p current original)
   (<= (sm-inversions current)
       (sm-inversions phase-start))
   (implies
    (not nochange)
    (< (sm-inversions current)
       (sm-inversions phase-start)))))

(defun sm-column-loop-exit-result-p
  (original outer-baseline nochange current)
  (if nochange
      (and
       (sm-square-order-p current (sm-columns original))
       (sm-snake-order-p current)
       (sm-mocc-preserved-p current original))
    (and
     (<= 0 (sm-inversions outer-baseline))
     (< (sm-inversions current)
        (sm-inversions outer-baseline))
     (sm-mocc-preserved-p current original))))

(defun-sk sm-all-column-loop-states-p
  (original outer-baseline phase-start last-column)
  (forall
   (nochange current)
   (implies
    (and
     (or (equal nochange t) (equal nochange nil))
     (sm-matrix-p current))
    (implies
     (sm-same-dimensions-p current phase-start)
     (and
      (sm-all-column-indices-p
       original
       phase-start
       nochange
       current
       last-column)
      (implies
       (sm-column-loop-exit-state-p
        original
        phase-start
        nochange
        current
        (+ last-column 1))
       (sm-column-loop-exit-result-p
        original
        outer-baseline
        nochange
        current)))))))

(defun sm-column-phase-p
  (original outer-baseline phase-start)
  (let ((last-column (- (sm-columns original) 1)))
    (and
     (implies
      (<= 0 (+ last-column 1))
      (and
       (sm-columns-sorted-before-p phase-start 0)
       (sm-mocc-preserved-p phase-start original)
       (<= (sm-inversions phase-start)
           (sm-inversions phase-start))
       (sm-all-column-loop-states-p
        original
        outer-baseline
        phase-start
        last-column)))
     (implies
      (< (+ last-column 1) 0)
      (and
       (sm-square-order-p
        phase-start
        (sm-columns original))
       (sm-snake-order-p phase-start)
       (sm-mocc-preserved-p phase-start original))))))

;; Row-pass continuations.

(defun sm-row-sort-post-p
  (after before selected-row)
  (and
   (sm-row-frame-p after before selected-row)
   (sm-mocc-preserved-p after before)
   (sm-sorted-row-p
    after
    selected-row
    (equal (sm-tmod selected-row 2) 0))
   (<= (sm-inversions after)
       (sm-inversions before))))

(defun sm-row-updated-state-p
  (original row-baseline after next-row)
  (and
   (sm-rows-sorted-before-p after next-row)
   (sm-mocc-preserved-p after original)
   (<= (sm-inversions after)
       (sm-inversions row-baseline))))

(defun-sk sm-all-row-sort-results-p
  (original row-baseline before selected-row)
  (forall
   (after)
   (implies
    (sm-matrix-p after)
    (implies
     (sm-same-dimensions-p after before)
     (implies
      (sm-row-sort-post-p after before selected-row)
      (sm-row-updated-state-p
       original
       row-baseline
       after
       (+ selected-row 1)))))))

(defun sm-row-loop-state-p
  (original row-baseline current row last-row)
  (and
   (integerp row)
   (<= 0 row)
   (<= row last-row)
   (sm-rows-sorted-before-p current row)
   (sm-mocc-preserved-p current original)
   (<= (sm-inversions current)
       (sm-inversions row-baseline))))

(defun sm-row-index-obligation-p
  (original row-baseline current row)
  (and
   (not (equal 2 0))
   (<= 0 row)
   (< row (sm-rows current))
   (sm-all-row-sort-results-p
    original row-baseline current row)))

(defun-sk sm-all-row-indices-p
  (original row-baseline current last-row)
  (forall
   (row)
   (implies
    (integerp row)
    (implies
     (sm-row-loop-state-p
      original row-baseline current row last-row)
     (sm-row-index-obligation-p
      original row-baseline current row)))))

(defun sm-row-loop-exit-state-p
  (original row-baseline current upper)
  (and
   (sm-rows-sorted-before-p current upper)
   (sm-mocc-preserved-p current original)
   (<= (sm-inversions current)
       (sm-inversions row-baseline))))

(defun-sk sm-all-row-loop-states-p
  (original row-baseline last-row)
  (forall
   (current)
   (implies
    (sm-matrix-p current)
    (implies
     (sm-same-dimensions-p current row-baseline)
     (and
      (sm-all-row-indices-p
       original row-baseline current last-row)
      (implies
       (sm-row-loop-exit-state-p
        original
        row-baseline
        current
        (+ last-row 1))
       (sm-column-phase-p
        original row-baseline current)))))))

(defun sm-shearsort-vc-p (original row-baseline)
  (let ((last-row (- (sm-columns original) 1)))
    (and
     (implies
      (<= 0 (+ last-row 1))
      (and
       (sm-rows-sorted-before-p row-baseline 0)
       (sm-mocc-preserved-p row-baseline original)
       (<= (sm-inversions row-baseline)
           (sm-inversions row-baseline))
       (sm-all-row-loop-states-p
        original row-baseline last-row)))
     (implies
      (< (+ last-row 1) 0)
      (sm-column-phase-p
       original row-baseline row-baseline)))))

(defun-sk
    ntp4vc-verifythis-2021-shearsort-modified-shearsort-statement ()
  (forall
   (original row-baseline)
   (implies
    (and
     (sm-matrix-p original)
     (sm-matrix-p row-baseline))
    (implies
     (and
      (equal (sm-rows original)
             (sm-columns original))
      (equal (sm-rows row-baseline)
             (sm-rows original))
      (equal (sm-columns row-baseline)
             (sm-columns original))
      (sm-mocc-preserved-p row-baseline original))
     (sm-shearsort-vc-p original row-baseline)))))

(value-triple :itpeval-statement-checked)

:q
