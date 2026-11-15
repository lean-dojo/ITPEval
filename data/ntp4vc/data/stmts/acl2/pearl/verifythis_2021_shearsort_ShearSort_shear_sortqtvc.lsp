;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2021_shearsort_ShearSort_shear_sortqtvc: the ShearSort
;; verification condition for alternating row sorts, threshold propagation,
;; column sorts, and preservation of the matrix multiset. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Why3 matrices and function values are represented by arbitrary ACL2
;; objects with total application operations.  The predicates below recover
;; exactly the source types; no finite carrier is imposed.

(defstub ss-rows (matrix) t)
(defstub ss-columns (matrix) t)
(defstub ss-elt (matrix row column) t)
(defstub ss-apply (function argument) t)
(defstub ss-first (function argument) t)
(defstub ss-second (function argument) t)

(defun-sk ss-matrix-p (matrix)
  (forall
   (row column)
   (and
    (integerp (ss-rows matrix))
    (integerp (ss-columns matrix))
    (<= 0 (ss-rows matrix))
    (<= 0 (ss-columns matrix))
    (implies
     (and (integerp row) (integerp column))
     (integerp (ss-elt matrix row column))))))

(defun-sk ss-int-function-p (function)
  (forall
   (argument)
   (implies
    (integerp argument)
    (integerp (ss-apply function argument)))))

(defun-sk ss-pair-function-p (function)
  (forall
   (argument)
   (implies
    (integerp argument)
    (and
     (integerp (ss-first function argument))
     (integerp (ss-second function argument))))))

;; Why3 ComputerDivision is truncation toward zero.  Int.toNat maps negative
;; exponents to zero in the exported integer-power expression.

(defun ss-tdiv (numerator denominator)
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

(defun ss-tmod (numerator denominator)
  (if (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (- numerator (* denominator (ss-tdiv numerator denominator)))
    0))

(defun ss-power2 (exponent)
  (expt 2 (nfix exponent)))

;; Exact finite counts on half-open integer intervals.

(defun ss-below-count (matrix column value lower upper)
  (declare (xargs :measure (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (if (<= (ss-elt matrix lower column) value) 1 0)
     (ss-below-count matrix column value (+ lower 1) upper))))

(defun ss-above-count (matrix column value lower upper)
  (declare (xargs :measure (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (if (< value (ss-elt matrix lower column)) 1 0)
     (ss-above-count matrix column value (+ lower 1) upper))))

(defun ss-row-value-count (matrix row value lower upper)
  (declare (xargs :measure (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (if (equal (ss-elt matrix row lower) value) 1 0)
     (ss-row-value-count matrix row value (+ lower 1) upper))))

(defun ss-column-value-count (matrix column value lower upper)
  (declare (xargs :measure (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (if (equal (ss-elt matrix lower column) value) 1 0)
     (ss-column-value-count
      matrix column value (+ lower 1) upper))))

(defun ss-mocc-columns (matrix value row column columns)
  (declare (xargs :measure (nfix (- columns column))))
  (if (or
       (not (integerp column))
       (not (integerp columns))
       (<= columns column))
      0
    (+
     (if (equal (ss-elt matrix row column) value) 1 0)
     (ss-mocc-columns matrix value row (+ column 1) columns))))

(defun ss-mocc-rows (matrix value row rows columns)
  (declare (xargs :measure (nfix (- rows row))))
  (if (or
       (not (integerp row))
       (not (integerp rows))
       (<= rows row))
      0
    (+
     (ss-mocc-columns matrix value row 0 columns)
     (ss-mocc-rows matrix value (+ row 1) rows columns))))

(defun ss-mocc (matrix value rows columns)
  (ss-mocc-rows matrix value 0 rows columns))

(defun-sk ss-row-permut-p (left left-row right right-row lower upper)
  (forall
   (value)
   (implies
    (integerp value)
    (equal
     (ss-row-value-count left left-row value lower upper)
     (ss-row-value-count right right-row value lower upper)))))

(defun-sk ss-column-permut-p
  (left left-column right right-column lower upper)
  (forall
   (value)
   (implies
    (integerp value)
    (equal
     (ss-column-value-count left left-column value lower upper)
     (ss-column-value-count right right-column value lower upper)))))

(defun-sk ss-row-permutations-p (left right rows columns)
  (forall
   (row)
   (implies
    (and (integerp row) (<= 0 row) (< row rows))
    (ss-row-permut-p left row right row 0 columns))))

(defun-sk ss-column-permutations-p (left right rows columns)
  (forall
   (column)
   (implies
    (and (integerp column) (<= 0 column) (< column columns))
    (ss-column-permut-p left column right column 0 rows))))

(defun-sk ss-mocc-preserved-p (original current rows columns)
  (forall
   (value)
   (implies
    (integerp value)
    (equal
     (ss-mocc original value rows columns)
     (ss-mocc current value rows columns)))))

;; Matrix ordering predicates used by the contract and loop invariants.

(defun-sk ss-cross-row-order-p (matrix rows columns)
  (forall
   (i j1 j2 k)
   (implies
    (and
     (integerp i) (integerp j1) (integerp j2) (integerp k)
     (<= 0 i) (< i k) (< k rows)
     (<= 0 j1) (< j1 columns)
     (<= 0 j2) (< j2 columns))
    (<= (ss-elt matrix i j1) (ss-elt matrix k j2)))))

(defun-sk ss-snake-row-order-p (matrix rows columns)
  (forall
   (i j k)
   (implies
    (and
     (integerp i) (integerp j) (integerp k)
     (<= 0 i) (< i rows)
     (<= 0 j) (<= j k) (< k columns))
    (if (equal (ss-tmod i 2) 0)
        (<= (ss-elt matrix i j) (ss-elt matrix i k))
      (<= (ss-elt matrix i k) (ss-elt matrix i j))))))

(defun-sk ss-column-order-p (matrix rows columns)
  (forall
   (i j k)
   (implies
    (and
     (integerp i) (integerp j) (integerp k)
     (<= 0 i) (<= i k) (< k rows)
     (<= 0 j) (< j columns))
    (<= (ss-elt matrix i j) (ss-elt matrix k j)))))

(defun-sk ss-threshold-bounds-p (zeros ones rows width)
  (forall
   (value)
   (implies
    (integerp value)
    (and
     (<= 0 (ss-apply zeros value))
     (<= (ss-apply zeros value) (ss-apply ones value))
     (<= (ss-apply ones value) rows)
     (<= (ss-apply ones value)
         (+ (ss-apply zeros value) width))))))

(defun-sk ss-threshold-elements-p (matrix zeros ones rows columns)
  (forall
   (value i j)
   (implies
    (and
     (integerp value) (integerp i) (integerp j)
     (<= 0 j) (< j columns))
    (and
     (implies
      (and (<= 0 i) (< i (ss-apply zeros value)))
      (<= (ss-elt matrix i j) value))
     (implies
      (and (<= (ss-apply ones value) i) (< i rows))
      (< value (ss-elt matrix i j)))))))

(defun ss-threshold-state-p
  (matrix zeros ones rows columns width)
  (and
   (ss-int-function-p zeros)
   (ss-int-function-p ones)
   (ss-threshold-bounds-p zeros ones rows width)
   (ss-threshold-elements-p matrix zeros ones rows columns)))

(defun ss-log-interval-p (k ind rows)
  (and
   (< (* (- k 1) (ss-power2 ind)) rows)
   (<= rows (* k (ss-power2 ind)))))

(defun ss-loop-state-p
  (original current zeros ones k ind l rows columns)
  (and
   (integerp k) (integerp ind)
   (<= 0 ind) (<= ind l)
   (ss-threshold-state-p current zeros ones rows columns k)
   (< 0 k)
   (ss-log-interval-p k ind rows)
   (implies
    (< l ind)
    (ss-snake-row-order-p current rows columns))
   (ss-mocc-preserved-p original current rows columns)))

;; The local SELECT routine's full recursive and while-loop VC.

(defun-sk ss-function-row-order-p (function columns ascending)
  (forall
   (j k)
   (implies
    (and
     (integerp j) (integerp k)
     (<= 0 j) (<= j k) (< k columns))
    (if ascending
        (<= (ss-apply function j) (ss-apply function k))
      (<= (ss-apply function k) (ss-apply function j))))))

(defun-sk ss-select-result-p (r1 r2 result value columns)
  (forall
   (i)
   (implies
    (and (integerp i) (<= 0 i) (< i columns))
    (if result
        (or
         (<= (ss-apply r1 i) value)
         (<= (ss-apply r2 i) value))
      (or
       (< value (ss-apply r1 i))
       (< value (ss-apply r2 i)))))))

(defun-sk ss-swapped-result-obligation-p (r1 r2 value columns)
  (forall
   (result)
   (implies
    (and
     (or (equal result t) (equal result nil))
     (ss-select-result-p r2 r1 result value columns))
    (ss-select-result-p r1 r2 result value columns))))

(defun-sk ss-select-prefix-p (r1 r2 value upper)
  (forall
   (j)
   (implies
    (and (integerp j) (<= 0 j) (< j upper))
    (and
     (<= (ss-apply r1 j) value)
     (< value (ss-apply r2 j))))))

(defun-sk ss-select-final-result-p (r1 r2 value columns i)
  (forall
   (result)
   (implies
    (and
     (or (equal result t) (equal result nil))
     (equal
      result
      (if (equal i columns)
          t
        (<= (ss-apply r2 i) value))))
    (ss-select-result-p r1 r2 result value columns))))

(defun ss-select-loop-outcome-p (r1 r2 value columns i outcome)
  (if outcome
      (and
       (<= 0 (- columns i))
       (< (- columns (+ i 1)) (- columns i))
       (<= 0 (+ i 1))
       (<= (+ i 1) columns)
       (ss-select-prefix-p r1 r2 value (+ i 1)))
    (ss-select-final-result-p r1 r2 value columns i)))

(defun-sk ss-select-loop-step-p (r1 r2 value columns i)
  (forall
   (outcome)
   (implies
    (and
     (or (equal outcome t) (equal outcome nil))
     (equal
      outcome
      (if (not (equal i columns))
          (if (<= (ss-apply r1 i) value)
              (< value (ss-apply r2 i))
            nil)
        nil)))
    (ss-select-loop-outcome-p
     r1 r2 value columns i outcome))))

(defun-sk ss-select-loop-vc-p (r1 r2 value columns)
  (forall
   (i)
   (implies
    (and
     (integerp i)
     (<= 0 i) (<= i columns)
     (ss-select-prefix-p r1 r2 value i))
    (ss-select-loop-step-p r1 r2 value columns i))))

(defun ss-select-vc-p (r1 r2 b value columns)
  (if (not b)
      (and
       (<= 0 (if b 0 1))
       (< 0 (if b 0 1))
       (ss-function-row-order-p r2 columns t)
       (ss-function-row-order-p r1 columns nil)
       (ss-swapped-result-obligation-p r1 r2 value columns))
    (and
     (<= 0 columns)
     (ss-select-prefix-p r1 r2 value 0)
     (ss-select-loop-vc-p r1 r2 value columns))))

(defun-sk ss-all-select-vcs-p (value columns)
  (forall
   (r1 r2 b)
   (implies
    (and
     (ss-int-function-p r1)
     (ss-int-function-p r2)
     (or (equal b t) (equal b nil))
     (ss-function-row-order-p r1 columns b)
     (ss-function-row-order-p r2 columns (not b)))
    (ss-select-vc-p r1 r2 b value columns))))

;; NZO loop obligations after all rows have been snake-sorted.

(defun-sk ss-nzo-column-counts-p
  (matrix value index no nz o rows columns)
  (forall
   (column)
   (implies
    (and
     (integerp column)
     (<= 0 column) (< column columns))
    (and
     (<= nz
         (ss-below-count matrix column value 0 index))
     (<= (- rows no)
         (+
          (ss-above-count matrix column value 0 index)
          (ss-above-count matrix column value o rows)))))))

(defun ss-nzo-state-p
  (matrix value z o index no nz rows columns)
  (and
   (integerp index) (integerp no) (integerp nz)
   (<= z index) (<= index o)
   (<= z nz) (<= no o)
   (equal
    (- index z)
    (* 2 (+ (- nz z) (- o no))))
   (ss-nzo-column-counts-p
    matrix value index no nz o rows columns)))

(defun-sk ss-matrix-select-result-p
  (matrix row1 row2 result value columns)
  (forall
   (i)
   (implies
    (and (integerp i) (<= 0 i) (< i columns))
    (if result
        (or
         (<= (ss-elt matrix row1 i) value)
         (<= (ss-elt matrix row2 i) value))
      (or
       (< value (ss-elt matrix row1 i))
       (< value (ss-elt matrix row2 i)))))))

(defun-sk ss-matrix-row-order-p (matrix row columns ascending)
  (forall
   (j k)
   (implies
    (and
     (integerp j) (integerp k)
     (<= 0 j) (<= j k) (< k columns))
    (if ascending
        (<= (ss-elt matrix row j) (ss-elt matrix row k))
      (<= (ss-elt matrix row k) (ss-elt matrix row j))))))

(defun ss-nzo-updated-state-p
  (matrix value z o index no nz rows columns selected)
  (let ((next-index (+ index 2)))
    (if selected
        (and
         (<= 0 (- o index))
         (< (- o next-index) (- o index))
         (<= z next-index) (<= next-index o)
         (<= z (+ nz 1)) (<= no o)
         (equal
          (- next-index z)
          (* 2 (+ (- (+ nz 1) z) (- o no))))
         (ss-nzo-column-counts-p
          matrix value next-index no (+ nz 1) o rows columns))
      (and
       (<= 0 (- o index))
       (< (- o next-index) (- o index))
       (<= z next-index) (<= next-index o)
       (<= z nz) (<= (- no 1) o)
       (equal
        (- next-index z)
        (* 2 (+ (- nz z) (- o (- no 1)))))
       (ss-nzo-column-counts-p
        matrix value next-index (- no 1) nz o rows columns)))))

(defun-sk ss-nzo-selection-step-p
  (matrix value z o index no nz rows columns)
  (forall
   (selected)
   (implies
    (and
     (or (equal selected t) (equal selected nil))
     (ss-matrix-select-result-p
      matrix index (+ index 1) selected value columns))
    (ss-nzo-updated-state-p
     matrix value z o index no nz rows columns selected))))

(defun-sk ss-nzo-final-counts-p
  (matrix value nz no rows columns)
  (forall
   (column)
   (implies
    (and
     (integerp column)
     (<= 0 column) (< column columns))
    (and
     (<= nz
         (ss-below-count matrix column value 0 rows))
     (<= (- rows no)
         (ss-above-count matrix column value 0 rows))))))

(defun ss-nzo-result-p
  (matrix value nz no kd rows columns)
  (and
   (integerp nz) (integerp no)
   (<= 0 nz) (<= nz no) (<= no rows)
   (<= no (+ nz kd))
   (ss-nzo-final-counts-p
    matrix value nz no rows columns)))

(defun ss-nzo-loop-case-p
  (matrix value z o index no nz kd rows columns)
  (if (< (+ index 1) o)
      (and
       (ss-all-select-vcs-p value columns)
       (not (equal 2 0))
       (ss-matrix-row-order-p
        matrix index columns
        (equal (ss-tmod index 2) 0))
       (ss-matrix-row-order-p
        matrix (+ index 1) columns
        (not (equal (ss-tmod index 2) 0)))
       (ss-nzo-selection-step-p
        matrix value z o index no nz rows columns))
    (ss-nzo-result-p matrix value nz no kd rows columns)))

(defun-sk ss-nzo-loop-vc-p
  (matrix value z o kd rows columns)
  (forall
   (index no nz)
   (implies
    (ss-nzo-state-p
     matrix value z o index no nz rows columns)
    (ss-nzo-loop-case-p
     matrix value z o index no nz kd rows columns))))

(defun ss-nzo-vc-for-value-p
  (matrix zeros ones value kd rows columns)
  (let ((z (ss-apply zeros value))
        (o (ss-apply ones value)))
    (and
     (ss-nzo-state-p matrix value z o z o z rows columns)
     (ss-nzo-loop-vc-p matrix value z o kd rows columns))))

(defun-sk ss-all-nzo-vcs-p
  (matrix zeros ones kd rows columns)
  (forall
   (value)
   (implies
    (integerp value)
    (ss-nzo-vc-for-value-p
     matrix zeros ones value kd rows columns))))

(defun-sk ss-nzo-function-result-p
  (matrix nzo kd rows columns)
  (forall
   (value)
   (implies
    (integerp value)
    (ss-nzo-result-p
     matrix value
     (ss-first nzo value)
     (ss-second nzo value)
     kd rows columns))))

(defun-sk ss-function-is-first-p (newz nzo)
  (forall
   (value)
   (implies
    (integerp value)
    (equal
     (ss-apply newz value)
     (ss-first nzo value)))))

(defun-sk ss-function-is-second-p (newo nzo)
  (forall
   (value)
   (implies
    (integerp value)
    (equal
     (ss-apply newo value)
     (ss-second nzo value)))))

;; Obligations following a column sort, including the two ghost recursive
;; searches used to establish the new threshold bounds.

(defun-sk ss-aux-top-vc-p (matrix rows columns)
  (forall
   (value i j)
   (implies
    (and
     (integerp value) (integerp i) (integerp j)
     (<= 0 i) (< i rows)
     (< 0 (ss-below-count matrix j value (+ i 1) rows))
     (<= 0 j) (< j columns)
     (< value (ss-elt matrix i j)))
    (let ((next (+ i 1)))
      (and
       (<= 0 (- rows i))
       (< (- rows next) (- rows i))
       (<= 0 next) (< next rows)
       (< 0 (ss-below-count matrix j value (+ next 1) rows))
       (<= 0 j) (< j columns)
       (< value (ss-elt matrix next j)))))))

(defun-sk ss-aux-bottom-vc-p (matrix rows columns)
  (forall
   (value i j)
   (implies
    (and
     (integerp value) (integerp i) (integerp j)
     (<= 0 i) (< i rows)
     (< 0 (ss-above-count matrix j value 0 i))
     (<= 0 j) (< j columns)
     (<= (ss-elt matrix i j) value))
    (let ((previous (- i 1)))
      (and
       (<= 0 i)
       (< previous i)
       (<= 0 previous) (< previous rows)
       (< 0 (ss-above-count matrix j value 0 previous))
       (<= 0 j) (< j columns)
       (<= (ss-elt matrix previous j) value))))))

(defun ss-after-column-sort-p
  (original matrix newz newo kd ind l rows columns)
  (and
   (ss-aux-top-vc-p matrix rows columns)
   (ss-aux-bottom-vc-p matrix rows columns)
   (ss-threshold-state-p matrix newz newo rows columns kd)
   (< 0 kd)
   (ss-log-interval-p kd (+ ind 1) rows)
   (implies
    (< l (+ ind 1))
    (ss-snake-row-order-p matrix rows columns))
   (ss-mocc-preserved-p original matrix rows columns)))

(defun-sk ss-all-column-sorts-p
  (original before newz newo kd ind l rows columns)
  (forall
   (after)
   (implies
    (and
     (ss-matrix-p after)
     (equal (ss-rows after) (ss-rows before))
     (equal (ss-columns after) (ss-columns before)))
    (implies
     (and
      (ss-column-permutations-p after before rows columns)
      (ss-column-order-p after rows columns))
     (ss-after-column-sort-p
      original after newz newo kd ind l rows columns)))))

;; ACL2 requires called functions to have appeared earlier, so the mutually
;; nested existential-free continuations are ordered from the inside out.

(defun-sk ss-new-ones-continuation-p
  (original matrix zeros ones nzo newz kd ind l rows columns)
  (forall
   (newo)
   (implies
    (and
     (ss-int-function-p newo)
     (ss-function-is-second-p newo nzo))
    (and
     (implies
      (equal ind l)
      (ss-threshold-state-p matrix zeros ones rows columns 1))
     (implies
      (implies
       (equal ind l)
       (ss-cross-row-order-p matrix rows columns))
      (ss-all-column-sorts-p
       original matrix newz newo kd ind l rows columns))))))

(defun-sk ss-all-new-zero-functions-p
  (original matrix zeros ones nzo kd ind l rows columns)
  (forall
   (newz)
   (implies
    (and
     (ss-int-function-p newz)
     (ss-function-is-first-p newz nzo))
    (ss-new-ones-continuation-p
     original matrix zeros ones nzo newz kd ind l rows columns))))

(defun-sk ss-all-nzo-functions-p
  (original matrix zeros ones kd ind l rows columns)
  (forall
   (nzo)
   (implies
    (and
     (ss-pair-function-p nzo)
     (ss-nzo-function-result-p matrix nzo kd rows columns))
    (ss-all-new-zero-functions-p
     original matrix zeros ones nzo kd ind l rows columns))))

(defun ss-after-row-sort-p
  (original matrix zeros ones k ind l rows columns)
  (let ((kd (ss-tdiv (+ k 1) 2)))
    (and
     (not (equal 2 0))
     (ss-all-nzo-vcs-p matrix zeros ones kd rows columns)
     (ss-all-nzo-functions-p
      original matrix zeros ones kd ind l rows columns))))

(defun-sk ss-all-row-sorts-p
  (original before zeros ones k ind l rows columns)
  (forall
   (after)
   (implies
    (and
     (ss-matrix-p after)
     (equal (ss-rows after) (ss-rows before))
     (equal (ss-columns after) (ss-columns before)))
    (implies
     (and
      (ss-row-permutations-p after before rows columns)
      (ss-snake-row-order-p after rows columns))
     (ss-after-row-sort-p
      original after zeros ones k ind l rows columns)))))

(defun-sk ss-all-loop-indices-p
  (original current zeros ones k l rows columns)
  (forall
   (ind)
   (implies
    (ss-loop-state-p
     original current zeros ones k ind l rows columns)
    (ss-all-row-sorts-p
     original current zeros ones k ind l rows columns))))

(defun ss-final-contract-p (original current rows columns include-mocc)
  (and
   (ss-cross-row-order-p current rows columns)
   (ss-snake-row-order-p current rows columns)
   (implies
    include-mocc
    (ss-mocc-preserved-p original current rows columns))))

(defun ss-post-loop-obligation-p
  (original current zeros ones k l rows columns)
  (implies
   (and
    (ss-threshold-state-p current zeros ones rows columns k)
    (< 0 k)
    (ss-log-interval-p k (+ l 1) rows)
    (implies
     (< l (+ l 1))
     (ss-snake-row-order-p current rows columns))
    (ss-mocc-preserved-p original current rows columns))
   (and
    (ss-threshold-state-p current zeros ones rows columns 1)
    (implies
     (ss-cross-row-order-p current rows columns)
     (ss-final-contract-p
      original current rows columns t)))))

(defun ss-negative-loop-obligation-p (matrix rows columns l)
  (implies
   (< (+ l 1) 0)
   (and
    ;; With the source constants zeros(v)=0 and ones(v)=rows, this is exactly
    ;; the width-one initial threshold state.
    (<= rows 1)
    (implies
     (ss-cross-row-order-p matrix rows columns)
     (ss-final-contract-p matrix matrix rows columns nil)))))

(defun ss-loop-state-family-body-p
  (original current zeros ones k l rows columns)
  (and
   (ss-all-loop-indices-p
    original current zeros ones k l rows columns)
   (ss-post-loop-obligation-p
    original current zeros ones k l rows columns)
   (ss-negative-loop-obligation-p original rows columns l)))

(defun-sk ss-all-loop-state-families-p
  (original l rows columns)
  (forall
   (ones zeros k current)
   (implies
    (and
     (ss-int-function-p ones)
     (ss-int-function-p zeros)
     (integerp k)
     (ss-matrix-p current)
     (equal (ss-rows current) rows)
     (equal (ss-columns current) columns))
    (ss-loop-state-family-body-p
     original current zeros ones k l rows columns))))

(defun-sk ss-column-sorted-procedure-vc-p (rows columns)
  (forall
   (ones zeros matrix)
   (implies
    (and
     (ss-int-function-p ones)
     (ss-int-function-p zeros)
     (ss-matrix-p matrix)
     (equal (ss-rows matrix) rows)
     (equal (ss-columns matrix) columns)
     (ss-threshold-state-p matrix zeros ones rows columns 1))
    (ss-cross-row-order-p matrix rows columns))))

(defun ss-zero-phase-p (matrix l rows columns)
  (and
   (ss-column-sorted-procedure-vc-p rows columns)
   (implies
    (<= 0 (+ l 1))
    (and
     ;; Source constants fc/fc1/fc5/fc6 are zero and fc2/fc3/fc4/fc7
     ;; are rows, so the initial threshold clauses reduce exactly to rows>=0.
     (<= 0 rows)
     (< 0 rows)
     (ss-log-interval-p rows 0 rows)
     (implies
      (< l 0)
      (ss-snake-row-order-p matrix rows columns))
     (ss-all-loop-state-families-p matrix l rows columns)))
   (implies
    (< (+ l 1) 0)
    (and
     (<= rows 1)
     (implies
      (ss-cross-row-order-p matrix rows columns)
      (ss-final-contract-p matrix matrix rows columns nil))))))

(defun ss-log-loop-step-p (p l rows)
  (if (not (equal p 0))
      (let ((next-p (ss-tdiv p 2))
            (next-l (+ l 1)))
        (and
         (not (equal 2 0))
         (<= 0 p)
         (< next-p p)
         (<= 0 next-l)
         (<= 0 next-p)
         (implies
          (not (equal next-l 0))
          (<= (ss-power2 (- next-l 1)) rows))
         (< (* next-p (ss-power2 next-l)) rows)
         (<= rows (* (ss-power2 next-l) (+ next-p 1)))))
    t))

(defun-sk ss-all-log-loop-states-p (matrix rows columns)
  (forall
   (p l)
   (implies
    (and
     (integerp p) (integerp l)
     (<= 0 l) (<= 0 p)
     (implies
      (not (equal l 0))
      (<= (ss-power2 (- l 1)) rows))
     (< (* p (ss-power2 l)) rows)
     (<= rows (* (ss-power2 l) (+ p 1))))
    (if (not (equal p 0))
        (ss-log-loop-step-p p l rows)
      (ss-zero-phase-p matrix l rows columns)))))

(defun ss-shear-sort-vc-for-matrix-p (matrix)
  (let ((rows (ss-rows matrix))
        (columns (ss-columns matrix)))
    (if (not (equal rows 0))
        (let ((initial-p (- rows 1)))
          (and
           (<= 0 initial-p)
           (< (* initial-p (ss-power2 0)) rows)
           (<= rows (* (ss-power2 0) (+ initial-p 1)))
           (ss-all-log-loop-states-p matrix rows columns)))
      (ss-final-contract-p matrix matrix rows columns nil))))

(defun-sk ntp4vc-shearsort-shear-sort-statement ()
  (forall
   (matrix)
   (implies
    (ss-matrix-p matrix)
    (ss-shear-sort-vc-for-matrix-p matrix))))

(value-triple :itpeval-statement-checked)

:q
