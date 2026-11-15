;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2021_shearsort_ShearSort_sort_rowqtvc: the verification
;; condition for copying a matrix row into an array, sorting and optionally
;; reversing it, and writing it back. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Why3 integer matrices remain arbitrary objects observed through total
;; dimension and entry operations. The predicate supplies the source matrix
;; invariant and integer entry type without bounding dimensions or entries.

(defstub sr-rows (matrix) t)
(defstub sr-columns (matrix) t)
(defstub sr-elt (matrix row column) t)

(defun-sk sr-matrix-p (matrix)
  (forall
   (row column)
   (and
    (integerp (sr-rows matrix))
    (integerp (sr-columns matrix))
    (<= 0 (sr-rows matrix))
    (<= 0 (sr-columns matrix))
    (implies
     (and (integerp row) (integerp column))
     (integerp (sr-elt matrix row column))))))

(defun sr-same-dimensions-p (left right)
  (and
   (equal (sr-rows left) (sr-rows right))
   (equal (sr-columns left) (sr-columns right))))

(defun sr-valid-index-p (matrix row column)
  (and
   (integerp row)
   (integerp column)
   (<= 0 row)
   (< row (sr-rows matrix))
   (<= 0 column)
   (< column (sr-columns matrix))))

;; ACL2 finite true lists of integers represent Why3 arrays and exported
;; integer lists. Int.toNat maps negative integers to zero, and indexing
;; returns the inhabited integer default zero outside the list.

(defun sr-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (sr-integer-list-p (cdr xs)))
    (equal xs nil)))

(defun sr-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun sr-nth-int (index xs)
  (let ((natural-index (sr-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      0)))

;; Unlike ACL2's update-nth, List.set leaves an out-of-range list unchanged.

(defun sr-list-set-natural (xs index value)
  (declare (xargs :measure (nfix index)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (sr-list-set-natural
        (cdr xs) (- index 1) value)))))

(defun sr-list-set-int (xs index value)
  (sr-list-set-natural xs (sr-int-to-nat index) value))

;; MapPermut.permut is equality of all integer-value occurrence counts on a
;; half-open integer interval.

(defun sr-list-value-count (xs value lower upper)
  (declare (xargs :measure (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (if (equal (sr-nth-int lower xs) value) 1 0)
     (sr-list-value-count xs value (+ lower 1) upper))))

(defun sr-row-value-count (matrix row value lower upper)
  (declare (xargs :measure (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (if (equal (sr-elt matrix row lower) value) 1 0)
     (sr-row-value-count
      matrix row value (+ lower 1) upper))))

(defun-sk sr-list-permut-p (left right lower upper)
  (forall
   (value)
   (implies
    (integerp value)
    (equal
     (sr-list-value-count left value lower upper)
     (sr-list-value-count right value lower upper)))))

(defun-sk sr-row-permut-p
  (left right selected-row lower upper)
  (forall
   (value)
   (implies
    (integerp value)
    (equal
     (sr-row-value-count
      left selected-row value lower upper)
     (sr-row-value-count
      right selected-row value lower upper)))))

;; Extensional predicates represent the source equalities between total
;; integer-indexed functions.

(defun-sk sr-list-set-update-law-p (xs index value)
  (forall
   (argument)
   (implies
    (integerp argument)
    (equal
     (sr-nth-int
      argument
      (sr-list-set-int xs index value))
     (if (equal argument index)
         value
       (sr-nth-int argument xs))))))

(defun-sk sr-matrix-single-update-p
  (new old selected-row selected-column value)
  (forall
   (row column)
   (implies
    (and (integerp row) (integerp column))
    (equal
     (sr-elt new row column)
     (if (equal row selected-row)
         (if (equal column selected-column)
             value
           (sr-elt old selected-row column))
       (sr-elt old row column))))))

;; Array, row, and matrix predicates used directly by the generated
;; verification condition.

(defun-sk sr-zero-array-p (array length)
  (forall
   (index)
   (and
    (equal (len array) length)
    (implies
     (integerp index)
     (implies
      (and (<= 0 index) (< index length))
      (equal (sr-nth-int index array) 0))))))

(defun-sk sr-row-prefix-p (array matrix selected-row upper)
  (forall
   (index)
   (implies
    (integerp index)
    (implies
     (and (<= 0 index) (< index upper))
     (equal
      (sr-nth-int index array)
      (sr-elt matrix selected-row index))))))

(defun-sk sr-list-sorted-p (array)
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
      (sr-nth-int left array)
      (sr-nth-int right array))))))

(defun-sk sr-unchanged-except-row-p
  (current original selected-row)
  (forall
   (row column)
   (implies
    (and
     (integerp row)
     (integerp column)
     (<= 0 row)
     (< row (sr-rows current))
     (<= 0 column)
     (< column (sr-columns current))
     (not (equal row selected-row)))
    (equal
     (sr-elt current row column)
     (sr-elt original row column)))))

(defun-sk sr-selected-row-sorted-p
  (matrix selected-row ascending)
  (forall
   (left right)
   (implies
    (and (integerp left) (integerp right))
    (implies
     (and
      (<= 0 left)
      (<= left right)
      (< right (sr-columns matrix)))
     (if (equal ascending t)
         (<=
          (sr-elt matrix selected-row left)
          (sr-elt matrix selected-row right))
       (<=
        (sr-elt matrix selected-row right)
        (sr-elt matrix selected-row left)))))))

(defun sr-final-contract-p
  (current original selected-row ascending)
  (and
   (sr-unchanged-except-row-p
    current original selected-row)
   (sr-selected-row-sorted-p
    current selected-row ascending)
   (sr-row-permut-p
    current original selected-row
    0 (sr-columns current))))

(defun sr-original-negative-contract-p
  (matrix selected-row ascending)
  (and
   (sr-selected-row-sorted-p
    matrix selected-row ascending)
   (sr-row-permut-p
    matrix matrix selected-row
    0 (sr-columns matrix))))

;; Write-back loop: every matrix state and every loop index retain the exact
;; invariant and update obligations from the source VC.

(defun-sk sr-all-single-update-results-p
  (array original current selected-row index value)
  (forall
   (next)
   (implies
    (sr-matrix-p next)
    (implies
     (sr-same-dimensions-p next current)
     (implies
      (sr-matrix-single-update-p
       next current selected-row index value)
      (and
       (sr-row-prefix-p
        array next selected-row (+ index 1))
       (sr-unchanged-except-row-p
        next original selected-row)))))))

(defun sr-write-index-result-p
  (array original current selected-row index)
  (and
   (<= 0 index)
   (< index (len array))
   (sr-valid-index-p current selected-row index)
   (sr-all-single-update-results-p
    array
    original
    current
    selected-row
    index
    (sr-nth-int index array))))

(defun-sk sr-all-write-indices-p
  (array original current selected-row upper)
  (forall
   (index)
   (implies
    (integerp index)
    (implies
     (and
      (<= 0 index)
      (<= index upper)
      (sr-row-prefix-p
       array current selected-row index)
      (sr-unchanged-except-row-p
       current original selected-row))
     (sr-write-index-result-p
      array original current selected-row index)))))

(defun sr-write-exit-p
  (array original current selected-row ascending upper)
  (implies
   (and
    (sr-row-prefix-p
     array current selected-row (+ upper 1))
    (sr-unchanged-except-row-p
     current original selected-row))
   (sr-final-contract-p
    current original selected-row ascending)))

(defun-sk sr-all-write-loop-matrices-p
  (array original selected-row ascending upper)
  (forall
   (current)
   (implies
    (sr-matrix-p current)
    (implies
     (sr-same-dimensions-p current original)
     (and
      (sr-all-write-indices-p
       array original current selected-row upper)
      (sr-write-exit-p
       array original current selected-row
       ascending upper))))))

(defun sr-write-back-vc-p
  (array original selected-row ascending)
  (let ((upper (- (sr-columns original) 1)))
    (and
     (implies
      (<= 0 (+ upper 1))
      (and
       (sr-row-prefix-p
        array original selected-row 0)
       (sr-all-write-loop-matrices-p
        array original selected-row ascending upper)))
     (implies
      (< (+ upper 1) 0)
      (sr-original-negative-contract-p
       original selected-row ascending)))))

;; The optional reversal branch keeps the source loop's exact middle,
;; reflected-outside, and permutation invariants.

(defun-sk sr-reversal-middle-p
  (current sorted lower upper)
  (forall
   (index)
   (implies
    (integerp index)
    (implies
     (and (<= lower index) (<= index upper))
     (equal
      (sr-nth-int index current)
      (sr-nth-int index sorted))))))

(defun-sk sr-reversal-outside-p
  (current sorted lower upper)
  (forall
   (index)
   (implies
    (integerp index)
    (implies
     (or
      (and (<= 0 index) (< index lower))
      (and (< upper index) (< index (len current))))
     (equal
      (sr-nth-int index current)
      (sr-nth-int
       (- (- (len current) 1) index)
       sorted))))))

(defun sr-reversal-invariant-p
  (current sorted lower upper)
  (and
   (<= 0 lower)
   (<= lower (+ upper 1))
   (<= (+ upper 1) (len current))
   (equal (+ lower upper) (- (len current) 1))
   (sr-reversal-middle-p current sorted lower upper)
   (sr-reversal-outside-p current sorted lower upper)
   (sr-list-permut-p sorted current 0 (len current))))

(defun-sk sr-exchange-p (after before lower upper)
  (forall
   (index)
   (and
    (<= 0 lower)
    (< lower (len after))
    (<= 0 upper)
    (< upper (len after))
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (<= index (len after))
       (not (equal index lower))
       (not (equal index upper)))
      (equal
       (sr-nth-int index after)
       (sr-nth-int index before))))
    (equal
     (sr-nth-int lower after)
     (sr-nth-int upper before))
    (equal
     (sr-nth-int upper after)
     (sr-nth-int lower before)))))

(defun sr-next-reversal-invariant-p
  (after sorted lower upper)
  (and
   (<= 0 (- upper lower))
   (<
    (- (- upper 1) (+ lower 1))
    (- upper lower))
   (sr-reversal-invariant-p
    after sorted (+ lower 1) (- upper 1))))

(defun sr-reversal-step-p
  (current sorted original selected-row ascending lower upper)
  (if (< lower upper)
      (and
       (<= 0 upper)
       (< upper (len current))
       (let ((temporary (sr-nth-int upper current)))
         (and
          (<= 0 lower)
          (< lower (len current))
          (let* ((lower-value (sr-nth-int lower current))
                 (after-upper
                  (sr-list-set-int
                   current upper lower-value)))
            (and
             (<= 0 upper)
             (< upper (len current))
             (implies
              (equal
               (len after-upper)
               (len current))
              (implies
               (sr-list-set-update-law-p
                current upper lower-value)
               (and
                (<= 0 lower)
                (< lower (len after-upper))
                (let ((after
                       (sr-list-set-int
                        after-upper lower temporary)))
                  (implies
                   (equal
                    (len after)
                    (len after-upper))
                   (implies
                    (sr-list-set-update-law-p
                     after-upper lower temporary)
                    (and
                     (sr-exchange-p
                      after current lower upper)
                     (implies
                      (sr-list-permut-p
                       after current 0 (len after))
                     (sr-next-reversal-invariant-p
                       after sorted lower upper))))))))))))))
    (sr-write-back-vc-p
     current original selected-row ascending)))

(defun-sk sr-all-reversal-states-p
  (sorted original selected-row ascending)
  (forall
   (upper lower current)
   (implies
    (and
     (integerp upper)
     (integerp lower)
     (sr-integer-list-p current))
    (implies
     (equal (len current) (len sorted))
     (implies
      (sr-reversal-invariant-p
       current sorted lower upper)
      (sr-reversal-step-p
       current sorted original selected-row
       ascending lower upper))))))

(defun sr-reversal-vc-p
  (sorted original selected-row ascending)
  (let ((upper (- (len sorted) 1)))
    (and
     (sr-reversal-invariant-p
      sorted sorted 0 upper)
     (sr-all-reversal-states-p
      sorted original selected-row ascending))))

(defun sr-after-sort-vc-p
  (sorted original selected-row ascending)
  (if (equal ascending nil)
      (sr-reversal-vc-p
       sorted original selected-row ascending)
    (sr-write-back-vc-p
     sorted original selected-row ascending)))

;; Sorting is specified by universal post-state quantification, matching the
;; source call to the abstract array-sort procedure.

(defun-sk sr-all-sorted-results-p
  (before original selected-row ascending)
  (forall
   (after)
   (implies
    (sr-integer-list-p after)
    (implies
     (equal (len after) (len before))
     (implies
      (and
       (sr-list-sorted-p after)
       (sr-list-permut-p
        after before 0 (len after)))
      (sr-after-sort-vc-p
       after original selected-row ascending))))))

;; Copy loop: List.set's length and extensional update properties remain
;; explicit antecedents, exactly as in the generated VC.

(defun sr-copy-index-result-p
  (array matrix selected-row index)
  (let ((value (sr-elt matrix selected-row index)))
    (and
     (sr-valid-index-p matrix selected-row index)
     (<= 0 index)
     (< index (len array))
     (implies
      (equal
       (len (sr-list-set-int array index value))
       (len array))
      (implies
       (sr-list-set-update-law-p array index value)
       (sr-row-prefix-p
        (sr-list-set-int array index value)
        matrix
        selected-row
        (+ index 1)))))))

(defun-sk sr-all-copy-indices-p
  (array matrix selected-row upper)
  (forall
   (index)
   (implies
    (integerp index)
    (implies
     (and
      (<= 0 index)
      (<= index upper)
      (sr-row-prefix-p
       array matrix selected-row index))
     (sr-copy-index-result-p
      array matrix selected-row index)))))

(defun sr-copy-exit-p
  (array matrix selected-row ascending upper)
  (implies
   (sr-row-prefix-p
    array matrix selected-row (+ upper 1))
   (sr-all-sorted-results-p
    array matrix selected-row ascending)))

(defun-sk sr-all-copy-loop-arrays-p
  (initial matrix selected-row ascending upper)
  (forall
   (current)
   (implies
    (sr-integer-list-p current)
    (implies
     (equal (len current) (len initial))
     (and
      (sr-all-copy-indices-p
       current matrix selected-row upper)
      (sr-copy-exit-p
       current matrix selected-row
       ascending upper))))))

(defun-sk sr-all-negative-copy-results-p
  (initial matrix selected-row ascending)
  (forall
   (current)
   (implies
    (sr-integer-list-p current)
    (implies
     (equal (len current) (len initial))
     (implies
      (and
       (sr-list-sorted-p current)
       (sr-list-permut-p
        current initial 0 (len current)))
      (sr-after-sort-vc-p
       current matrix selected-row ascending))))))

(defun sr-copy-and-sort-vc-p
  (initial matrix selected-row ascending)
  (let ((upper (- (sr-columns matrix) 1)))
    (and
     (implies
      (<= 0 (+ upper 1))
      (and
       (sr-row-prefix-p
        initial matrix selected-row 0)
       (sr-all-copy-loop-arrays-p
        initial matrix selected-row
        ascending upper)))
     (implies
      (< (+ upper 1) 0)
      (sr-all-negative-copy-results-p
       initial matrix selected-row ascending)))))

(defun-sk sr-all-initial-arrays-p
  (matrix selected-row ascending columns)
  (forall
   (initial)
   (implies
    (sr-integer-list-p initial)
    (implies
     (sr-zero-array-p initial columns)
     (sr-copy-and-sort-vc-p
      initial matrix selected-row ascending)))))

;; The complete unproved verification condition.

(defun
    ntp4vc-pearl-verifythis-2021-shearsort-shearsort-sort-rowqtvc-statement
    (selected-row matrix ascending)
  (implies
   (and
    (integerp selected-row)
    (sr-matrix-p matrix)
    (or (equal ascending t) (equal ascending nil))
    (<= 0 selected-row)
    (< selected-row (sr-rows matrix)))
   (let ((columns (sr-columns matrix)))
     (and
      (<= 0 columns)
      (sr-all-initial-arrays-p
       matrix selected-row ascending columns)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
