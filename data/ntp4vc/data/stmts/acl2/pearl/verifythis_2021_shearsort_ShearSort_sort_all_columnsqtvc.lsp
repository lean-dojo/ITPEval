;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2021_shearsort_ShearSort_sort_all_columnsqtvc: the
;; verification condition for sorting every matrix column, either directly
;; or by transposing, sorting rows, and transposing back. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Why3 integer matrices remain arbitrary objects observed through total
;; row, column, and entry operations.  The predicate supplies exactly the
;; source matrix invariant and integer element type, without bounding either
;; dimensions or entries.

(defstub sac-rows (matrix) t)
(defstub sac-columns (matrix) t)
(defstub sac-elt (matrix row column) t)

(defun-sk sac-matrix-p (matrix)
  (forall
   (row column)
   (and
    (integerp (sac-rows matrix))
    (integerp (sac-columns matrix))
    (<= 0 (sac-rows matrix))
    (<= 0 (sac-columns matrix))
    (implies
     (and (integerp row) (integerp column))
     (integerp (sac-elt matrix row column))))))

;; MapPermut.permut is equality of all value-occurrence counts on a half-open
;; integer interval.  All intervals used here start at zero and have a
;; nonnegative matrix dimension as upper endpoint.

(defun sac-column-value-count (matrix column value lower upper)
  (declare (xargs :measure (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (if (equal (sac-elt matrix lower column) value) 1 0)
     (sac-column-value-count
      matrix column value (+ lower 1) upper))))

(defun sac-row-value-count (matrix row value lower upper)
  (declare (xargs :measure (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (if (equal (sac-elt matrix row lower) value) 1 0)
     (sac-row-value-count
      matrix row value (+ lower 1) upper))))

(defun-sk sac-column-permut-p
  (left right column lower upper)
  (forall
   (value)
   (implies
    (integerp value)
    (equal
     (sac-column-value-count left column value lower upper)
     (sac-column-value-count right column value lower upper)))))

(defun-sk sac-row-permut-p
  (left left-row right right-column lower upper)
  (forall
   (value)
   (implies
    (integerp value)
    (equal
     (sac-row-value-count left left-row value lower upper)
     (sac-column-value-count
      right right-column value lower upper)))))

(defun-sk sac-row-to-row-permut-p
  (left right row lower upper)
  (forall
   (value)
   (implies
    (integerp value)
    (equal
     (sac-row-value-count left row value lower upper)
     (sac-row-value-count right row value lower upper)))))

(defun-sk sac-all-column-permutations-p
  (left right column-upper row-upper)
  (forall
   (column)
   (implies
    (and
     (integerp column)
     (<= 0 column)
     (< column column-upper))
    (sac-column-permut-p
     left right column 0 row-upper))))

(defun-sk sac-all-row-to-column-permutations-p
  (left right row-upper entry-upper)
  (forall
   (row)
   (implies
    (and
     (integerp row)
     (<= 0 row)
     (< row row-upper))
    (sac-row-permut-p
     left row right row 0 entry-upper))))

;; Prefix-order predicates are the two loop invariants from the source.

(defun-sk sac-column-prefix-order-p
  (matrix row-upper column-upper)
  (forall
   (i j k)
   (implies
    (and
     (integerp i)
     (integerp j)
     (integerp k)
     (<= 0 i)
     (<= i k)
     (< k row-upper)
     (<= 0 j)
     (< j column-upper))
    (<=
     (sac-elt matrix i j)
     (sac-elt matrix k j)))))

(defun-sk sac-row-prefix-order-p
  (matrix entry-upper row-upper)
  (forall
   (i j k)
   (implies
    (and
     (integerp i)
     (integerp j)
     (integerp k)
     (<= 0 i)
     (<= i k)
     (< k entry-upper)
     (<= 0 j)
     (< j row-upper))
    (<=
     (sac-elt matrix j i)
     (sac-elt matrix j k)))))

(defun-sk sac-column-unchanged-except-p
  (new old selected)
  (forall
   (row column)
   (implies
    (and
     (integerp row)
     (integerp column)
     (<= 0 row)
     (< row (sac-rows new))
     (<= 0 column)
     (< column (sac-columns new))
     (not (equal column selected)))
    (equal
     (sac-elt new row column)
     (sac-elt old row column)))))

(defun-sk sac-row-unchanged-except-p
  (new old selected)
  (forall
   (row column)
   (implies
    (and
     (integerp row)
     (integerp column)
     (<= 0 row)
     (< row (sac-rows new))
     (<= 0 column)
     (< column (sac-columns new))
     (not (equal row selected)))
    (equal
     (sac-elt new row column)
     (sac-elt old row column)))))

(defun-sk sac-selected-column-sorted-p (matrix selected)
  (forall
   (i k)
   (implies
    (and
     (integerp i)
     (integerp k)
     (<= 0 i)
     (<= i k)
     (< k (sac-rows matrix)))
    (<=
     (sac-elt matrix i selected)
     (sac-elt matrix k selected)))))

(defun-sk sac-selected-row-sorted-p (matrix selected)
  (forall
   (j k)
   (implies
    (and
     (integerp j)
     (integerp k)
     (<= 0 j)
     (<= j k)
     (< k (sac-columns matrix)))
    (<=
     (sac-elt matrix selected j)
     (sac-elt matrix selected k)))))

(defun-sk sac-transpose-relation-p (old new)
  (forall
   (i j)
   (implies
    (and
     (integerp i)
     (integerp j)
     (<= 0 i)
     (< i (sac-rows new))
     (<= 0 j)
     (< j (sac-columns new)))
    (equal
     (sac-elt old i j)
     (sac-elt new j i)))))

(defun sac-same-dimensions-p (left right)
  (and
   (equal (sac-rows left) (sac-rows right))
   (equal (sac-columns left) (sac-columns right))))

(defun sac-final-column-contract-p (current original)
  (and
   (sac-all-column-permutations-p
    current original
    (sac-columns current)
    (sac-rows current))
   (sac-column-prefix-order-p
    current
    (sac-rows current)
    (sac-columns current))))

;; Direct branch: each universally quantified post-state of SORT_COLUMN that
;; satisfies its frame, order, and permutation postconditions must establish
;; the next loop invariant.

(defun sac-direct-column-step-post-p
  (after original tid)
  (and
   (sac-all-column-permutations-p
    after original
    (sac-columns after)
    (sac-rows after))
   (sac-column-prefix-order-p
    after
    (sac-rows after)
    (+ tid 1))))

(defun-sk sac-all-direct-column-results-p
  (before original tid)
  (forall
   (after)
   (implies
    (and
     (sac-matrix-p after)
     (sac-same-dimensions-p after before))
    (implies
     (and
      (sac-column-unchanged-except-p after before tid)
      (sac-selected-column-sorted-p after tid)
      (sac-column-permut-p
       after before tid 0 (sac-rows after)))
     (sac-direct-column-step-post-p
      after original tid)))))

(defun sac-direct-loop-premise-p
  (current original tid o2)
  (and
   (integerp tid)
   (<= 0 tid)
   (<= tid o2)
   (sac-all-column-permutations-p
    current original
    (sac-columns current)
    (sac-rows current))
   (sac-column-prefix-order-p
    current
    (sac-rows current)
    tid)))

(defun-sk sac-all-direct-loop-indices-p
  (current original o2)
  (forall
   (tid)
   (implies
    (sac-direct-loop-premise-p
     current original tid o2)
    (and
     (<= 0 tid)
     (< tid (sac-columns current))
     (sac-all-direct-column-results-p
      current original tid)))))

(defun sac-direct-loop-exit-p (current original o2)
  (implies
   (and
    (sac-all-column-permutations-p
     current original
     (sac-columns current)
     (sac-rows current))
    (sac-column-prefix-order-p
     current
     (sac-rows current)
     (+ o2 1)))
   (sac-final-column-contract-p
    current original)))

(defun-sk sac-all-direct-loop-matrices-p (original o2)
  (forall
   (current)
   (implies
    (and
     (sac-matrix-p current)
     (sac-same-dimensions-p current original))
    (and
     (sac-all-direct-loop-indices-p
      current original o2)
     (sac-direct-loop-exit-p
      current original o2)))))

(defun sac-direct-initial-invariant-p (matrix)
  (and
   (sac-all-column-permutations-p
    matrix matrix
    (sac-columns matrix)
    (sac-rows matrix))
   (sac-column-prefix-order-p
    matrix (sac-rows matrix) 0)))

(defun sac-direct-branch-p (matrix)
  (let ((o2 (- (sac-columns matrix) 1)))
    (and
     (implies
      (<= 0 (+ o2 1))
      (and
       (sac-direct-initial-invariant-p matrix)
       (sac-all-direct-loop-matrices-p matrix o2)))
     (implies
      (< (+ o2 1) 0)
      (sac-final-column-contract-p
       matrix matrix)))))

;; Transpose branch: SORT_ROW preserves row permutations relative to the
;; original columns, then the second transpose converts the completed row
;; invariant back to the required column contract.

(defun sac-row-step-post-p (after original n tid)
  (and
   (sac-all-row-to-column-permutations-p
    after original n n)
   (sac-row-prefix-order-p
    after n (+ tid 1))))

(defun-sk sac-all-row-sort-results-p
  (before original n tid)
  (forall
   (after)
   (implies
    (and
     (sac-matrix-p after)
     (sac-same-dimensions-p after before))
    (implies
     (and
      (sac-row-unchanged-except-p after before tid)
      (sac-selected-row-sorted-p after tid)
      (sac-row-to-row-permut-p
       after before tid 0 (sac-columns after)))
     (sac-row-step-post-p
      after original n tid)))))

(defun sac-row-loop-premise-p
  (current original n tid o2)
  (and
   (integerp tid)
   (<= 0 tid)
   (<= tid o2)
   (sac-all-row-to-column-permutations-p
    current original n n)
   (sac-row-prefix-order-p
    current n tid)))

(defun-sk sac-all-row-loop-indices-p
  (current original n o2)
  (forall
   (tid)
   (implies
    (sac-row-loop-premise-p
     current original n tid o2)
    (and
     (<= 0 tid)
     (< tid (sac-rows current))
     (sac-all-row-sort-results-p
      current original n tid)))))

(defun-sk sac-all-final-transposes-p
  (before original)
  (forall
   (after)
   (implies
    (and
     (sac-matrix-p after)
     (sac-same-dimensions-p after before))
    (implies
     (sac-transpose-relation-p before after)
     (sac-final-column-contract-p
      after original)))))

(defun sac-row-loop-exit-p (current original n o2)
  (implies
   (and
    (sac-all-row-to-column-permutations-p
     current original n n)
    (sac-row-prefix-order-p
     current n (+ o2 1)))
   (and
    (equal
     (sac-rows current)
     (sac-columns current))
    (sac-all-final-transposes-p
     current original))))

(defun-sk sac-all-row-loop-matrices-p
  (transposed original n o2)
  (forall
   (current)
   (implies
    (and
     (sac-matrix-p current)
     (sac-same-dimensions-p current transposed))
    (and
     (sac-all-row-loop-indices-p
      current original n o2)
     (sac-row-loop-exit-p
      current original n o2)))))

(defun sac-row-initial-invariant-p
  (transposed original n)
  (and
   (sac-all-row-to-column-permutations-p
    transposed original n n)
   (sac-row-prefix-order-p
    transposed n 0)))

(defun sac-transposed-loop-p
  (transposed original n)
  (let ((o2 (- (sac-columns transposed) 1)))
    (and
     (implies
      (<= 0 (+ o2 1))
      (and
       (sac-row-initial-invariant-p
        transposed original n)
       (sac-all-row-loop-matrices-p
        transposed original n o2)))
     (implies
      (< (+ o2 1) 0)
      (and
       (equal
        (sac-rows transposed)
        (sac-columns transposed))
       (sac-all-final-transposes-p
        transposed original))))))

(defun-sk sac-all-first-transposes-p (original n)
  (forall
   (transposed)
   (implies
    (and
     (sac-matrix-p transposed)
     (sac-same-dimensions-p transposed original))
    (implies
     (sac-transpose-relation-p
      original transposed)
     (sac-transposed-loop-p
      transposed original n)))))

(defun sac-transpose-branch-p (matrix)
  (let ((n (sac-rows matrix)))
    (and
     (equal
      (sac-rows matrix)
      (sac-columns matrix))
     (sac-all-first-transposes-p
      matrix n))))

;; The source nondeterministic Boolean supplies an existential result and then
;; requires the appropriate branch for every Boolean satisfying its ensures
;; clause.  Both quantifier scopes are retained explicitly.

(defun-sk sac-choice-exists-p (matrix)
  (exists
   (result)
   (and
    (or (equal result t) (equal result nil))
    (or
     (equal result t)
     (equal
      (sac-rows matrix)
      (sac-columns matrix))))))

(defun-sk sac-all-choice-results-p (matrix)
  (forall
   (choice)
   (implies
    (or (equal choice t) (equal choice nil))
    (implies
     (or
      (equal choice t)
      (equal
       (sac-rows matrix)
       (sac-columns matrix)))
     (if (equal choice t)
         (sac-direct-branch-p matrix)
       (sac-transpose-branch-p matrix))))))

(defun
    ntp4vc-pearl-verifythis-2021-shearsort-shearsort-sort-all-columnsqtvc-statement
    (matrix)
  (implies
   (sac-matrix-p matrix)
   (and
    (sac-choice-exists-p matrix)
    (sac-all-choice-results-p matrix))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
