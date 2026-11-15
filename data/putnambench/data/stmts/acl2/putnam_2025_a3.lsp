;; Statement-only formalization of PutnamBench corpus artifact putnam_2025_a3:
;; Alice has no winning strategy in the non-repeating ternary-string game for
;; any positive string length. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A natural below 3^n is the base-3 code of exactly one function
;; Fin n -> Fin 3. Position zero is the least significant ternary digit.

(defun putnam-2025-a3-digit (code position)
  (mod (floor (nfix code)
              (expt 3 (nfix position)))
       3))

;; DIFF-SEEN records whether the unique changed position has already occurred.

(defun putnam-2025-a3-valid-move-scan-p
    (left right position positions-left diff-seen)
  (declare (xargs :measure (nfix positions-left)))
  (if (zp positions-left)
      diff-seen
    (let ((left-digit
           (putnam-2025-a3-digit left position))
          (right-digit
           (putnam-2025-a3-digit right position)))
      (if (equal left-digit right-digit)
          (putnam-2025-a3-valid-move-scan-p
           left
           right
           (+ position 1)
           (- positions-left 1)
           diff-seen)
        (and
         (not diff-seen)
         (or (equal (+ left-digit 1) right-digit)
             (equal (+ right-digit 1) left-digit))
         (putnam-2025-a3-valid-move-scan-p
          left
          right
          (+ position 1)
          (- positions-left 1)
          t))))))

(defun putnam-2025-a3-valid-move-p (n state-count left right)
  (and
   (natp n)
   (natp left)
   (natp right)
   (< left state-count)
   (< right state-count)
   (putnam-2025-a3-valid-move-scan-p
    left right 0 n nil)))

;; HISTORY lists, newest first, the states played after the initial all-zero
;; string. Generated histories are therefore in bijection with the source's
;; valid plays.

(defun putnam-2025-a3-legal-next-p
    (n state-count history candidate)
  (and
   (natp candidate)
   (< candidate state-count)
   (not (member-equal candidate (cons 0 history)))
   (putnam-2025-a3-valid-move-p
    n
    state-count
    (if (consp history) (car history) 0)
    candidate)))

;; A :VALUE call enters a HasWinningStrategy node. A :OUR-SCAN call searches
;; existentially for the constructor's move s. An :OPP-SCAN call checks
;; universally every legal reply s'. Decreasing MOVES-LEFT corresponds to
;; adding a fresh state; within a scan, CANDIDATES-LEFT decreases.

(defun putnam-2025-a3-search-measure
    (state-count moves-left phase candidates-left)
  (make-ord
   1
   (+ 1 (nfix moves-left))
   (if (equal phase :value)
       (+ 1 (nfix state-count))
     (nfix candidates-left))))

(defun putnam-2025-a3-has-winning-strategy-search-p
    (n state-count history moves-left phase candidates-left)
  (declare
   (xargs
    :measure
    (putnam-2025-a3-search-measure
     state-count moves-left phase candidates-left)
    :well-founded-relation o<))
  (cond
   ((equal phase :value)
    (if (zp moves-left)
        nil
      (putnam-2025-a3-has-winning-strategy-search-p
       n
       state-count
       history
       moves-left
       :our-scan
       state-count)))
   ((zp moves-left)
    (equal phase :opp-scan))
   ((zp candidates-left)
    (equal phase :opp-scan))
   ((equal phase :our-scan)
    (let ((candidate (- candidates-left 1)))
      (if
       (and
        (putnam-2025-a3-legal-next-p
         n state-count history candidate)
        (putnam-2025-a3-has-winning-strategy-search-p
         n
         state-count
         (cons candidate history)
         (- moves-left 1)
         :opp-scan
         state-count))
       t
        (putnam-2025-a3-has-winning-strategy-search-p
         n
         state-count
         history
         moves-left
         :our-scan
         (- candidates-left 1)))))
   ((equal phase :opp-scan)
    (let ((candidate (- candidates-left 1)))
      (if
       (and
        (putnam-2025-a3-legal-next-p
         n state-count history candidate)
        (not
         (putnam-2025-a3-has-winning-strategy-search-p
          n
          state-count
          (cons candidate history)
          (- moves-left 1)
          :value
          0)))
       nil
        (putnam-2025-a3-has-winning-strategy-search-p
         n
         state-count
         history
         moves-left
         :opp-scan
         (- candidates-left 1)))))
   (t nil)))

(defun putnam-2025-a3-alice-has-winning-strategy-p (n)
  (let ((state-count (expt 3 (nfix n))))
    (putnam-2025-a3-has-winning-strategy-search-p
     n
     state-count
     nil
     (- state-count 1)
     :value
     0)))

;; The ground-truth solution predicate is False. Keeping it as a separate
;; definition preserves the source theorem's stated biconditional.

(defun putnam-2025-a3-solution-p (n)
  (declare (ignore n))
  nil)

(defun putnambench-putnam-2025-a3-statement (n)
  (implies
   (and (natp n)
        (<= 1 n))
   (equal
    (putnam-2025-a3-solution-p n)
    (putnam-2025-a3-alice-has-winning-strategy-p n))))

(value-triple :itpeval-statement-checked)
:q
