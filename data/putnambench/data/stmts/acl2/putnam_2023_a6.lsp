;; Statement-only formalization of PutnamBench corpus artifact putnam_2023_a6:
;; Bob has a winning parity strategy in the alternating permutation game for
;; every positive number of available integers. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The remaining integers are represented by their exact finite list. At an
;; Alice node every legal choice must preserve Bob's win; at a Bob node one
;; legal choice suffices. Thus backward induction is equivalent in both
;; directions to an existential Bob strategy followed by universal
;; quantification over all conforming valid games. The parity goal is selected
;; outside the game-tree search, so Bob chooses it before Alice's first move.

(defun putnam-2023-a6-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     start
     (putnam-2023-a6-range-from
      (+ start 1) (- count 1)))))

(defun putnam-2023-a6-remove-first (value values)
  (if (endp values)
      nil
    (if (equal value (car values))
        (cdr values)
      (cons
       (car values)
       (putnam-2023-a6-remove-first
        value (cdr values))))))

;; A :VALUE call starts a node, while a :SCAN call aggregates its legal
;; children. The lexicographic measure first counts moves left and then
;; distinguishes node entry from the number of unscanned choices.

(defun putnam-2023-a6-search-measure
    (moves-left phase choices-left)
  (make-ord
   1
   (+ 1 (nfix moves-left))
   (if (equal phase :value)
       (+ 1 (nfix moves-left))
     (nfix choices-left))))

(defun putnam-2023-a6-bob-wins-search
    (remaining moves-left turn fixed-points goal
               phase choices choices-left aggregate)
  (declare
   (xargs
    :measure
    (putnam-2023-a6-search-measure
     moves-left phase choices-left)
    :well-founded-relation o<))
  (cond
   ((equal phase :value)
    (if (or (zp moves-left)
            (endp remaining))
        (equal (mod fixed-points 2) goal)
      (putnam-2023-a6-bob-wins-search
       remaining
       moves-left
       turn
       fixed-points
       goal
       :scan
       remaining
       moves-left
       (if (evenp turn) t nil))))
   ((or (zp moves-left)
        (zp choices-left)
        (endp choices))
    aggregate)
   (t
    (let* ((choice (car choices))
           (next-fixed-points
            (+ fixed-points
               (if (equal choice (+ turn 1)) 1 0)))
           (child-win
            (putnam-2023-a6-bob-wins-search
             (putnam-2023-a6-remove-first
              choice remaining)
             (- moves-left 1)
             (+ turn 1)
             next-fixed-points
             goal
             :value
             nil
             0
             nil))
           (next-aggregate
            (if (evenp turn)
                (and aggregate child-win)
              (or aggregate child-win))))
      (putnam-2023-a6-bob-wins-search
       remaining
       moves-left
       turn
       fixed-points
       goal
       :scan
       (cdr choices)
       (- choices-left 1)
       next-aggregate)))))

(defun putnam-2023-a6-bob-has-winning-strategy-p (n)
  (let ((available
         (putnam-2023-a6-range-from 1 n)))
    (or
     (putnam-2023-a6-bob-wins-search
      available n 0 0 0 :value nil 0 nil)
     (putnam-2023-a6-bob-wins-search
      available n 0 0 1 :value nil 0 nil))))

;; Universal closure of N gives the pointwise form of the source set equality.

(defun putnambench-putnam-2023-a6-statement (n)
  (implies
   (natp n)
   (equal
    (and
     (< 0 n)
     (putnam-2023-a6-bob-has-winning-strategy-p n))
    (< 0 n))))

(value-triple :itpeval-statement-checked)
:q
