;; Statement-only formalization of PutnamBench corpus artifact putnam_2004_a5:
;; the total number of monochromatic connected regions over all two-colorings
;; of a nonempty finite rectangular checkerboard exceeds 2^(mn) times mn/8.
;; This file contains no proof.

(in-package "ACL2")

;; Row-major positions 0,...,M*N-1 identify the squares of the board.  A
;; coloring is its unique M*N-bit natural number, so the exhaustive sum below
;; ranges bijectively over every function Fin M x Fin N -> {red, black}.

(defun putnam-2004-a5-bit-set-p (code position)
  (equal (mod (floor code (expt 2 position)) 2)
         1))

(defun putnam-2004-a5-adjacent-p
    (left right columns cell-count)
  (and (natp left)
       (natp right)
       (posp columns)
       (< left cell-count)
       (< right cell-count)
       (let ((left-row (floor left columns))
             (left-column (mod left columns))
             (right-row (floor right columns))
             (right-column (mod right columns)))
         (or (and (equal left-row right-row)
                  (equal (abs (- left-column right-column)) 1))
             (and (equal left-column right-column)
                  (equal (abs (- left-row right-row)) 1))))))

(defun putnam-2004-a5-same-color-p
    (coloring left right)
  (equal (putnam-2004-a5-bit-set-p coloring left)
         (putnam-2004-a5-bit-set-p coloring right)))

;; This is the existential test for an already reached same-color neighbor.

(defun putnam-2004-a5-has-reached-neighbor-p
    (cell neighbor-count columns cell-count coloring reached)
  (declare (xargs :measure (nfix neighbor-count)))
  (if (zp neighbor-count)
      nil
    (let ((neighbor (- neighbor-count 1)))
      (or (and (putnam-2004-a5-bit-set-p reached neighbor)
               (putnam-2004-a5-adjacent-p
                cell neighbor columns cell-count)
               (putnam-2004-a5-same-color-p
                coloring cell neighbor))
          (putnam-2004-a5-has-reached-neighbor-p
           cell neighbor columns cell-count coloring reached)))))

;; One closure round adds exactly the squares at monochromatic graph distance
;; one from REACHED.  Membership tests use the old set REACHED throughout the
;; round, while RESULT accumulates the newly added bits.

(defun putnam-2004-a5-expand-region-scan
    (remaining columns cell-count coloring reached result)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      result
    (let ((cell (- remaining 1)))
      (putnam-2004-a5-expand-region-scan
       cell
       columns
       cell-count
       coloring
       reached
       (if (or (putnam-2004-a5-bit-set-p reached cell)
               (putnam-2004-a5-has-reached-neighbor-p
                cell cell-count columns cell-count coloring reached))
           (if (putnam-2004-a5-bit-set-p result cell)
               result
             (+ result (expt 2 cell)))
         result)))))

(defun putnam-2004-a5-expand-region
    (columns cell-count coloring reached)
  (putnam-2004-a5-expand-region-scan
   cell-count columns cell-count coloring reached reached))

;; Every simple path in a graph with CELL-COUNT vertices has fewer than
;; CELL-COUNT edges, so CELL-COUNT rounds give the exact connected component.

(defun putnam-2004-a5-region-closure
    (rounds columns cell-count coloring reached)
  (declare (xargs :measure (nfix rounds)))
  (if (zp rounds)
      reached
    (putnam-2004-a5-region-closure
     (- rounds 1)
     columns
     cell-count
     coloring
     (putnam-2004-a5-expand-region
      columns cell-count coloring reached))))

(defun putnam-2004-a5-connected-p
    (start target columns cell-count coloring)
  (and (natp start)
       (natp target)
       (< start cell-count)
       (< target cell-count)
       (putnam-2004-a5-bit-set-p
        (putnam-2004-a5-region-closure
         cell-count
         columns
         cell-count
         coloring
         (expt 2 start))
        target)))

;; A square represents a region precisely when no smaller row-major square is
;; connected to it.  Thus exactly one square is counted per connected region.

(defun putnam-2004-a5-connected-to-earlier-p
    (cell earlier-count columns cell-count coloring)
  (declare (xargs :measure (nfix earlier-count)))
  (if (zp earlier-count)
      nil
    (let ((earlier (- earlier-count 1)))
      (or (putnam-2004-a5-connected-p
           earlier cell columns cell-count coloring)
          (putnam-2004-a5-connected-to-earlier-p
           cell earlier columns cell-count coloring)))))

(defun putnam-2004-a5-region-count-through
    (remaining columns cell-count coloring)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let ((cell (- remaining 1)))
      (+ (if (putnam-2004-a5-connected-to-earlier-p
              cell cell columns cell-count coloring)
             0
           1)
         (putnam-2004-a5-region-count-through
          cell columns cell-count coloring)))))

(defun putnam-2004-a5-region-count
    (columns cell-count coloring)
  (putnam-2004-a5-region-count-through
   cell-count columns cell-count coloring))

(defun putnam-2004-a5-total-region-count
    (coloring-count columns cell-count)
  (declare (xargs :measure (nfix coloring-count)))
  (if (zp coloring-count)
      0
    (let ((coloring (- coloring-count 1)))
      (+ (putnam-2004-a5-region-count
          columns cell-count coloring)
         (putnam-2004-a5-total-region-count
          coloring columns cell-count)))))

(defun putnambench-putnam-2004-a5-statement (m n)
  (implies
   (and (natp m)
        (natp n)
        (< 0 (* m n)))
   (let* ((cell-count (* m n))
          (coloring-count (expt 2 cell-count)))
     (> (putnam-2004-a5-total-region-count
         coloring-count n cell-count)
        (* coloring-count (/ cell-count 8))))))

(value-triple :itpeval-statement-checked)
:q
