;; Statement-only formalization of PutnamBench corpus artifact putnam_2005_a2:
;; the number of rook tours through every point of an n by 3 integer grid,
;; starting at (1,1) and ending at (n,1), is 0 for n=1 and 2^(n-2) otherwise.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source represents a tour by a total function on the naturals, with
;; value (0,0) at index 0 and at every index above 3*n. Its values at indices
;; 1 through 3*n contain every grid point exactly once. Consequently, taking
;; that finite prefix is a bijection from the source functions to the paths
;; counted below; conversely every counted path has a unique total extension
;; with the required zero values. This finite list is therefore an exact
;; encoding of the source function set, not a restriction to finite tables.

(defun putnam-2005-a2-grid-point-p (point n)
  (and
   (consp point)
   (integerp (car point))
   (integerp (cdr point))
   (<= 1 (car point))
   (<= (car point) n)
   (<= 1 (cdr point))
   (<= (cdr point) 3)))

;; REMAINING is the number of still-unfilled path positions. Each recursive
;; branch chooses one of the four unit-distance neighbors that lies in the
;; grid and has not occurred earlier in the path. Starting with 3*n-1
;; remaining positions forces the final path to contain all 3*n grid points
;; exactly once.
(defun putnam-2005-a2-count-from
    (n current visited remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (if (equal current (cons n 1)) 1 0)
    (let* ((row (car current))
           (column (cdr current))
           (right (cons (+ row 1) column))
           (left (cons (- row 1) column))
           (up (cons row (+ column 1)))
           (down (cons row (- column 1))))
      (+
       (if (and
            (putnam-2005-a2-grid-point-p right n)
            (not (member-equal right visited)))
           (putnam-2005-a2-count-from
            n right (cons right visited) (- remaining 1))
         0)
       (if (and
            (putnam-2005-a2-grid-point-p left n)
            (not (member-equal left visited)))
           (putnam-2005-a2-count-from
            n left (cons left visited) (- remaining 1))
         0)
       (if (and
            (putnam-2005-a2-grid-point-p up n)
            (not (member-equal up visited)))
           (putnam-2005-a2-count-from
            n up (cons up visited) (- remaining 1))
         0)
       (if (and
            (putnam-2005-a2-grid-point-p down n)
            (not (member-equal down visited)))
           (putnam-2005-a2-count-from
            n down (cons down visited) (- remaining 1))
         0)))))

(defun putnam-2005-a2-rook-tour-count (n)
  (if (and (natp n) (< 0 n))
      (let ((start (cons 1 1)))
        (putnam-2005-a2-count-from
         n start (list start) (- (* 3 n) 1)))
    0))

(defun putnam-2005-a2-solution (n)
  (if (equal n 1)
      0
    (expt 2 (nfix (- n 2)))))

(defun putnambench-putnam-2005-a2-statement (n)
  (implies
   (and (natp n) (< 0 n))
   (equal
    (putnam-2005-a2-rook-tour-count n)
    (putnam-2005-a2-solution n))))

(value-triple :itpeval-statement-checked)
:q
