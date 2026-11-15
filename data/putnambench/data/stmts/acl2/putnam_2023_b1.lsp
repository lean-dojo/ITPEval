;; Statement-only formalization of PutnamBench corpus artifact putnam_2023_b1:
;; the number of coin configurations reachable by diagonal legal moves on an
;; m-by-n grid is choose(m+n-2,m-1). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The problem text and Lean source existentially bind the finite legal
;; sequence. The free SEQ in the Isabelle set comprehension is read as the
;; corresponding omitted existential binder; the fixed-sequence reading would
;; count at most one configuration and does not express the stated problem.
;;
;; A board bitmask is in bijection with the total Boolean configurations that
;; can be reached from INITCOINS. Initially every coordinate outside the finite
;; m-by-n grid is false, and each legal move changes only two coordinates
;; inside that grid, so every reachable total function remains false outside
;; the grid. Bit (i*n+j) records the value at (i,j).
;;
;; MOVE-AT is the full source successor, not a weakened move relation:
;; LEGAL-AT-P requires the source coin and the three empty neighboring cells;
;; subtracting the source bit and adding the diagonal bit makes the first
;; three target cells empty and the diagonal target cell occupied. Every other
;; bit is unchanged, which is exactly the source's universal frame condition.

(defun putnam-2023-b1-insert-board (board boards)
  (if (member-equal board boards)
      boards
    (cons board boards)))

(defun putnam-2023-b1-initial-board-aux
    (n columns index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let* ((row (floor (nfix index) (nfix columns)))
           (column (mod (nfix index) (nfix columns)))
           (bit (+ (* row (nfix n)) column)))
      (+ (expt 2 bit)
         (putnam-2023-b1-initial-board-aux
          n columns (+ 1 (nfix index)) (- remaining 1))))))

(defun putnam-2023-b1-initial-board (m n)
  (let ((rows (nfix (- (nfix m) 1)))
        (columns (nfix (- (nfix n) 1))))
    (if (or (zp rows) (zp columns))
        0
      (putnam-2023-b1-initial-board-aux
       n columns 0 (* rows columns)))))

(defun putnam-2023-b1-bit-index (n row column)
  (+ (* (nfix row) (nfix n))
     (nfix column)))

(defun putnam-2023-b1-occupied-p (board n row column)
  (and (natp board)
       (logbitp
        (putnam-2023-b1-bit-index n row column)
        board)))

(defun putnam-2023-b1-legal-at-p (board m n row column)
  (and
   (natp board)
   (natp m)
   (natp n)
   (natp row)
   (natp column)
   (< row (- m 1))
   (< column (- n 1))
   (putnam-2023-b1-occupied-p board n row column)
   (not
    (putnam-2023-b1-occupied-p
     board n (+ row 1) column))
   (not
    (putnam-2023-b1-occupied-p
     board n row (+ column 1)))
   (not
    (putnam-2023-b1-occupied-p
     board n (+ row 1) (+ column 1)))))

(defun putnam-2023-b1-move-at (board n row column)
  (+ (- (nfix board)
        (expt
         2
         (putnam-2023-b1-bit-index n row column)))
     (expt
      2
      (putnam-2023-b1-bit-index
       n (+ row 1) (+ column 1)))))

(defun putnam-2023-b1-collect-moves
    (board m n columns index remaining boards)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      boards
    (let* ((row (floor (nfix index) (nfix columns)))
           (column (mod (nfix index) (nfix columns)))
           (next-boards
            (if (putnam-2023-b1-legal-at-p
                 board m n row column)
                (putnam-2023-b1-insert-board
                 (putnam-2023-b1-move-at
                  board n row column)
                 boards)
              boards)))
      (putnam-2023-b1-collect-moves
       board
       m
       n
       columns
       (+ 1 (nfix index))
       (- remaining 1)
       next-boards))))

(defun putnam-2023-b1-successors (board m n boards)
  (let ((rows (nfix (- (nfix m) 1)))
        (columns (nfix (- (nfix n) 1))))
    (if (or (zp rows) (zp columns))
        boards
      (putnam-2023-b1-collect-moves
       board m n columns 0 (* rows columns) boards))))

(defun putnam-2023-b1-expand (frontier m n boards)
  (if (consp frontier)
      (putnam-2023-b1-expand
       (cdr frontier)
       m
       n
       (putnam-2023-b1-successors
        (car frontier) m n boards))
    boards))

;; There are at most 2^(m*n) boards. Any reachable board has a simple legal
;; path with fewer vertices than this, so this finite closure is equivalent in
;; both directions to existence of an arbitrary finite legal sequence.
(defun putnam-2023-b1-reachable-closure
    (boards m n fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      boards
    (let ((expanded
           (putnam-2023-b1-expand boards m n boards)))
      (if (equal expanded boards)
          boards
        (putnam-2023-b1-reachable-closure
         expanded m n (- fuel 1))))))

(defun putnam-2023-b1-configuration-limit (m n)
  (expt 2 (* (nfix m) (nfix n))))

(defun putnam-2023-b1-reachable-count (m n)
  (len
   (putnam-2023-b1-reachable-closure
    (list (putnam-2023-b1-initial-board m n))
    m
    n
    (putnam-2023-b1-configuration-limit m n))))

(defun putnam-2023-b1-choose (total selected)
  (declare (xargs :measure (nfix total)))
  (cond
   ((zp selected) 1)
   ((zp total) 0)
   (t
    (+ (putnam-2023-b1-choose
        (- total 1) (- selected 1))
       (putnam-2023-b1-choose
        (- total 1) selected)))))

(defun putnambench-putnam-2023-b1-statement (m n)
  (implies
   (and
    (natp m)
    (natp n)
    (< 1 m)
    (< 1 n))
   (equal
    (putnam-2023-b1-reachable-count m n)
    (putnam-2023-b1-choose
     (- (+ m n) 2)
     (- m 1)))))

(value-triple :itpeval-statement-checked)
:q
