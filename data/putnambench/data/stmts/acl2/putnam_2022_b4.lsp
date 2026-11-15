;; Statement-only formalization of PutnamBench corpus artifact putnam_2022_b4:
;; the natural lengths admitting a cyclic sequence of distinct real numbers
;; whose consecutive triples are three-term arithmetic progressions are
;; exactly the multiples of 3 that are at least 9. This file contains no proof.
;;
;; Only the first n values of the source function occur, so an n-vector is
;; extensionally equivalent to that finite restriction and every such vector
;; extends to a function on the naturals. For a vector with distinct entries,
;; a triple is an arithmetic progression in increasing order exactly when one
;; of its three entries is the midpoint of the other two. The 3^n midpoint
;; choices therefore give homogeneous linear systems with integer
;; coefficients.
;;
;; For one such system, its real nullspace contains a vector with all
;; coordinates distinct exactly when it is not contained in any hyperplane
;; x_i = x_j: a finite union of proper subspaces cannot cover a vector space
;; over the infinite field of reals. Containment in x_i = x_j holds exactly
;; when adjoining that equation does not increase matrix rank. Since a
;; rational matrix has the same rank over the rationals and the reals, the
;; exact rational row-rank computation below decides the original real
;; existential bidirectionally; it does not restrict the witnesses to
;; rational sequences.

(in-package "ACL2")

(defun putnam-2022-b4-midpoint-index (i n choice)
  (mod (+ (nfix i) (nfix choice)) (nfix n)))

(defun putnam-2022-b4-row-entry (column i n choice)
  (let* ((middle
          (putnam-2022-b4-midpoint-index i n choice))
         (first-other
          (putnam-2022-b4-midpoint-index
           i n (mod (+ (nfix choice) 1) 3)))
         (second-other
          (putnam-2022-b4-midpoint-index
           i n (mod (+ (nfix choice) 2) 3))))
    (+ (if (equal column middle) 2 0)
       (if (equal column first-other) -1 0)
       (if (equal column second-other) -1 0))))

(defun putnam-2022-b4-build-row-aux
    (remaining column i n choice)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (putnam-2022-b4-row-entry column i n choice)
     (putnam-2022-b4-build-row-aux
      (- remaining 1) (+ column 1) i n choice))))

(defun putnam-2022-b4-build-row (i n choice)
  (putnam-2022-b4-build-row-aux n 0 i n choice))

(defun putnam-2022-b4-build-system-aux
    (remaining i n choices-code)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (putnam-2022-b4-build-row
      i n (mod (nfix choices-code) 3))
     (putnam-2022-b4-build-system-aux
      (- remaining 1)
      (+ i 1)
      n
      (floor (nfix choices-code) 3)))))

(defun putnam-2022-b4-build-system (n choices-code)
  (putnam-2022-b4-build-system-aux
   n 0 n choices-code))

(defun putnam-2022-b4-find-pivot (rows column)
  (if (consp rows)
      (if (equal (nth (nfix column) (car rows)) 0)
          (putnam-2022-b4-find-pivot (cdr rows) column)
        (car rows))
    nil))

(defun putnam-2022-b4-remove-first-row (row rows)
  (if (consp rows)
      (if (equal row (car rows))
          (cdr rows)
        (cons
         (car rows)
         (putnam-2022-b4-remove-first-row
          row (cdr rows))))
    nil))

(defun putnam-2022-b4-row-combination
    (left-scale left right-scale right)
  (if (and (consp left) (consp right))
      (cons
       (+ (* left-scale (car left))
          (* right-scale (car right)))
       (putnam-2022-b4-row-combination
        left-scale
        (cdr left)
        right-scale
        (cdr right)))
    nil))

(defun putnam-2022-b4-eliminate-column
    (rows pivot column)
  (if (consp rows)
      (let ((coefficient
             (nth (nfix column) (car rows)))
            (pivot-coefficient
             (nth (nfix column) pivot)))
        (cons
         (if (equal coefficient 0)
             (car rows)
           (putnam-2022-b4-row-combination
            pivot-coefficient
            (car rows)
            (- coefficient)
            pivot))
         (putnam-2022-b4-eliminate-column
          (cdr rows) pivot column)))
    nil))

(defun putnam-2022-b4-rank-aux
    (rows column columns-left)
  (declare (xargs :measure (nfix columns-left)))
  (if (zp columns-left)
      0
    (let ((pivot
           (putnam-2022-b4-find-pivot rows column)))
      (if (consp pivot)
          (+ 1
             (putnam-2022-b4-rank-aux
              (putnam-2022-b4-eliminate-column
               (putnam-2022-b4-remove-first-row
                pivot rows)
               pivot
               column)
              (+ column 1)
              (- columns-left 1)))
        (putnam-2022-b4-rank-aux
         rows (+ column 1) (- columns-left 1))))))

(defun putnam-2022-b4-rank (rows n)
  (putnam-2022-b4-rank-aux rows 0 n))

(defun putnam-2022-b4-difference-row-aux
    (remaining column left right)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (+ (if (equal column left) 1 0)
        (if (equal column right) -1 0))
     (putnam-2022-b4-difference-row-aux
      (- remaining 1)
      (+ column 1)
      left
      right))))

(defun putnam-2022-b4-difference-row (n left right)
  (putnam-2022-b4-difference-row-aux
   n 0 left right))

(defun putnam-2022-b4-separates-p
    (rows n left right base-rank)
  (< base-rank
     (putnam-2022-b4-rank
      (cons
       (putnam-2022-b4-difference-row
        n left right)
       rows)
      n)))

(defun putnam-2022-b4-all-pairs-separable-aux
    (rows n base-rank pair-code pairs-left)
  (declare (xargs :measure (nfix pairs-left)))
  (if (zp pairs-left)
      t
    (let ((left (floor (nfix pair-code) (nfix n)))
          (right (mod (nfix pair-code) (nfix n))))
      (and
       (or
        (not (< left right))
        (putnam-2022-b4-separates-p
         rows n left right base-rank))
       (putnam-2022-b4-all-pairs-separable-aux
        rows
        n
        base-rank
        (+ pair-code 1)
        (- pairs-left 1))))))

(defun putnam-2022-b4-all-pairs-separable-p (rows n)
  (putnam-2022-b4-all-pairs-separable-aux
   rows
   n
   (putnam-2022-b4-rank rows n)
   0
   (* (nfix n) (nfix n))))

(defun putnam-2022-b4-midpoint-choice-works-p
    (n choices-code)
  (putnam-2022-b4-all-pairs-separable-p
   (putnam-2022-b4-build-system n choices-code)
   n))

(defun putnam-2022-b4-exists-choice-aux
    (n choices-code choices-left)
  (declare (xargs :measure (nfix choices-left)))
  (if (zp choices-left)
      nil
    (or
     (putnam-2022-b4-midpoint-choice-works-p
      n choices-code)
     (putnam-2022-b4-exists-choice-aux
      n
      (+ choices-code 1)
      (- choices-left 1)))))

(defun putnam-2022-b4-cyclic-progression-exists-p (n)
  (putnam-2022-b4-exists-choice-aux
   n 0 (expt 3 (nfix n))))

(defun putnambench-putnam-2022-b4-statement (n)
  (implies
   (natp n)
   (iff
    (and
     (<= 4 n)
     (putnam-2022-b4-cyclic-progression-exists-p n))
    (and
     (<= 9 n)
     (equal (mod n 3) 0)))))

(value-triple :itpeval-statement-checked)
:q
