;; Statement-only formalization of PutnamBench corpus artifact putnam_2001_b1:
;; balanced two-colorings of a row-major numbered even square grid have equal
;; sums of the labels in the two color classes. This file contains no proof.

(in-package "ACL2")

;; COLORS is an exact n-by-n list representation of the source function on
;; Fin n x Fin n. Each entry is 0 or 1. The source function NUMS is uniquely
;; fixed by its hypothesis, so the weighted sums use row*n+column+1 directly.
;; For n bit entries with even n, sum n/2 equivalently says that both colors
;; occur n/2 times, matching the two ground-truth balance formulations.

(defun putnam-2001-b1-bit-row-p (row remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (endp row)
    (and
     (consp row)
     (or (equal (car row) 0)
         (equal (car row) 1))
     (putnam-2001-b1-bit-row-p
      (cdr row) (- remaining 1)))))

(defun putnam-2001-b1-grid-p (colors n remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (endp colors)
    (and
     (consp colors)
     (putnam-2001-b1-bit-row-p (car colors) n)
     (putnam-2001-b1-grid-p
      (cdr colors) n (- remaining 1)))))

(defun putnam-2001-b1-row-sum (row)
  (if (endp row)
      0
    (+ (car row)
       (putnam-2001-b1-row-sum (cdr row)))))

(defun putnam-2001-b1-rows-balanced-p (colors half)
  (if (endp colors)
      t
    (and
     (equal (putnam-2001-b1-row-sum (car colors))
            half)
     (putnam-2001-b1-rows-balanced-p
      (cdr colors) half))))

(defun putnam-2001-b1-column-sum (colors column)
  (if (endp colors)
      0
    (+ (nth column (car colors))
       (putnam-2001-b1-column-sum
        (cdr colors) column))))

(defun putnam-2001-b1-columns-balanced-p
    (colors column remaining half)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (equal (putnam-2001-b1-column-sum colors column)
            half)
     (putnam-2001-b1-columns-balanced-p
      colors (+ column 1) (- remaining 1) half))))

(defun putnam-2001-b1-weighted-row-sum
    (row row-index column-index n color)
  (if (endp row)
      0
    (+ (if (equal (car row) color)
           (+ (* row-index n) column-index 1)
         0)
       (putnam-2001-b1-weighted-row-sum
        (cdr row) row-index (+ column-index 1) n color))))

(defun putnam-2001-b1-weighted-grid-sum
    (colors row-index n color)
  (if (endp colors)
      0
    (+ (putnam-2001-b1-weighted-row-sum
        (car colors) row-index 0 n color)
       (putnam-2001-b1-weighted-grid-sum
        (cdr colors) (+ row-index 1) n color))))

(defun putnambench-putnam-2001-b1-statement (n colors)
  (implies
   (and
    (posp n)
    (evenp n)
    (putnam-2001-b1-grid-p colors n n)
    (putnam-2001-b1-rows-balanced-p colors (/ n 2))
    (putnam-2001-b1-columns-balanced-p
     colors 0 n (/ n 2)))
   (equal
    (putnam-2001-b1-weighted-grid-sum colors 0 n 0)
    (putnam-2001-b1-weighted-grid-sum colors 0 n 1))))

(value-triple :itpeval-statement-checked)
:q
