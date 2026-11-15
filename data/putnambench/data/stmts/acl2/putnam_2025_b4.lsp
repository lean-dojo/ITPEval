;; Statement-only formalization of PutnamBench corpus artifact putnam_2025_b4:
;; an upper bound on the sum of an n by n nonnegative integer matrix whose
;; entry in one-based row i and column j is zero whenever i+j <= n and whose
;; entries increase by zero or one along rows and columns. This file contains
;; no proof.

(in-package "ACL2")

;; An exact-length list of exact-length natural-number rows is the extensional
;; representation of the source matrix on Fin (m+2). The recursive predicates
;; below range over every valid row and column index in canonical order.

(defun putnam-2025-b4-natural-row-p (row columns)
  (declare (xargs :measure (nfix columns)))
  (if (zp columns)
      (equal row nil)
    (and
     (consp row)
     (natp (car row))
     (putnam-2025-b4-natural-row-p
      (cdr row) (- columns 1)))))

(defun putnam-2025-b4-natural-matrix-p
    (matrix rows columns)
  (declare (xargs :measure (nfix rows)))
  (if (zp rows)
      (equal matrix nil)
    (and
     (consp matrix)
     (putnam-2025-b4-natural-row-p
      (car matrix) columns)
     (putnam-2025-b4-natural-matrix-p
      (cdr matrix) (- rows 1) columns))))

(defun putnam-2025-b4-zero-region-row-p
    (row row-index column-index m)
  (if (endp row)
      t
    (and
     (implies
      (<= (+ row-index column-index) m)
      (equal (car row) 0))
     (putnam-2025-b4-zero-region-row-p
      (cdr row) row-index (+ column-index 1) m))))

(defun putnam-2025-b4-zero-region-p
    (matrix row-index m)
  (if (endp matrix)
      t
    (and
     (putnam-2025-b4-zero-region-row-p
      (car matrix) row-index 0 m)
     (putnam-2025-b4-zero-region-p
      (cdr matrix) (+ row-index 1) m))))

(defun putnam-2025-b4-adjacent-rows-p (upper lower)
  (if (endp upper)
      (endp lower)
    (and
     (consp lower)
     (or
      (equal (car lower) (car upper))
      (equal (car lower) (+ (car upper) 1)))
     (putnam-2025-b4-adjacent-rows-p
      (cdr upper) (cdr lower)))))

(defun putnam-2025-b4-vertical-steps-p (matrix)
  (if (or (endp matrix)
          (endp (cdr matrix)))
      t
    (and
     (putnam-2025-b4-adjacent-rows-p
      (car matrix) (cadr matrix))
     (putnam-2025-b4-vertical-steps-p
      (cdr matrix)))))

(defun putnam-2025-b4-horizontal-row-p (row)
  (if (or (endp row)
          (endp (cdr row)))
      t
    (and
     (or
      (equal (cadr row) (car row))
      (equal (cadr row) (+ (car row) 1)))
     (putnam-2025-b4-horizontal-row-p
      (cdr row)))))

(defun putnam-2025-b4-horizontal-steps-p (matrix)
  (if (endp matrix)
      t
    (and
     (putnam-2025-b4-horizontal-row-p (car matrix))
     (putnam-2025-b4-horizontal-steps-p
      (cdr matrix)))))

(defun putnam-2025-b4-row-sum (row)
  (if (endp row)
      0
    (+ (car row)
       (putnam-2025-b4-row-sum (cdr row)))))

(defun putnam-2025-b4-matrix-sum (matrix)
  (if (endp matrix)
      0
    (+ (putnam-2025-b4-row-sum (car matrix))
       (putnam-2025-b4-matrix-sum (cdr matrix)))))

(defun putnam-2025-b4-row-nonzero-count (row)
  (if (endp row)
      0
    (+ (if (equal (car row) 0) 0 1)
       (putnam-2025-b4-row-nonzero-count
        (cdr row)))))

(defun putnam-2025-b4-matrix-nonzero-count (matrix)
  (if (endp matrix)
      0
    (+ (putnam-2025-b4-row-nonzero-count
        (car matrix))
       (putnam-2025-b4-matrix-nonzero-count
        (cdr matrix)))))

(defun putnambench-putnam-2025-b4-statement
    (m matrix s nonzero-count)
  (implies
   (and
    (natp m)
    (putnam-2025-b4-natural-matrix-p
     matrix (+ m 2) (+ m 2))
    (putnam-2025-b4-zero-region-p matrix 0 m)
    (putnam-2025-b4-vertical-steps-p matrix)
    (putnam-2025-b4-horizontal-steps-p matrix)
    (natp s)
    (equal s (putnam-2025-b4-matrix-sum matrix))
    (natp nonzero-count)
    (equal
     nonzero-count
     (putnam-2025-b4-matrix-nonzero-count matrix)))
   (<= (* 3 s)
       (* (+ m 4) nonzero-count))))

(value-triple :itpeval-statement-checked)
:q
