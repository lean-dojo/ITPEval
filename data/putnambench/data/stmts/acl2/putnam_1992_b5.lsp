;; Statement-only formalization of PutnamBench corpus artifact putnam_1992_b5:
;; the determinant ratios D_n/n! for the specified (n-1)-square matrices are
;; unbounded, so the boundedness question has answer False. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; D_n is represented by the exact Leibniz determinant over all permutations
;; of the columns 0,...,n-2. The entry at (i,j) is i+3 on the diagonal and 1
;; off the diagonal, exactly as in both source statements.

(defun putnam-1992-b5-indices (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (- count 1)
          (putnam-1992-b5-indices (- count 1)))))

(defun putnam-1992-b5-prepend-each (value lists)
  (if (endp lists)
      nil
    (cons
     (cons value (car lists))
     (putnam-1992-b5-prepend-each value (cdr lists)))))

(defun putnam-1992-b5-insert-everywhere (value values)
  (if (endp values)
      (list (list value))
    (cons
     (cons value values)
     (putnam-1992-b5-prepend-each
      (car values)
      (putnam-1992-b5-insert-everywhere
       value (cdr values))))))

(defun putnam-1992-b5-insert-into-permutations
    (value permutations)
  (if (endp permutations)
      nil
    (append
     (putnam-1992-b5-insert-everywhere
      value (car permutations))
     (putnam-1992-b5-insert-into-permutations
      value (cdr permutations)))))

(defun putnam-1992-b5-permutations (values)
  (if (endp values)
      (list nil)
    (putnam-1992-b5-insert-into-permutations
     (car values)
     (putnam-1992-b5-permutations (cdr values)))))

(defun putnam-1992-b5-count-smaller (value values)
  (if (endp values)
      0
    (+ (if (< (car values) value) 1 0)
       (putnam-1992-b5-count-smaller value (cdr values)))))

(defun putnam-1992-b5-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (putnam-1992-b5-count-smaller
        (car permutation) (cdr permutation))
       (putnam-1992-b5-inversion-count
        (cdr permutation)))))

(defun putnam-1992-b5-permutation-sign (permutation)
  (if (equal
       (mod (putnam-1992-b5-inversion-count permutation) 2)
       0)
      1
    -1))

(defun putnam-1992-b5-entry (row column)
  (if (equal row column)
      (+ row 3)
    1))

(defun putnam-1992-b5-determinant-product
    (row permutation)
  (if (endp permutation)
      1
    (* (putnam-1992-b5-entry row (car permutation))
       (putnam-1992-b5-determinant-product
        (+ row 1) (cdr permutation)))))

(defun putnam-1992-b5-determinant-sum (permutations)
  (if (endp permutations)
      0
    (+ (* (putnam-1992-b5-permutation-sign
           (car permutations))
          (putnam-1992-b5-determinant-product
           0 (car permutations)))
       (putnam-1992-b5-determinant-sum
        (cdr permutations)))))

(defun putnam-1992-b5-determinant (n)
  (putnam-1992-b5-determinant-sum
   (putnam-1992-b5-permutations
    (putnam-1992-b5-indices (- n 1)))))

(defun putnam-1992-b5-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (putnam-1992-b5-factorial (- n 1)))))

(defun putnam-1992-b5-exceeds-bound-p (bound n)
  (and
   (natp n)
   (<= 2 n)
   (< bound
      (abs
       (/ (putnam-1992-b5-determinant n)
          (putnam-1992-b5-factorial n))))))

;; The annotated answer is False. Negating boundedness directly says that
;; every rational bound is exceeded in absolute value by some source term.
(defun-sk putnam-1992-b5-counterexample-exists-p (bound)
  (exists (n)
    (putnam-1992-b5-exceeds-bound-p bound n)))

(defun putnambench-putnam-1992-b5-statement (bound)
  (implies
   (rationalp bound)
   (putnam-1992-b5-counterexample-exists-p bound)))

(value-triple :itpeval-statement-checked)
:q
