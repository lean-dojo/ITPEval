;; Statement-only formalization of PutnamBench corpus artifact putnam_2023_b6:
;; the determinant of the n by n integer matrix counting nonnegative solutions
;; of a(i+1)+b(j+1)=n equals the stated signed even integer. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A finite matrix is represented extensionally by its rows in zero-based
;; index order. The source equation determines every entry. Since i+1 and j+1
;; are positive, every nonnegative solution has a,b <= n, so the bounded
;; recursive count below is exactly the source count over all naturals.

(defun putnam-2023-b6-count-b (a b n i j)
  (declare (xargs :measure (nfix b)))
  (if (zp b)
      (if (equal (* a (+ i 1)) n) 1 0)
    (+ (if (equal
            (+ (* a (+ i 1))
               (* b (+ j 1)))
            n)
           1
         0)
       (putnam-2023-b6-count-b
        a (- b 1) n i j))))

(defun putnam-2023-b6-count-pairs (a n i j)
  (declare (xargs :measure (nfix a)))
  (if (zp a)
      (putnam-2023-b6-count-b 0 n n i j)
    (+ (putnam-2023-b6-count-b a n n i j)
       (putnam-2023-b6-count-pairs
        (- a 1) n i j))))

(defun putnam-2023-b6-row-matches-p
    (row remaining n i j)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (equal row nil)
    (and
     (consp row)
     (equal
      (car row)
      (putnam-2023-b6-count-pairs n n i j))
     (putnam-2023-b6-row-matches-p
      (cdr row) (- remaining 1) n i (+ j 1)))))

(defun putnam-2023-b6-matrix-matches-p
    (matrix remaining n i)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (equal matrix nil)
    (and
     (consp matrix)
     (putnam-2023-b6-row-matches-p
      (car matrix) n n i 0)
     (putnam-2023-b6-matrix-matches-p
      (cdr matrix) (- remaining 1) n (+ i 1)))))

;; Generate all permutations of the zero-based column indices.

(defun putnam-2023-b6-indices (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (- count 1)
          (putnam-2023-b6-indices (- count 1)))))

(defun putnam-2023-b6-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (putnam-2023-b6-prefix-each item (cdr lists)))))

(defun putnam-2023-b6-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons (cons item list)
          (putnam-2023-b6-prefix-each
           (car list)
           (putnam-2023-b6-insert-everywhere
            item (cdr list))))))

(defun putnam-2023-b6-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (putnam-2023-b6-insert-everywhere item (car lists))
     (putnam-2023-b6-insert-into-each
      item (cdr lists)))))

(defun putnam-2023-b6-permutations (list)
  (if (endp list)
      (list nil)
    (putnam-2023-b6-insert-into-each
     (car list)
     (putnam-2023-b6-permutations (cdr list)))))

(defun putnam-2023-b6-count-smaller (item list)
  (if (endp list)
      0
    (+ (if (< (car list) item) 1 0)
       (putnam-2023-b6-count-smaller item (cdr list)))))

(defun putnam-2023-b6-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (putnam-2023-b6-count-smaller
        (car permutation) (cdr permutation))
       (putnam-2023-b6-inversion-count
        (cdr permutation)))))

(defun putnam-2023-b6-permutation-sign (permutation)
  (if (evenp
       (putnam-2023-b6-inversion-count permutation))
      1
    -1))

(defun putnam-2023-b6-diagonal-product
    (matrix row permutation)
  (if (endp permutation)
      1
    (* (nth (car permutation) (nth row matrix))
       (putnam-2023-b6-diagonal-product
        matrix (+ row 1) (cdr permutation)))))

(defun putnam-2023-b6-determinant-sum
    (matrix permutations)
  (if (endp permutations)
      0
    (+ (* (putnam-2023-b6-permutation-sign
           (car permutations))
          (putnam-2023-b6-diagonal-product
           matrix 0 (car permutations)))
       (putnam-2023-b6-determinant-sum
        matrix (cdr permutations)))))

;; This is the exact Leibniz determinant of the represented integer matrix.

(defun putnam-2023-b6-determinant (matrix n)
  (putnam-2023-b6-determinant-sum
   matrix
   (putnam-2023-b6-permutations
    (putnam-2023-b6-indices n))))

(defun putnam-2023-b6-ceiling-half (n)
  (floor (+ n 1) 2))

(defun putnam-2023-b6-solution (n)
  (let ((half (putnam-2023-b6-ceiling-half n)))
    (* (if (evenp (+ half 1)) 1 -1)
       2
       half)))

(defun putnambench-putnam-2023-b6-statement (n matrix)
  (implies
   (and
    (natp n)
    (< 0 n)
    (putnam-2023-b6-matrix-matches-p matrix n n 0))
   (equal
    (putnam-2023-b6-determinant matrix n)
    (putnam-2023-b6-solution n))))

(value-triple :itpeval-statement-checked)
:q
