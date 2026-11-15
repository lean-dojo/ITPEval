;; Statement-only formalization of PutnamBench corpus artifact putnam_2021_b5:
;; positive powers of an integer matrix whose nonempty principal minors all
;; have odd determinant retain that property. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; An exact-length list of exact-length integer rows is the extensional
;; representation of a matrix on Fin n. ACL2 universally closes N, MATRIX,
;; and K in the final predicate, preserving the source quantifiers over every
;; positive dimension, every integer matrix, and every positive exponent.

(defun putnam-2021-b5-integer-row-p (row columns)
  (declare (xargs :measure (nfix columns)))
  (if (zp columns)
      (equal row nil)
    (and
     (consp row)
     (integerp (car row))
     (putnam-2021-b5-integer-row-p
      (cdr row) (- columns 1)))))

(defun putnam-2021-b5-integer-matrix-p
    (matrix rows columns)
  (declare (xargs :measure (nfix rows)))
  (if (zp rows)
      (equal matrix nil)
    (and
     (consp matrix)
     (putnam-2021-b5-integer-row-p
      (car matrix) columns)
     (putnam-2021-b5-integer-matrix-p
      (cdr matrix) (- rows 1) columns))))

(defun putnam-2021-b5-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     start
     (putnam-2021-b5-range-from
      (+ start 1) (- count 1)))))

;; POWERSET enumerates every subset of the finite index carrier exactly once.

(defun putnam-2021-b5-prefix-each (item lists)
  (if (consp lists)
      (cons
       (cons item (car lists))
       (putnam-2021-b5-prefix-each item (cdr lists)))
    nil))

(defun putnam-2021-b5-powerset (items)
  (if (consp items)
      (let ((tail-subsets
             (putnam-2021-b5-powerset (cdr items))))
        (append
         tail-subsets
         (putnam-2021-b5-prefix-each
          (car items) tail-subsets)))
    (list nil)))

(defun putnam-2021-b5-select-row (row indices)
  (if (consp indices)
      (cons
       (nth (car indices) row)
       (putnam-2021-b5-select-row row (cdr indices)))
    nil))

(defun putnam-2021-b5-principal-submatrix
    (matrix indices)
  (if (consp indices)
      (cons
       (putnam-2021-b5-select-row
        (nth (car indices) matrix) indices)
       (putnam-2021-b5-principal-submatrix
        matrix (cdr indices)))
    nil))

;; The determinant is the exact Leibniz signed sum over all permutations.

(defun putnam-2021-b5-permutation-prefix-each
    (item lists)
  (if (consp lists)
      (cons
       (cons item (car lists))
       (putnam-2021-b5-permutation-prefix-each
        item (cdr lists)))
    nil))

(defun putnam-2021-b5-insert-everywhere (item list)
  (if (consp list)
      (cons
       (cons item list)
       (putnam-2021-b5-permutation-prefix-each
        (car list)
        (putnam-2021-b5-insert-everywhere
         item (cdr list))))
    (list (list item))))

(defun putnam-2021-b5-insert-into-each
    (item lists)
  (if (consp lists)
      (append
       (putnam-2021-b5-insert-everywhere
        item (car lists))
       (putnam-2021-b5-insert-into-each
        item (cdr lists)))
    nil))

(defun putnam-2021-b5-permutations (items)
  (if (consp items)
      (putnam-2021-b5-insert-into-each
       (car items)
       (putnam-2021-b5-permutations (cdr items)))
    (list nil)))

(defun putnam-2021-b5-count-greater (item items)
  (if (consp items)
      (+ (if (> item (car items)) 1 0)
         (putnam-2021-b5-count-greater
          item (cdr items)))
    0))

(defun putnam-2021-b5-inversion-count (permutation)
  (if (consp permutation)
      (+ (putnam-2021-b5-count-greater
          (car permutation) (cdr permutation))
         (putnam-2021-b5-inversion-count
          (cdr permutation)))
    0))

(defun putnam-2021-b5-diagonal-product
    (matrix permutation row)
  (if (consp permutation)
      (*
       (nth (car permutation) (nth row matrix))
       (putnam-2021-b5-diagonal-product
        matrix (cdr permutation) (+ row 1)))
    1))

(defun putnam-2021-b5-determinant-sum
    (matrix permutations)
  (if (consp permutations)
      (let* ((permutation (car permutations))
             (product
              (putnam-2021-b5-diagonal-product
               matrix permutation 0))
             (signed-product
              (if (evenp
                   (putnam-2021-b5-inversion-count
                    permutation))
                  product
                (- product))))
        (+
         signed-product
         (putnam-2021-b5-determinant-sum
          matrix (cdr permutations))))
    0))

(defun putnam-2021-b5-determinant
    (matrix dimension)
  (putnam-2021-b5-determinant-sum
   matrix
   (putnam-2021-b5-permutations
    (putnam-2021-b5-range-from 0 dimension))))

(defun putnam-2021-b5-all-principal-minors-odd-p
    (matrix subsets)
  (if (consp subsets)
      (and
       (or
        (endp (car subsets))
        (oddp
         (putnam-2021-b5-determinant
          (putnam-2021-b5-principal-submatrix
           matrix (car subsets))
          (len (car subsets)))))
       (putnam-2021-b5-all-principal-minors-odd-p
        matrix (cdr subsets)))
    t))

(defun putnam-2021-b5-very-odd-p (matrix dimension)
  (putnam-2021-b5-all-principal-minors-odd-p
   matrix
   (putnam-2021-b5-powerset
    (putnam-2021-b5-range-from 0 dimension))))

;; These functions give ordinary integer matrix multiplication.

(defun putnam-2021-b5-matrix-column
    (matrix column)
  (if (consp matrix)
      (cons
       (nth column (car matrix))
       (putnam-2021-b5-matrix-column
        (cdr matrix) column))
    nil))

(defun putnam-2021-b5-dot-product (left right)
  (if (and (consp left) (consp right))
      (+
       (* (car left) (car right))
       (putnam-2021-b5-dot-product
        (cdr left) (cdr right)))
    0))

(defun putnam-2021-b5-multiply-row
    (row right columns)
  (if (consp columns)
      (cons
       (putnam-2021-b5-dot-product
        row
        (putnam-2021-b5-matrix-column
         right (car columns)))
       (putnam-2021-b5-multiply-row
        row right (cdr columns)))
    nil))

(defun putnam-2021-b5-matrix-multiply-rows
    (left right columns)
  (if (consp left)
      (cons
       (putnam-2021-b5-multiply-row
        (car left) right columns)
       (putnam-2021-b5-matrix-multiply-rows
        (cdr left) right columns))
    nil))

(defun putnam-2021-b5-matrix-multiply
    (left right dimension)
  (putnam-2021-b5-matrix-multiply-rows
   left right
   (putnam-2021-b5-range-from 0 dimension)))

;; On positive exponents this recurrence is exactly the source matrix power.

(defun putnam-2021-b5-positive-power
    (matrix exponent dimension)
  (declare (xargs :measure (nfix exponent)))
  (if (or (not (natp exponent))
          (<= exponent 1))
      matrix
    (putnam-2021-b5-matrix-multiply
     (putnam-2021-b5-positive-power
      matrix (- exponent 1) dimension)
     matrix
     dimension)))

(defun putnambench-putnam-2021-b5-statement
    (n matrix k)
  (implies
   (and
    (posp n)
    (putnam-2021-b5-integer-matrix-p matrix n n)
    (putnam-2021-b5-very-odd-p matrix n)
    (posp k))
   (putnam-2021-b5-very-odd-p
    (putnam-2021-b5-positive-power matrix k n)
    n)))

(value-triple :itpeval-statement-checked)
:q
