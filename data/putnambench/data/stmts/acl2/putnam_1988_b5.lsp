;; Statement-only formalization of PutnamBench corpus artifact putnam_1988_b5:
;; the prescribed (2n+1)-square skew-symmetric matrix has real rank 2n for
;; every positive integer n. This file contains no proof.

(in-package "ACL2")

;; The source hypotheses uniquely determine every entry: diagonal entries are
;; zero, entries d places below the diagonal are 1 for 1 <= d <= n and -1
;; for n < d <= 2n, and upper entries follow by skew symmetry. Thus the
;; canonical integer matrix below is bidirectionally equivalent to quantifying
;; over source matrices satisfying those hypotheses.
;;
;; Integer determinants embed faithfully into the reals. For a
;; (2n+1)-square matrix, real rank 2n is equivalent to a zero full determinant
;; together with a nonzero 2n-by-2n minor. The finite searches below keep the
;; existential choice of that minor internal to the statement.

(defun putnam-1988-b5-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-1988-b5-range-from
           (+ start 1) (- count 1)))))

(defun putnam-1988-b5-entry (n row column)
  (cond
   ((equal row column) 0)
   ((> row column)
    (if (<= (- row column) n) 1 -1))
   ((<= (- column row) n) -1)
   (t 1)))

(defun putnam-1988-b5-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons
     (cons item (car lists))
     (putnam-1988-b5-prefix-each item (cdr lists)))))

(defun putnam-1988-b5-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons
     (cons item list)
     (putnam-1988-b5-prefix-each
      (car list)
      (putnam-1988-b5-insert-everywhere
       item (cdr list))))))

(defun putnam-1988-b5-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (putnam-1988-b5-insert-everywhere
      item (car lists))
     (putnam-1988-b5-insert-into-each
      item (cdr lists)))))

(defun putnam-1988-b5-permutations (list)
  (if (endp list)
      (list nil)
    (putnam-1988-b5-insert-into-each
     (car list)
     (putnam-1988-b5-permutations (cdr list)))))

(defun putnam-1988-b5-count-greater (item list)
  (if (endp list)
      0
    (+ (if (> item (car list)) 1 0)
       (putnam-1988-b5-count-greater
        item (cdr list)))))

(defun putnam-1988-b5-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (putnam-1988-b5-count-greater
        (car permutation) (cdr permutation))
       (putnam-1988-b5-inversion-count
        (cdr permutation)))))

(defun putnam-1988-b5-diagonal-product
    (n rows column-permutation)
  (if (endp rows)
      1
    (* (putnam-1988-b5-entry
        n (car rows) (car column-permutation))
       (putnam-1988-b5-diagonal-product
        n (cdr rows) (cdr column-permutation)))))

(defun putnam-1988-b5-determinant-sum
    (n rows column-permutations)
  (if (endp column-permutations)
      0
    (let* ((permutation (car column-permutations))
           (product
            (putnam-1988-b5-diagonal-product
             n rows permutation))
           (signed-product
            (if (evenp
                 (putnam-1988-b5-inversion-count
                  permutation))
                product
              (- product))))
      (+ signed-product
         (putnam-1988-b5-determinant-sum
          n rows (cdr column-permutations))))))

(defun putnam-1988-b5-determinant (n rows columns)
  (putnam-1988-b5-determinant-sum
   n
   rows
   (putnam-1988-b5-permutations columns)))

(defun putnam-1988-b5-combinations (values size)
  (if (or (zp size) (endp values))
      (if (zp size) (list nil) nil)
    (append
     (putnam-1988-b5-prefix-each
      (car values)
      (putnam-1988-b5-combinations
       (cdr values) (- size 1)))
     (putnam-1988-b5-combinations
      (cdr values) size))))

(defun putnam-1988-b5-nonzero-column-minor-p
    (n rows column-choices)
  (if (endp column-choices)
      nil
    (or
     (not
      (equal
       (putnam-1988-b5-determinant
        n rows (car column-choices))
       0))
     (putnam-1988-b5-nonzero-column-minor-p
      n rows (cdr column-choices)))))

(defun putnam-1988-b5-nonzero-minor-p
    (n row-choices column-choices)
  (if (endp row-choices)
      nil
    (or
     (putnam-1988-b5-nonzero-column-minor-p
      n (car row-choices) column-choices)
     (putnam-1988-b5-nonzero-minor-p
      n (cdr row-choices) column-choices))))

(defun putnam-1988-b5-rank-is-2n-p (n)
  (let* ((dimension (+ (* 2 n) 1))
         (minor-size (* 2 n))
         (indices
          (putnam-1988-b5-range-from 0 dimension))
         (row-choices
          (putnam-1988-b5-combinations
           indices minor-size))
         (column-choices
          (putnam-1988-b5-combinations
           indices minor-size)))
    (and
     (equal
      (putnam-1988-b5-determinant
       n indices indices)
      0)
     (putnam-1988-b5-nonzero-minor-p
      n row-choices column-choices))))

(defun putnambench-putnam-1988-b5-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (putnam-1988-b5-rank-is-2n-p n)))

(value-triple :itpeval-statement-checked)
:q
