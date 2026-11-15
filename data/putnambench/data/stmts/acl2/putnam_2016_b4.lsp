;; Statement-only formalization of PutnamBench corpus artifact putnam_2016_b4:
;; the expected determinant of A minus its transpose for a uniformly random
;; 2n by 2n zero-one matrix is (2n)!/(4^n n!). This file contains no proof.

(in-package "ACL2")

;; Each integer from 0 through 2^(2n)^2-1 is the row-major bit string of one
;; zero-one matrix, giving a bijection with the source's finite matrix set.
;; All entries of A-transpose(A), its determinant, and the finite sum are
;; integers. ACL2's exact rational average therefore embeds into the reals as
;; exactly the source average, without restricting any matrix or real value.

(defun putnam-2016-b4-indices (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (- count 1)
          (putnam-2016-b4-indices (- count 1)))))

(defun putnam-2016-b4-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (putnam-2016-b4-prefix-each item (cdr lists)))))

(defun putnam-2016-b4-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons (cons item list)
          (putnam-2016-b4-prefix-each
           (car list)
           (putnam-2016-b4-insert-everywhere
            item (cdr list))))))

(defun putnam-2016-b4-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (putnam-2016-b4-insert-everywhere item (car lists))
     (putnam-2016-b4-insert-into-each
      item (cdr lists)))))

(defun putnam-2016-b4-permutations (list)
  (if (endp list)
      (list nil)
    (putnam-2016-b4-insert-into-each
     (car list)
     (putnam-2016-b4-permutations (cdr list)))))

(defun putnam-2016-b4-count-smaller (item list)
  (if (endp list)
      0
    (+ (if (< (car list) item) 1 0)
       (putnam-2016-b4-count-smaller item (cdr list)))))

(defun putnam-2016-b4-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (putnam-2016-b4-count-smaller
        (car permutation) (cdr permutation))
       (putnam-2016-b4-inversion-count
        (cdr permutation)))))

(defun putnam-2016-b4-permutation-sign (permutation)
  (if (evenp
       (putnam-2016-b4-inversion-count permutation))
      1
    -1))

(defun putnam-2016-b4-matrix-entry
    (code dimension row column)
  (mod
   (floor
    code
    (expt 2 (+ (* row dimension) column)))
   2))

(defun putnam-2016-b4-skew-entry
    (code dimension row column)
  (-
   (putnam-2016-b4-matrix-entry
    code dimension row column)
   (putnam-2016-b4-matrix-entry
    code dimension column row)))

(defun putnam-2016-b4-diagonal-product
    (code dimension row permutation)
  (if (endp permutation)
      1
    (* (putnam-2016-b4-skew-entry
        code dimension row (car permutation))
       (putnam-2016-b4-diagonal-product
        code dimension (+ row 1) (cdr permutation)))))

(defun putnam-2016-b4-determinant-sum
    (code dimension permutations)
  (if (endp permutations)
      0
    (+ (* (putnam-2016-b4-permutation-sign
           (car permutations))
          (putnam-2016-b4-diagonal-product
           code dimension 0 (car permutations)))
       (putnam-2016-b4-determinant-sum
        code dimension (cdr permutations)))))

;; This is the exact Leibniz determinant of A-transpose(A).

(defun putnam-2016-b4-determinant
    (code dimension permutations)
  (putnam-2016-b4-determinant-sum
   code dimension permutations))

(defun putnam-2016-b4-sum-matrices
    (code remaining dimension permutations)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (putnam-2016-b4-determinant
        code dimension permutations)
       (putnam-2016-b4-sum-matrices
        (+ code 1)
        (- remaining 1)
        dimension
        permutations))))

(defun putnam-2016-b4-average (n)
  (let* ((dimension (* 2 n))
         (entry-count (* dimension dimension))
         (matrix-count (expt 2 entry-count))
         (permutations
          (putnam-2016-b4-permutations
           (putnam-2016-b4-indices dimension))))
    (/ (putnam-2016-b4-sum-matrices
        0 matrix-count dimension permutations)
       matrix-count)))

(defun putnam-2016-b4-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-2016-b4-factorial (- n 1)))))

(defun putnam-2016-b4-solution (n)
  (/ (putnam-2016-b4-factorial (* 2 n))
     (* (expt 4 n)
        (putnam-2016-b4-factorial n))))

(defun putnambench-putnam-2016-b4-statement (n)
  (implies
   (and (natp n)
        (<= 1 n))
   (equal
    (putnam-2016-b4-average n)
    (putnam-2016-b4-solution n))))

(value-triple :itpeval-statement-checked)
:q
