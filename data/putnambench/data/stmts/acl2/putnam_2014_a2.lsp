;; Statement-only formalization of PutnamBench corpus artifact putnam_2014_a2:
;; for every positive n, the determinant of the n by n real matrix whose
;; (i,j)-entry is 1/min(i,j), with indices starting at 1, is
;; (-1)^(n-1)/((n-1)! n!). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source entry hypothesis determines A extensionally, so quantifying over
;; A under that hypothesis is equivalent to taking the canonical matrix below.
;; Every entry is rational, and the Leibniz formula uses only field operations,
;; so its real determinant is the canonical real embedding of this exact ACL2
;; rational. Equality of these rationals is therefore bidirectionally
;; equivalent to the source real equality; no arbitrary real value is narrowed.

(defun putnam-2014-a2-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-2014-a2-range-from
           (+ 1 start) (- count 1)))))

;; Generate all permutations of the zero-based column indices.

(defun putnam-2014-a2-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (putnam-2014-a2-prefix-each item (cdr lists)))))

(defun putnam-2014-a2-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons (cons item list)
          (putnam-2014-a2-prefix-each
           (car list)
           (putnam-2014-a2-insert-everywhere
            item (cdr list))))))

(defun putnam-2014-a2-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (putnam-2014-a2-insert-everywhere item (car lists))
     (putnam-2014-a2-insert-into-each
      item (cdr lists)))))

(defun putnam-2014-a2-permutations (list)
  (if (endp list)
      (list nil)
    (putnam-2014-a2-insert-into-each
     (car list)
     (putnam-2014-a2-permutations (cdr list)))))

(defun putnam-2014-a2-count-greater (item list)
  (if (endp list)
      0
    (+ (if (> item (car list)) 1 0)
       (putnam-2014-a2-count-greater item (cdr list)))))

(defun putnam-2014-a2-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (putnam-2014-a2-count-greater
        (car permutation) (cdr permutation))
       (putnam-2014-a2-inversion-count
        (cdr permutation)))))

;; Zero-based row and column indices represent the source indices i=row+1 and
;; j=column+1.

(defun putnam-2014-a2-entry (row column)
  (/ 1
     (if (< row column)
         (+ row 1)
       (+ column 1))))

(defun putnam-2014-a2-diagonal-product (permutation row)
  (if (endp permutation)
      1
    (* (putnam-2014-a2-entry row (car permutation))
       (putnam-2014-a2-diagonal-product
        (cdr permutation) (+ row 1)))))

(defun putnam-2014-a2-determinant-sum (permutations)
  (if (endp permutations)
      0
    (let* ((permutation (car permutations))
           (product
            (putnam-2014-a2-diagonal-product permutation 0))
           (signed-product
            (if (evenp
                 (putnam-2014-a2-inversion-count permutation))
                product
              (- product))))
      (+ signed-product
         (putnam-2014-a2-determinant-sum
          (cdr permutations))))))

(defun putnam-2014-a2-determinant (n)
  (putnam-2014-a2-determinant-sum
   (putnam-2014-a2-permutations
    (putnam-2014-a2-range-from 0 n))))

(defun putnam-2014-a2-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-2014-a2-factorial (- n 1)))))

(defun putnam-2014-a2-solution (n)
  (/ (if (evenp (- n 1)) 1 -1)
     (* (putnam-2014-a2-factorial (- n 1))
        (putnam-2014-a2-factorial n))))

(defun putnambench-putnam-2014-a2-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (equal
    (putnam-2014-a2-determinant n)
    (putnam-2014-a2-solution n))))

(value-triple :itpeval-statement-checked)
:q
