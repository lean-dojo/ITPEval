;; Statement-only formalization of PutnamBench corpus artifact putnam_1969_a2:
;; the determinant of the n by n real matrix with (i,j)-entry |i-j| has the
;; stated closed form for every positive n. This file contains no proof.

(in-package "ACL2")

;; The matrix entries are integers. Its determinant over the reals is therefore
;; the canonical real image of the exact integer Leibniz sum computed below.
;; Permutations are image lists for the ordered index set {0,...,n-1}.

(defun putnam-1969-a2-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-1969-a2-range-from
           (+ start 1) (- count 1)))))

(defun putnam-1969-a2-prefix-each (value lists)
  (if (endp lists)
      nil
    (cons (cons value (car lists))
          (putnam-1969-a2-prefix-each
           value (cdr lists)))))

(defun putnam-1969-a2-insert-everywhere (value values)
  (if (endp values)
      (list (list value))
    (cons (cons value values)
          (putnam-1969-a2-prefix-each
           (car values)
           (putnam-1969-a2-insert-everywhere
            value (cdr values))))))

(defun putnam-1969-a2-insert-into-each
    (value permutations)
  (if (endp permutations)
      nil
    (append
     (putnam-1969-a2-insert-everywhere
      value (car permutations))
     (putnam-1969-a2-insert-into-each
      value (cdr permutations)))))

(defun putnam-1969-a2-permutations (values)
  (if (endp values)
      (list nil)
    (putnam-1969-a2-insert-into-each
     (car values)
     (putnam-1969-a2-permutations
      (cdr values)))))

(defun putnam-1969-a2-count-greater (value values)
  (if (endp values)
      0
    (+ (if (> value (car values)) 1 0)
       (putnam-1969-a2-count-greater
        value (cdr values)))))

(defun putnam-1969-a2-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (putnam-1969-a2-count-greater
        (car permutation) (cdr permutation))
       (putnam-1969-a2-inversion-count
        (cdr permutation)))))

(defun putnam-1969-a2-distance (i j)
  (abs (- i j)))

(defun putnam-1969-a2-diagonal-product
    (permutation row-index)
  (if (endp permutation)
      1
    (* (putnam-1969-a2-distance
        row-index (car permutation))
       (putnam-1969-a2-diagonal-product
        (cdr permutation) (+ row-index 1)))))

(defun putnam-1969-a2-determinant-sum (permutations)
  (if (endp permutations)
      0
    (let* ((permutation (car permutations))
           (product
            (putnam-1969-a2-diagonal-product
             permutation 0))
           (signed-product
            (if (equal
                 (mod
                  (putnam-1969-a2-inversion-count
                   permutation)
                  2)
                 0)
                product
              (- product))))
      (+ signed-product
         (putnam-1969-a2-determinant-sum
          (cdr permutations))))))

(defun putnam-1969-a2-determinant (n)
  (putnam-1969-a2-determinant-sum
   (putnam-1969-a2-permutations
    (putnam-1969-a2-range-from 0 n))))

(defun putnambench-putnam-1969-a2-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (equal
    (putnam-1969-a2-determinant n)
    (* (expt -1 (- n 1))
       (- n 1)
       (expt 2 (- n 2))))))

(value-triple :itpeval-statement-checked)
:q
