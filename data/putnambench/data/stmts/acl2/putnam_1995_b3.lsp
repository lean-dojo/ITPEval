;; Statement-only formalization of PutnamBench corpus artifact putnam_1995_b3:
;; for each positive n, the sum of the determinants associated with all
;; n^2-digit decimal integers is 45 for n=1, 10*45^2 for n=2, and 0 otherwise.
;; This file contains no proof.

(in-package "ACL2")

;; The source digit functions vanish from index n^2 onward and are therefore
;; in bijection with the n^2-digit integers enumerated below. The decimal digit
;; at INDEX is read from left to right, matching the source's row-major matrix.

(defun putnam-1995-b3-digit (code digit-count index)
  (mod
   (floor code
          (expt 10 (- digit-count (+ index 1))))
   10))

(defun putnam-1995-b3-indices (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (- count 1)
          (putnam-1995-b3-indices (- count 1)))))

(defun putnam-1995-b3-prepend-each (value lists)
  (if (endp lists)
      nil
    (cons
     (cons value (car lists))
     (putnam-1995-b3-prepend-each value (cdr lists)))))

(defun putnam-1995-b3-insert-everywhere (value values)
  (if (endp values)
      (list (list value))
    (cons
     (cons value values)
     (putnam-1995-b3-prepend-each
      (car values)
      (putnam-1995-b3-insert-everywhere
       value (cdr values))))))

(defun putnam-1995-b3-insert-into-permutations
    (value permutations)
  (if (endp permutations)
      nil
    (append
     (putnam-1995-b3-insert-everywhere
      value (car permutations))
     (putnam-1995-b3-insert-into-permutations
      value (cdr permutations)))))

(defun putnam-1995-b3-permutations (values)
  (if (endp values)
      (list nil)
    (putnam-1995-b3-insert-into-permutations
     (car values)
     (putnam-1995-b3-permutations (cdr values)))))

(defun putnam-1995-b3-count-smaller (value values)
  (if (endp values)
      0
    (+ (if (< (car values) value) 1 0)
       (putnam-1995-b3-count-smaller value (cdr values)))))

(defun putnam-1995-b3-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (putnam-1995-b3-count-smaller
        (car permutation) (cdr permutation))
       (putnam-1995-b3-inversion-count
        (cdr permutation)))))

(defun putnam-1995-b3-permutation-sign (permutation)
  (if (equal
       (mod (putnam-1995-b3-inversion-count permutation) 2)
       0)
      1
    -1))

;; This is the product of the row-column entries selected by PERMUTATION.

(defun putnam-1995-b3-diagonal-product
    (code n digit-count row permutation)
  (if (endp permutation)
      1
    (* (putnam-1995-b3-digit
        code
        digit-count
        (+ (* row n) (car permutation)))
       (putnam-1995-b3-diagonal-product
        code n digit-count (+ row 1) (cdr permutation)))))

(defun putnam-1995-b3-determinant-sum
    (code n digit-count permutations)
  (if (endp permutations)
      0
    (+ (* (putnam-1995-b3-permutation-sign
           (car permutations))
          (putnam-1995-b3-diagonal-product
           code n digit-count 0 (car permutations)))
       (putnam-1995-b3-determinant-sum
        code n digit-count (cdr permutations)))))

;; The exact integer determinant is represented by its Leibniz expansion.

(defun putnam-1995-b3-determinant (code n digit-count)
  (putnam-1995-b3-determinant-sum
   code
   n
   digit-count
   (putnam-1995-b3-permutations
    (putnam-1995-b3-indices n))))

(defun putnam-1995-b3-sum-codes
    (code remaining n digit-count)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (putnam-1995-b3-determinant
        code n digit-count)
       (putnam-1995-b3-sum-codes
        (+ code 1) (- remaining 1) n digit-count))))

(defun putnam-1995-b3-total (n)
  (let* ((digit-count (* n n))
         (first-code (expt 10 (- digit-count 1)))
         (number-of-codes (* 9 first-code)))
    (putnam-1995-b3-sum-codes
     first-code number-of-codes n digit-count)))

(defun putnam-1995-b3-solution (n)
  (if (equal n 1)
      45
    (if (equal n 2)
        (* 10 (expt 45 2))
      0)))

(defun putnambench-putnam-1995-b3-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (equal
    (putnam-1995-b3-total n)
    (putnam-1995-b3-solution n))))

(value-triple :itpeval-statement-checked)
:q
