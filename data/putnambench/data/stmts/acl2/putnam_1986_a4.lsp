;; Statement-only formalization of PutnamBench corpus artifact putnam_1986_a4:
;; the number of n by n matrices over {-1,0,1} whose transversal sums are all
;; equal has the stated four-term exponential formula. This file contains no
;; proof.

(in-package "ACL2")

;; A code in [0,3^(n^2)) has exactly n^2 base-three digits. Mapping the digit
;; 0, 1, or 2 at position row*n+column to -1, 0, or 1 gives a bijection with
;; all n by n matrices in the source set.
(defun putnam-1986-a4-matrix-entry
    (matrix-code n row column)
  (- (mod
      (floor matrix-code
             (expt 3 (+ (* row n) column)))
      3)
     1))

(defun putnam-1986-a4-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-1986-a4-range-from
           (+ start 1) (- count 1)))))

(defun putnam-1986-a4-prefix-each (value lists)
  (if (endp lists)
      nil
    (cons (cons value (car lists))
          (putnam-1986-a4-prefix-each
           value (cdr lists)))))

(defun putnam-1986-a4-insert-everywhere (value values)
  (if (endp values)
      (list (list value))
    (cons (cons value values)
          (putnam-1986-a4-prefix-each
           (car values)
           (putnam-1986-a4-insert-everywhere
            value (cdr values))))))

(defun putnam-1986-a4-insert-into-each
    (value permutations)
  (if (endp permutations)
      nil
    (append
     (putnam-1986-a4-insert-everywhere
      value (car permutations))
     (putnam-1986-a4-insert-into-each
      value (cdr permutations)))))

;; For the duplicate-free index list 0,...,n-1, these are exactly the
;; permutations of the columns, hence exactly the source transversals.
(defun putnam-1986-a4-permutations (values)
  (if (endp values)
      (list nil)
    (putnam-1986-a4-insert-into-each
     (car values)
     (putnam-1986-a4-permutations
      (cdr values)))))

(defun putnam-1986-a4-transversal-sum
    (matrix-code n permutation row)
  (if (endp permutation)
      0
    (+ (putnam-1986-a4-matrix-entry
        matrix-code n row (car permutation))
       (putnam-1986-a4-transversal-sum
        matrix-code n (cdr permutation) (+ row 1)))))

(defun putnam-1986-a4-all-transversal-sums-equal-p
    (matrix-code n reference-sum permutations)
  (if (endp permutations)
      t
    (and
     (equal
      (putnam-1986-a4-transversal-sum
       matrix-code n (car permutations) 0)
      reference-sum)
     (putnam-1986-a4-all-transversal-sums-equal-p
      matrix-code n reference-sum (cdr permutations)))))

;; The permutation list is nonempty. Therefore the source existential common
;; sum S is equivalent to requiring every transversal sum to equal the sum for
;; its first permutation; the witness remains internal to this predicate.
(defun putnam-1986-a4-good-matrix-code-p (matrix-code n)
  (let* ((indices
          (putnam-1986-a4-range-from 0 n))
         (permutations
          (putnam-1986-a4-permutations indices))
         (reference-sum
          (putnam-1986-a4-transversal-sum
           matrix-code n (car permutations) 0)))
    (putnam-1986-a4-all-transversal-sums-equal-p
     matrix-code n reference-sum permutations)))

(defun putnam-1986-a4-count-good-matrix-codes
    (code-count n)
  (declare (xargs :measure (nfix code-count)))
  (if (zp code-count)
      0
    (let ((matrix-code (- code-count 1)))
      (+ (if (putnam-1986-a4-good-matrix-code-p
              matrix-code n)
             1
           0)
         (putnam-1986-a4-count-good-matrix-codes
          matrix-code n)))))

(defun putnam-1986-a4-matrix-count (n)
  (if (natp n)
      (putnam-1986-a4-count-good-matrix-codes
       (expt 3 (* n n))
       n)
    0))

;; The free argument N universally ranges over the positive dimensions from
;; the source theorem. The displayed expression instantiates the catalogued
;; solution (a1,b1,a2,b2,a3,b3,a4) = (1,4,2,3,-4,2,1).
(defun putnambench-putnam-1986-a4-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (equal
    (putnam-1986-a4-matrix-count n)
    (+ (expt 4 n)
       (* 2 (expt 3 n))
       (* -4 (expt 2 n))
       1))))

(value-triple :itpeval-statement-checked)
:q
