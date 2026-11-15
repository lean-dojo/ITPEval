;; Statement-only formalization of PutnamBench corpus artifact putnam_1996_b3:
;; for n at least 2, the greatest cyclic adjacent-product sum over all
;; permutations of 1 through n has the stated cubic value. This file contains
;; no proof.

(in-package "ACL2")

;; Restricting a source function x to indices 0,...,n-1 gives exactly one
;; permutation list below, and every such list extends to a source function
;; arbitrarily outside those indices. Thus this finite representation is
;; bidirectionally equivalent to the function-based source statement.

(defun putnam-1996-b3-one-through (n)
  (declare (xargs :measure (nfix n)))
  (if (or (not (natp n))
          (zp n))
      nil
    (append
     (putnam-1996-b3-one-through (- n 1))
     (list n))))

(defun putnam-1996-b3-prepend-each (value lists)
  (if (endp lists)
      nil
    (cons
     (cons value (car lists))
     (putnam-1996-b3-prepend-each value (cdr lists)))))

(defun putnam-1996-b3-insert-everywhere (value values)
  (if (endp values)
      (list (list value))
    (cons
     (cons value values)
     (putnam-1996-b3-prepend-each
      (car values)
      (putnam-1996-b3-insert-everywhere
       value (cdr values))))))

(defun putnam-1996-b3-insert-into-permutations
    (value permutations)
  (if (endp permutations)
      nil
    (append
     (putnam-1996-b3-insert-everywhere
      value (car permutations))
     (putnam-1996-b3-insert-into-permutations
      value (cdr permutations)))))

(defun putnam-1996-b3-permutations (values)
  (if (endp values)
      (list nil)
    (putnam-1996-b3-insert-into-permutations
     (car values)
     (putnam-1996-b3-permutations (cdr values)))))

(defun putnam-1996-b3-adjacent-product-sum (values)
  (if (or (endp values)
          (endp (cdr values)))
      0
    (+
     (* (car values) (cadr values))
     (putnam-1996-b3-adjacent-product-sum
      (cdr values)))))

(defun putnam-1996-b3-last-value (values)
  (if (or (endp values)
          (endp (cdr values)))
      (car values)
    (putnam-1996-b3-last-value (cdr values))))

(defun putnam-1996-b3-cyclic-product-sum (values)
  (if (endp values)
      0
    (+
     (putnam-1996-b3-adjacent-product-sum values)
     (* (putnam-1996-b3-last-value values)
        (car values)))))

(defun putnam-1996-b3-value-attained-p
    (permutations value)
  (if (endp permutations)
      nil
    (or
     (equal
      (putnam-1996-b3-cyclic-product-sum
       (car permutations))
      value)
     (putnam-1996-b3-value-attained-p
      (cdr permutations) value))))

(defun putnam-1996-b3-all-values-at-most-p
    (permutations value)
  (if (endp permutations)
      t
    (and
     (<=
      (putnam-1996-b3-cyclic-product-sum
       (car permutations))
      value)
     (putnam-1996-b3-all-values-at-most-p
      (cdr permutations) value))))

(defun putnam-1996-b3-solution (n)
  (/
   (+ (* 2 (expt n 3))
      (* 3 (expt n 2))
      (- (* 11 n))
      18)
   6))

(defun putnambench-putnam-1996-b3-statement (n)
  (implies
   (and
    (natp n)
    (<= 2 n))
   (let* ((permutations
           (putnam-1996-b3-permutations
            (putnam-1996-b3-one-through n)))
          (solution
           (putnam-1996-b3-solution n)))
     (and
      (putnam-1996-b3-value-attained-p
       permutations solution)
      (putnam-1996-b3-all-values-at-most-p
       permutations solution)))))

(value-triple :itpeval-statement-checked)
:q
