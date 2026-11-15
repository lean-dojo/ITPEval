;; Statement-only formalization of PutnamBench corpus artifact putnam_2024_a6:
;; the Hankel determinant of the real power-series coefficients defined by
;; (1-3x-sqrt(1-14x+9x^2))/4 equals 10^(n(n-1)/2). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; If C(x) is the source generating function, then C(0)=0 and squaring the
;; displayed radical identity gives
;;
;;   C = X + 3*X*C + 2*C^2.
;;
;; Conversely, this formal identity with constant coefficient zero has a
;; unique coefficient sequence. Its coefficients have positive radius of
;; convergence, and near zero the square root with constant term one recovers
;; the source analytic identity. Thus the recurrence below is bidirectionally
;; equivalent to the source HasSum hypothesis, not a finite truncation of an
;; arbitrary sequence. The recurrence also shows that every coefficient is an
;; integer, so ACL2 integer arithmetic represents its real value exactly.

(defun putnam-2024-a6-convolution-sum
    (coefficients k i)
  (declare (xargs :measure (nfix i)))
  (if (zp i)
      0
    (+
     (* (nth i coefficients)
        (nth (- k i) coefficients))
     (putnam-2024-a6-convolution-sum
      coefficients k (- i 1)))))

(defun putnam-2024-a6-next-coefficient (coefficients)
  (let ((k (len coefficients)))
    (+
     (if (equal k 1) 1 0)
     (* 3 (nth (- k 1) coefficients))
     (* 2
        (putnam-2024-a6-convolution-sum
         coefficients k (- k 1))))))

;; Starting from (c_0)=(0), append exactly REMAINING further coefficients.

(defun putnam-2024-a6-extend-coefficients
    (remaining coefficients)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      coefficients
    (putnam-2024-a6-extend-coefficients
     (- remaining 1)
     (append
      coefficients
      (list
       (putnam-2024-a6-next-coefficient
        coefficients))))))

(defun putnam-2024-a6-hankel-entries
    (coefficients n index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (let ((row (floor index n))
          (column (mod index n)))
      (cons
       (nth (+ row column 1) coefficients)
       (putnam-2024-a6-hankel-entries
        coefficients n (+ index 1) (- remaining 1))))))

;; For positive N, indices i+j+1 range through at most 2*N-1, so the exact
;; prefix constructed here contains every coefficient used by the matrix.

(defun putnam-2024-a6-hankel-matrix (n)
  (if (posp n)
      (let ((coefficients
             (putnam-2024-a6-extend-coefficients
              (- (* 2 n) 1)
              (list 0))))
        (putnam-2024-a6-hankel-entries
         coefficients n 0 (* n n)))
    nil))

(defun putnam-2024-a6-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     start
     (putnam-2024-a6-range-from
      (+ start 1) (- count 1)))))

(defun putnam-2024-a6-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons
     (cons item (car lists))
     (putnam-2024-a6-prefix-each item (cdr lists)))))

(defun putnam-2024-a6-insert-everywhere (item values)
  (if (endp values)
      (list (list item))
    (cons
     (cons item values)
     (putnam-2024-a6-prefix-each
      (car values)
      (putnam-2024-a6-insert-everywhere
       item (cdr values))))))

(defun putnam-2024-a6-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (putnam-2024-a6-insert-everywhere
      item (car lists))
     (putnam-2024-a6-insert-into-each
      item (cdr lists)))))

(defun putnam-2024-a6-permutations (values)
  (if (endp values)
      (list nil)
    (putnam-2024-a6-insert-into-each
     (car values)
     (putnam-2024-a6-permutations (cdr values)))))

(defun putnam-2024-a6-count-greater (item values)
  (if (endp values)
      0
    (+
     (if (> item (car values)) 1 0)
     (putnam-2024-a6-count-greater
      item (cdr values)))))

(defun putnam-2024-a6-inversion-count (permutation)
  (if (endp permutation)
      0
    (+
     (putnam-2024-a6-count-greater
      (car permutation) (cdr permutation))
     (putnam-2024-a6-inversion-count
      (cdr permutation)))))

(defun putnam-2024-a6-diagonal-product
    (matrix n permutation row)
  (if (endp permutation)
      1
    (*
     (nth (+ (* row n) (car permutation)) matrix)
     (putnam-2024-a6-diagonal-product
      matrix n (cdr permutation) (+ row 1)))))

;; This is the full Leibniz determinant, so the row-major list is exactly the
;; source matrix on Fin N rather than a weakened matrix invariant.

(defun putnam-2024-a6-determinant-sum
    (matrix n permutations)
  (if (endp permutations)
      0
    (let* ((permutation (car permutations))
           (product
            (putnam-2024-a6-diagonal-product
             matrix n permutation 0))
           (signed-product
            (if (evenp
                 (putnam-2024-a6-inversion-count
                  permutation))
                product
              (- product))))
      (+
       signed-product
       (putnam-2024-a6-determinant-sum
        matrix n (cdr permutations))))))

(defun putnam-2024-a6-determinant (matrix n)
  (putnam-2024-a6-determinant-sum
   matrix
   n
   (putnam-2024-a6-permutations
    (putnam-2024-a6-range-from 0 n))))

;; ACL2 universally closes N. The benchmark's annotated solution is
;; 10^(N*(N-1)/2), and N*(N-1) is even for every natural N.

(defun putnambench-putnam-2024-a6-statement (n)
  (implies
   (posp n)
   (equal
    (putnam-2024-a6-determinant
     (putnam-2024-a6-hankel-matrix n)
     n)
    (expt 10 (floor (* n (- n 1)) 2)))))

(value-triple :itpeval-statement-checked)
:q
