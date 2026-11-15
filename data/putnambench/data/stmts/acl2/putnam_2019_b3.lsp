;; Statement-only formalization of PutnamBench corpus artifact putnam_2019_b3:
;; a real orthogonal matrix without eigenvalue 1 becomes a matrix with
;; eigenvalue 1 after left multiplication by a reflection in a unit vector.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2's native "real" numbers are rational, so the scalar arguments present
;; an arbitrary real-closed ordered field instead. Real-closed fields are
;; elementarily equivalent, and the matrix assertion below is first-order in
;; the field operations. Thus this retains arbitrary real entries rather than
;; restricting the source matrices and vector to rational coordinates.

(defun p2019b3-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p2019b3-unary (operation x)
  (apply$ operation (list x)))

(defun p2019b3-binary (operation x y)
  (apply$ operation (list x y)))

(defun-sk p2019b3-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and (p2019b3-member-p carrier x)
          (p2019b3-member-p carrier y)
          (p2019b3-member-p carrier z))
     (and
      (p2019b3-member-p carrier
                        (p2019b3-binary add x y))
      (p2019b3-member-p carrier
                        (p2019b3-binary multiply x y))
      (p2019b3-member-p carrier
                        (p2019b3-unary negate x))
      (p2019b3-member-p carrier
                        (p2019b3-unary inverse x))
      (equal
       (p2019b3-binary add
                       (p2019b3-binary add x y) z)
       (p2019b3-binary add
                       x (p2019b3-binary add y z)))
      (equal (p2019b3-binary add x y)
             (p2019b3-binary add y x))
      (equal (p2019b3-binary add x zero) x)
      (equal
       (p2019b3-binary add
                       x (p2019b3-unary negate x))
       zero)
      (equal
       (p2019b3-binary multiply
                       (p2019b3-binary multiply x y) z)
       (p2019b3-binary multiply
                       x (p2019b3-binary multiply y z)))
      (equal (p2019b3-binary multiply x y)
             (p2019b3-binary multiply y x))
      (equal (p2019b3-binary multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (p2019b3-binary multiply
                        x (p2019b3-unary inverse x))
        one))
      (equal
       (p2019b3-binary multiply
                       x (p2019b3-binary add y z))
       (p2019b3-binary add
                       (p2019b3-binary multiply x y)
                       (p2019b3-binary multiply x z)))))))

(defun-sk p2019b3-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and (p2019b3-member-p carrier x)
          (p2019b3-member-p carrier y)
          (p2019b3-member-p carrier z))
     (and
      (not (p2019b3-binary less x x))
      (or (equal x y)
          (p2019b3-binary less x y)
          (p2019b3-binary less y x))
      (implies
       (and (p2019b3-binary less x y)
            (p2019b3-binary less y z))
       (p2019b3-binary less x z))
      (implies
       (p2019b3-binary less x y)
       (p2019b3-binary
        less
        (p2019b3-binary add x z)
        (p2019b3-binary add y z)))
      (implies
       (and (p2019b3-binary less zero x)
            (p2019b3-binary less zero y))
       (p2019b3-binary
        less zero (p2019b3-binary multiply x y)))))))

(defun-sk p2019b3-square-root-laws-p
    (carrier zero multiply less square-root)
  (forall (x)
    (implies
     (and (p2019b3-member-p carrier x)
          (not (p2019b3-binary less x zero)))
     (let ((root (p2019b3-unary square-root x)))
       (and
        (p2019b3-member-p carrier root)
        (not (p2019b3-binary less root zero))
        (equal (p2019b3-binary multiply root root)
               x))))))

(defun p2019b3-scalar-list-p (values carrier)
  (if (endp values)
      (equal values nil)
    (and
     (p2019b3-member-p carrier (car values))
     (p2019b3-scalar-list-p (cdr values) carrier))))

(defun p2019b3-polynomial-p (coefficients carrier zero)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (p2019b3-scalar-list-p coefficients carrier)
   (not (equal (car (last coefficients)) zero))))

(defun p2019b3-polynomial-eval
    (coefficients x zero add multiply)
  (if (endp coefficients)
      zero
    (p2019b3-binary
     add
     (car coefficients)
     (p2019b3-binary
      multiply
      x
      (p2019b3-polynomial-eval
       (cdr coefficients) x zero add multiply)))))

(defun-sk p2019b3-odd-root-laws-p
    (carrier zero add multiply odd-root)
  (forall (coefficients)
    (implies
     (and
      (p2019b3-polynomial-p coefficients carrier zero)
      (evenp (len coefficients)))
     (let ((root (p2019b3-unary odd-root coefficients)))
       (and
        (p2019b3-member-p carrier root)
        (equal
         (p2019b3-polynomial-eval
          coefficients root zero add multiply)
         zero))))))

(defun p2019b3-real-closed-field-p
    (carrier zero one add multiply negate inverse
             less square-root odd-root)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp square-root)
   (tamep-functionp odd-root)
   (p2019b3-member-p carrier zero)
   (p2019b3-member-p carrier one)
   (not (equal zero one))
   (p2019b3-field-laws-p
    carrier zero one add multiply negate inverse)
   (p2019b3-order-laws-p
    carrier zero add multiply less)
   (p2019b3-binary less zero one)
   (p2019b3-square-root-laws-p
    carrier zero multiply less square-root)
   (p2019b3-odd-root-laws-p
    carrier zero add multiply odd-root)))

;; Matrices are true lists of rows, and vectors are true lists of scalars.
;; Their lengths give the exact Fin n indexing used by the source statements.

(defun p2019b3-vector-p (vector n carrier)
  (and
   (true-listp vector)
   (equal (len vector) n)
   (p2019b3-scalar-list-p vector carrier)))

(defun p2019b3-matrix-rows-p (rows n carrier)
  (if (endp rows)
      (equal rows nil)
    (and
     (p2019b3-vector-p (car rows) n carrier)
     (p2019b3-matrix-rows-p (cdr rows) n carrier))))

(defun p2019b3-matrix-p (matrix n carrier)
  (and
   (true-listp matrix)
   (equal (len matrix) n)
   (p2019b3-matrix-rows-p matrix n carrier)))

(defun p2019b3-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (p2019b3-range-from
           (+ 1 start) (- count 1)))))

(defun p2019b3-dot-product
    (left right zero add multiply)
  (if (or (endp left) (endp right))
      zero
    (p2019b3-binary
     add
     (p2019b3-binary multiply (car left) (car right))
     (p2019b3-dot-product
      (cdr left) (cdr right) zero add multiply))))

(defun p2019b3-row-orthogonal-to-rows-p
    (row rows zero add multiply)
  (if (endp rows)
      t
    (and
     (equal
      (p2019b3-dot-product
       row (car rows) zero add multiply)
      zero)
     (p2019b3-row-orthogonal-to-rows-p
      row (cdr rows) zero add multiply))))

(defun p2019b3-orthonormal-rows-p
    (rows zero one add multiply)
  (if (endp rows)
      t
    (and
     (equal
      (p2019b3-dot-product
       (car rows) (car rows) zero add multiply)
      one)
     (p2019b3-row-orthogonal-to-rows-p
      (car rows) (cdr rows) zero add multiply)
     (p2019b3-orthonormal-rows-p
      (cdr rows) zero one add multiply))))

(defun p2019b3-matrix-column (column matrix)
  (if (endp matrix)
      nil
    (cons (nth column (car matrix))
          (p2019b3-matrix-column column (cdr matrix)))))

(defun p2019b3-matrix-columns
    (matrix column count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     (p2019b3-matrix-column column matrix)
     (p2019b3-matrix-columns
      matrix (+ 1 column) (- count 1)))))

(defun p2019b3-matrix-transpose (matrix n)
  (p2019b3-matrix-columns matrix 0 n))

(defun p2019b3-orthogonal-matrix-p
    (matrix n zero one add multiply)
  (and
   (p2019b3-orthonormal-rows-p
    matrix zero one add multiply)
   (p2019b3-orthonormal-rows-p
    (p2019b3-matrix-transpose matrix n)
    zero one add multiply)))

;; Field-valued matrix operations.

(defun p2019b3-vector-add (left right add)
  (if (or (endp left) (endp right))
      nil
    (cons
     (p2019b3-binary add (car left) (car right))
     (p2019b3-vector-add (cdr left) (cdr right) add))))

(defun p2019b3-vector-negate (vector negate)
  (if (endp vector)
      nil
    (cons
     (p2019b3-unary negate (car vector))
     (p2019b3-vector-negate (cdr vector) negate))))

(defun p2019b3-vector-subtract (left right add negate)
  (p2019b3-vector-add
   left (p2019b3-vector-negate right negate) add))

(defun p2019b3-vector-scale (scalar vector multiply)
  (if (endp vector)
      nil
    (cons
     (p2019b3-binary multiply scalar (car vector))
     (p2019b3-vector-scale
      scalar (cdr vector) multiply))))

(defun p2019b3-matrix-negate (matrix negate)
  (if (endp matrix)
      nil
    (cons
     (p2019b3-vector-negate (car matrix) negate)
     (p2019b3-matrix-negate (cdr matrix) negate))))

(defun p2019b3-matrix-add (left right add)
  (if (or (endp left) (endp right))
      nil
    (cons
     (p2019b3-vector-add (car left) (car right) add)
     (p2019b3-matrix-add (cdr left) (cdr right) add))))

(defun p2019b3-matrix-subtract (left right add negate)
  (p2019b3-matrix-add
   left (p2019b3-matrix-negate right negate) add))

(defun p2019b3-matrix-scale (scalar matrix multiply)
  (if (endp matrix)
      nil
    (cons
     (p2019b3-vector-scale scalar (car matrix) multiply)
     (p2019b3-matrix-scale
      scalar (cdr matrix) multiply))))

(defun p2019b3-matrix-multiply-row
    (row right column count zero add multiply)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     (p2019b3-dot-product
      row
      (p2019b3-matrix-column column right)
      zero add multiply)
     (p2019b3-matrix-multiply-row
      row right (+ 1 column) (- count 1)
      zero add multiply))))

(defun p2019b3-matrix-multiply-rows
    (left right n zero add multiply)
  (if (endp left)
      nil
    (cons
     (p2019b3-matrix-multiply-row
      (car left) right 0 n zero add multiply)
     (p2019b3-matrix-multiply-rows
      (cdr left) right n zero add multiply))))

(defun p2019b3-matrix-multiply
    (left right n zero add multiply)
  (p2019b3-matrix-multiply-rows
   left right n zero add multiply))

(defun p2019b3-identity-row
    (row-index columns zero one)
  (if (endp columns)
      nil
    (cons
     (if (equal row-index (car columns)) one zero)
     (p2019b3-identity-row
      row-index (cdr columns) zero one))))

(defun p2019b3-identity-rows
    (rows columns zero one)
  (if (endp rows)
      nil
    (cons
     (p2019b3-identity-row
      (car rows) columns zero one)
     (p2019b3-identity-rows
      (cdr rows) columns zero one))))

(defun p2019b3-identity-matrix (n zero one)
  (let ((indices (p2019b3-range-from 0 n)))
    (p2019b3-identity-rows
     indices indices zero one)))

(defun p2019b3-outer-product-rows
    (row-scalars vector multiply)
  (if (endp row-scalars)
      nil
    (cons
     (p2019b3-vector-scale
      (car row-scalars) vector multiply)
     (p2019b3-outer-product-rows
      (cdr row-scalars) vector multiply))))

(defun p2019b3-outer-product (vector multiply)
  (p2019b3-outer-product-rows
   vector vector multiply))

(defun p2019b3-reflection-matrix
    (vector n zero one add multiply negate)
  (let ((two (p2019b3-binary add one one)))
    (p2019b3-matrix-subtract
     (p2019b3-identity-matrix n zero one)
     (p2019b3-matrix-scale
      two
      (p2019b3-outer-product vector multiply)
      multiply)
     add negate)))

;; The determinant is the signed Leibniz sum over all permutations.

(defun p2019b3-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (p2019b3-prefix-each item (cdr lists)))))

(defun p2019b3-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons
     (cons item list)
     (p2019b3-prefix-each
      (car list)
      (p2019b3-insert-everywhere item (cdr list))))))

(defun p2019b3-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (p2019b3-insert-everywhere item (car lists))
     (p2019b3-insert-into-each item (cdr lists)))))

(defun p2019b3-permutations (list)
  (if (endp list)
      (list nil)
    (p2019b3-insert-into-each
     (car list)
     (p2019b3-permutations (cdr list)))))

(defun p2019b3-count-greater (item list)
  (if (endp list)
      0
    (+ (if (> item (car list)) 1 0)
       (p2019b3-count-greater item (cdr list)))))

(defun p2019b3-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (p2019b3-count-greater
        (car permutation) (cdr permutation))
       (p2019b3-inversion-count (cdr permutation)))))

(defun p2019b3-diagonal-product
    (matrix permutation row-index one multiply)
  (if (endp permutation)
      one
    (p2019b3-binary
     multiply
     (nth (car permutation) (nth row-index matrix))
     (p2019b3-diagonal-product
      matrix (cdr permutation) (+ 1 row-index)
      one multiply))))

(defun p2019b3-determinant-sum
    (matrix permutations row-one zero add multiply negate)
  (if (endp permutations)
      zero
    (let* ((permutation (car permutations))
           (product
            (p2019b3-diagonal-product
             matrix permutation 0 row-one multiply))
           (signed-product
            (if (evenp
                 (p2019b3-inversion-count permutation))
                product
              (p2019b3-unary negate product))))
      (p2019b3-binary
       add
       signed-product
       (p2019b3-determinant-sum
        matrix (cdr permutations) row-one
        zero add multiply negate)))))

(defun p2019b3-matrix-determinant
    (matrix n zero one add multiply negate)
  (p2019b3-determinant-sum
   matrix
   (p2019b3-permutations
    (p2019b3-range-from 0 n))
   one zero add multiply negate))

(defun putnambench-putnam-2019-b3-statement
    (carrier zero one add multiply negate inverse
             less square-root odd-root n q u p)
  (implies
   (and
    (p2019b3-real-closed-field-p
     carrier zero one add multiply negate inverse
     less square-root odd-root)
    (posp n)
    (p2019b3-matrix-p q n carrier)
    (p2019b3-vector-p u n carrier)
    (p2019b3-matrix-p p n carrier)
    (p2019b3-orthogonal-matrix-p
     q n zero one add multiply)
    (equal
     (p2019b3-dot-product
      u u zero add multiply)
     one)
    (equal
     p
     (p2019b3-reflection-matrix
      u n zero one add multiply negate)))
   (let* ((identity
           (p2019b3-identity-matrix n zero one))
          (q-minus-identity
           (p2019b3-matrix-subtract
            q identity add negate))
          (pq
           (p2019b3-matrix-multiply
            p q n zero add multiply))
          (pq-minus-identity
           (p2019b3-matrix-subtract
            pq identity add negate)))
     (implies
      (not
       (equal
        (p2019b3-matrix-determinant
         q-minus-identity n zero one add multiply negate)
        zero))
      (equal
       (p2019b3-matrix-determinant
        pq-minus-identity n zero one add multiply negate)
       zero)))))

(value-triple :itpeval-statement-checked)
:q
