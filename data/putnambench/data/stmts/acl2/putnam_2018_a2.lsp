;; Statement-only formalization of PutnamBench corpus artifact putnam_2018_a2:
;; the intersection matrix of all nonempty subsets of {1,...,n} has
;; determinant 1 when n=1 and -1 otherwise. This file contains no proof.

(in-package "ACL2")

;; The carrier and each of its subsets use the canonical increasing list
;; representation. Thus a family list is exactly a function on the finite
;; index type in the sources, while membership in the generated powerset is
;; extensional set membership. The source range condition and the prescribed
;; index count make the family an ordering of all nonempty subsets.

(defun putnam-2018-a2-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-2018-a2-range-from
           (+ start 1) (- count 1)))))

(defun putnam-2018-a2-adjoin-to-each (element sets)
  (if (endp sets)
      nil
    (cons (cons element (car sets))
          (putnam-2018-a2-adjoin-to-each
           element (cdr sets)))))

(defun putnam-2018-a2-powerset (carrier)
  (if (endp carrier)
      (list nil)
    (let ((tail-powerset
           (putnam-2018-a2-powerset (cdr carrier))))
      (append
       tail-powerset
       (putnam-2018-a2-adjoin-to-each
        (car carrier) tail-powerset)))))

(defun putnam-2018-a2-delete-empty (sets)
  (if (endp sets)
      nil
    (if (endp (car sets))
        (putnam-2018-a2-delete-empty (cdr sets))
      (cons (car sets)
            (putnam-2018-a2-delete-empty (cdr sets))))))

(defun putnam-2018-a2-subsets-from-powerset-p
    (subsets powerset)
  (if (endp subsets)
      t
    (and
     (member-equal (car subsets) powerset)
     (putnam-2018-a2-subsets-from-powerset-p
      (cdr subsets) powerset))))

(defun putnam-2018-a2-powerset-covered-p
    (powerset subsets)
  (if (endp powerset)
      t
    (and
     (member-equal (car powerset) subsets)
     (putnam-2018-a2-powerset-covered-p
      (cdr powerset) subsets))))

(defun putnam-2018-a2-intersect-p (left right)
  (if (endp left)
      nil
    (or
     (member-equal (car left) right)
     (putnam-2018-a2-intersect-p (cdr left) right))))

(defun putnam-2018-a2-matrix-row-p
    (row left-set subsets)
  (if (endp subsets)
      (equal row nil)
    (and
     (consp row)
     (equal
      (car row)
      (if (putnam-2018-a2-intersect-p
           left-set (car subsets))
          1
        0))
     (putnam-2018-a2-matrix-row-p
      (cdr row) left-set (cdr subsets)))))

(defun putnam-2018-a2-matrix-p
    (matrix row-subsets all-subsets)
  (if (endp row-subsets)
      (equal matrix nil)
    (and
     (consp matrix)
     (putnam-2018-a2-matrix-row-p
      (car matrix) (car row-subsets) all-subsets)
     (putnam-2018-a2-matrix-p
      (cdr matrix) (cdr row-subsets) all-subsets))))

;; The determinant is the exact signed Leibniz sum over all column
;; permutations.

(defun putnam-2018-a2-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (putnam-2018-a2-prefix-each item (cdr lists)))))

(defun putnam-2018-a2-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons
     (cons item list)
     (putnam-2018-a2-prefix-each
      (car list)
      (putnam-2018-a2-insert-everywhere
       item (cdr list))))))

(defun putnam-2018-a2-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (putnam-2018-a2-insert-everywhere item (car lists))
     (putnam-2018-a2-insert-into-each
      item (cdr lists)))))

(defun putnam-2018-a2-permutations (list)
  (if (endp list)
      (list nil)
    (putnam-2018-a2-insert-into-each
     (car list)
     (putnam-2018-a2-permutations (cdr list)))))

(defun putnam-2018-a2-count-greater (item list)
  (if (endp list)
      0
    (+ (if (> item (car list)) 1 0)
       (putnam-2018-a2-count-greater item (cdr list)))))

(defun putnam-2018-a2-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (putnam-2018-a2-count-greater
        (car permutation) (cdr permutation))
       (putnam-2018-a2-inversion-count
        (cdr permutation)))))

(defun putnam-2018-a2-permutation-sign (permutation)
  (if (equal
       (mod (putnam-2018-a2-inversion-count permutation) 2)
       0)
      1
    -1))

(defun putnam-2018-a2-diagonal-product
    (matrix permutation row)
  (if (endp permutation)
      1
    (* (nth (car permutation) (nth row matrix))
       (putnam-2018-a2-diagonal-product
        matrix (cdr permutation) (+ row 1)))))

(defun putnam-2018-a2-determinant-sum
    (matrix permutations)
  (if (endp permutations)
      0
    (+ (* (putnam-2018-a2-permutation-sign
           (car permutations))
          (putnam-2018-a2-diagonal-product
           matrix (car permutations) 0))
       (putnam-2018-a2-determinant-sum
        matrix (cdr permutations)))))

(defun putnam-2018-a2-determinant (matrix dimension)
  (putnam-2018-a2-determinant-sum
   matrix
   (putnam-2018-a2-permutations
    (putnam-2018-a2-range-from 0 dimension))))

(defun putnam-2018-a2-solution (n)
  (if (equal n 1) 1 -1))

(defun putnambench-putnam-2018-a2-statement
    (n subsets matrix)
  (let* ((dimension (- (expt 2 n) 1))
         (carrier (putnam-2018-a2-range-from 1 n))
         (nonempty-powerset
          (putnam-2018-a2-delete-empty
           (putnam-2018-a2-powerset carrier))))
    (implies
     (and
      (natp n)
      (<= 1 n)
      (true-listp subsets)
      (equal (len subsets) dimension)
      (putnam-2018-a2-subsets-from-powerset-p
       subsets nonempty-powerset)
      (putnam-2018-a2-powerset-covered-p
       nonempty-powerset subsets)
      (putnam-2018-a2-matrix-p
       matrix subsets subsets))
     (equal
      (putnam-2018-a2-determinant matrix dimension)
      (putnam-2018-a2-solution n)))))

(value-triple :itpeval-statement-checked)
:q
