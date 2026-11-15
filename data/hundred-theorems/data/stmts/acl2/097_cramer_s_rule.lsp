;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__097, "Cramer's Rule": for every finite square
;; matrix A and vector b over a commutative unital ring, multiplying A by the
;; vector of determinants obtained by replacing each column of A with b gives
;; det(A) times b.  This is the numerator form of the usual nonzero-determinant
;; solution formula and is expressed by the equivalent generic-matrix identity
;; over an integer polynomial ring.  This file contains no proof.

(in-package "ACL2")

;; Multivariate integer polynomials are sorted lists of
;; (monomial . coefficient) pairs.  A monomial is a sorted list of variable
;; indices, with repetition recording powers.

(defun ht097-monomial-mul (left right)
  (declare (xargs :measure
                  (+ (acl2-count left) (acl2-count right))))
  (cond ((endp left) right)
        ((endp right) left)
        ((<= (car left) (car right))
         (cons (car left)
               (ht097-monomial-mul (cdr left) right)))
        (t
         (cons (car right)
               (ht097-monomial-mul left (cdr right))))))

(defun ht097-poly-insert-term (monomial coefficient polynomial)
  (cond ((equal coefficient 0) polynomial)
        ((endp polynomial)
         (list (cons monomial coefficient)))
        ((equal monomial (caar polynomial))
         (let ((sum (+ coefficient (cdar polynomial))))
           (if (equal sum 0)
               (cdr polynomial)
             (cons (cons monomial sum) (cdr polynomial)))))
        ((lexorder monomial (caar polynomial))
         (cons (cons monomial coefficient) polynomial))
        (t
         (cons (car polynomial)
               (ht097-poly-insert-term monomial coefficient
                                       (cdr polynomial))))))

(defun ht097-poly-add (left right)
  (if (endp left)
      right
    (ht097-poly-add
     (cdr left)
     (ht097-poly-insert-term (caar left) (cdar left) right))))

(defun ht097-poly-neg (polynomial)
  (if (endp polynomial)
      nil
    (cons (cons (caar polynomial) (- (cdar polynomial)))
          (ht097-poly-neg (cdr polynomial)))))

(defun ht097-poly-mul-term (monomial coefficient polynomial)
  (if (endp polynomial)
      nil
    (ht097-poly-insert-term
     (ht097-monomial-mul monomial (caar polynomial))
     (* coefficient (cdar polynomial))
     (ht097-poly-mul-term monomial coefficient (cdr polynomial)))))

(defun ht097-poly-mul (left right)
  (if (endp left)
      nil
    (ht097-poly-add
     (ht097-poly-mul-term (caar left) (cdar left) right)
     (ht097-poly-mul (cdr left) right))))

(defun ht097-poly-one ()
  (list (cons nil 1)))

(defun ht097-poly-variable (index)
  (list (cons (list index) 1)))

;; The generic n-by-n matrix and n-vector have algebraically independent
;; entries.

(defun ht097-range-from (start count)
  (if (zp count)
      nil
    (cons start
          (ht097-range-from (+ 1 start) (- count 1)))))

(defun ht097-generic-row (n row columns)
  (if (endp columns)
      nil
    (cons (ht097-poly-variable
           (+ (* n row) (car columns)))
          (ht097-generic-row n row (cdr columns)))))

(defun ht097-generic-matrix-rows (n rows columns)
  (if (endp rows)
      nil
    (cons (ht097-generic-row n (car rows) columns)
          (ht097-generic-matrix-rows n (cdr rows) columns))))

(defun ht097-generic-matrix (n)
  (let ((indices (ht097-range-from 0 n)))
    (ht097-generic-matrix-rows n indices indices)))

(defun ht097-generic-vector-from (start count)
  (if (zp count)
      nil
    (cons (ht097-poly-variable start)
          (ht097-generic-vector-from (+ 1 start) (- count 1)))))

(defun ht097-generic-vector (n)
  (ht097-generic-vector-from (* n n) n))

;; The determinant is the signed sum over permutations.

(defun ht097-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (ht097-prefix-each item (cdr lists)))))

(defun ht097-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons (cons item list)
          (ht097-prefix-each
           (car list)
           (ht097-insert-everywhere item (cdr list))))))

(defun ht097-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append (ht097-insert-everywhere item (car lists))
            (ht097-insert-into-each item (cdr lists)))))

(defun ht097-permutations (list)
  (if (endp list)
      (list nil)
    (ht097-insert-into-each
     (car list)
     (ht097-permutations (cdr list)))))

(defun ht097-count-greater (item list)
  (if (endp list)
      0
    (+ (if (> item (car list)) 1 0)
       (ht097-count-greater item (cdr list)))))

(defun ht097-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (ht097-count-greater (car permutation) (cdr permutation))
       (ht097-inversion-count (cdr permutation)))))

(defun ht097-diagonal-product (matrix permutation row-index)
  (if (endp permutation)
      (ht097-poly-one)
    (ht097-poly-mul
     (nth (car permutation) (nth row-index matrix))
     (ht097-diagonal-product
      matrix (cdr permutation) (+ 1 row-index)))))

(defun ht097-determinant-sum (matrix permutations)
  (if (endp permutations)
      nil
    (let* ((permutation (car permutations))
           (product
            (ht097-diagonal-product matrix permutation 0))
           (signed-product
            (if (equal (mod (ht097-inversion-count permutation) 2) 0)
                product
              (ht097-poly-neg product))))
      (ht097-poly-add
       signed-product
       (ht097-determinant-sum matrix (cdr permutations))))))

(defun ht097-matrix-det (matrix n)
  (ht097-determinant-sum
   matrix
   (ht097-permutations (ht097-range-from 0 n))))

;; Replacing column k with b produces the kth determinant in Cramer's vector.

(defun ht097-replace-at (index value list)
  (cond ((endp list) nil)
        ((zp index) (cons value (cdr list)))
        (t
         (cons (car list)
               (ht097-replace-at (- index 1) value (cdr list))))))

(defun ht097-replace-column (matrix vector column)
  (if (or (endp matrix) (endp vector))
      nil
    (cons (ht097-replace-at column (car vector) (car matrix))
          (ht097-replace-column
           (cdr matrix) (cdr vector) column))))

(defun ht097-cramer-vector-columns (matrix vector n columns)
  (if (endp columns)
      nil
    (cons (ht097-matrix-det
           (ht097-replace-column matrix vector (car columns))
           n)
          (ht097-cramer-vector-columns
           matrix vector n (cdr columns)))))

(defun ht097-cramer-vector (matrix vector n)
  (ht097-cramer-vector-columns
   matrix vector n (ht097-range-from 0 n)))

;; Matrix-vector multiplication and scalar multiplication use the same
;; polynomial-ring operations.

(defun ht097-poly-dot-product (left right)
  (if (or (endp left) (endp right))
      nil
    (ht097-poly-add
     (ht097-poly-mul (car left) (car right))
     (ht097-poly-dot-product (cdr left) (cdr right)))))

(defun ht097-matrix-vector-mul (matrix vector)
  (if (endp matrix)
      nil
    (cons (ht097-poly-dot-product (car matrix) vector)
          (ht097-matrix-vector-mul (cdr matrix) vector))))

(defun ht097-vector-scale (coefficient vector)
  (if (endp vector)
      nil
    (cons (ht097-poly-mul coefficient (car vector))
          (ht097-vector-scale coefficient (cdr vector)))))

(defun ht097-cramers-rule-statement (n)
  (implies
   (natp n)
   (let* ((matrix (ht097-generic-matrix n))
          (vector (ht097-generic-vector n))
          (determinant (ht097-matrix-det matrix n))
          (cramer-vector (ht097-cramer-vector matrix vector n)))
     (equal
      (ht097-matrix-vector-mul matrix cramer-vector)
      (ht097-vector-scale determinant vector)))))

(value-triple :itpeval-statement-checked)
:q
