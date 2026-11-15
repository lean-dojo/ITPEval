;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__049, "The Cayley-Hamilton Theorem": the
;; characteristic polynomial of every finite square matrix over a commutative
;; unital ring annihilates the matrix.  This is expressed by the equivalent
;; generic-matrix identity over an integer polynomial ring.  This file contains
;; no proof.

(in-package "ACL2")

;; Multivariate integer polynomials are sorted lists of
;; (monomial . coefficient) pairs.  A monomial is a sorted list of variable
;; indices, with repetition recording powers.

(defun ht049-monomial-mul (left right)
  (declare (xargs :measure
                  (+ (acl2-count left) (acl2-count right))))
  (cond ((endp left) right)
        ((endp right) left)
        ((<= (car left) (car right))
         (cons (car left)
               (ht049-monomial-mul (cdr left) right)))
        (t
         (cons (car right)
               (ht049-monomial-mul left (cdr right))))))

(defun ht049-poly-insert-term (monomial coefficient polynomial)
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
               (ht049-poly-insert-term monomial coefficient
                                       (cdr polynomial))))))

(defun ht049-poly-add (left right)
  (if (endp left)
      right
    (ht049-poly-add
     (cdr left)
     (ht049-poly-insert-term (caar left) (cdar left) right))))

(defun ht049-poly-neg (polynomial)
  (if (endp polynomial)
      nil
    (cons (cons (caar polynomial) (- (cdar polynomial)))
          (ht049-poly-neg (cdr polynomial)))))

(defun ht049-poly-mul-term (monomial coefficient polynomial)
  (if (endp polynomial)
      nil
    (ht049-poly-insert-term
     (ht049-monomial-mul monomial (caar polynomial))
     (* coefficient (cdar polynomial))
     (ht049-poly-mul-term monomial coefficient (cdr polynomial)))))

(defun ht049-poly-mul (left right)
  (if (endp left)
      nil
    (ht049-poly-add
     (ht049-poly-mul-term (caar left) (cdar left) right)
     (ht049-poly-mul (cdr left) right))))

(defun ht049-poly-one ()
  (list (cons nil 1)))

(defun ht049-poly-variable (index)
  (list (cons (list index) 1)))

;; Univariate polynomials in the characteristic indeterminate are coefficient
;; lists in ascending degree; their coefficients are the polynomials above.

(defun ht049-upoly-normalize (coefficients)
  (if (endp coefficients)
      nil
    (let ((tail (ht049-upoly-normalize (cdr coefficients))))
      (if (and (equal (car coefficients) nil)
               (endp tail))
          nil
        (cons (car coefficients) tail)))))

(defun ht049-upoly-add (left right)
  (cond ((endp left) right)
        ((endp right) left)
        (t
         (ht049-upoly-normalize
          (cons (ht049-poly-add (car left) (car right))
                (ht049-upoly-add (cdr left) (cdr right)))))))

(defun ht049-upoly-neg (polynomial)
  (if (endp polynomial)
      nil
    (ht049-upoly-normalize
     (cons (ht049-poly-neg (car polynomial))
           (ht049-upoly-neg (cdr polynomial))))))

(defun ht049-upoly-scale (coefficient polynomial)
  (if (or (equal coefficient nil)
          (endp polynomial))
      nil
    (cons (ht049-poly-mul coefficient (car polynomial))
          (ht049-upoly-scale coefficient (cdr polynomial)))))

(defun ht049-upoly-mul (left right)
  (if (endp left)
      nil
    (let ((tail-product (ht049-upoly-mul (cdr left) right)))
      (ht049-upoly-add
       (ht049-upoly-scale (car left) right)
       (if (endp tail-product)
           nil
         (cons nil tail-product))))))

(defun ht049-upoly-one ()
  (list (ht049-poly-one)))

(defun ht049-upoly-from-entry (entry diagonalp)
  (if diagonalp
      (list (ht049-poly-neg entry) (ht049-poly-one))
    (list (ht049-poly-neg entry))))

;; The generic n-by-n matrix has algebraically independent entries x_(i,j).

(defun ht049-range-from (start count)
  (if (zp count)
      nil
    (cons start
          (ht049-range-from (+ 1 start) (- count 1)))))

(defun ht049-generic-row (n row columns)
  (if (endp columns)
      nil
    (cons (ht049-poly-variable
           (+ (* n row) (car columns)))
          (ht049-generic-row n row (cdr columns)))))

(defun ht049-generic-matrix-rows (n rows columns)
  (if (endp rows)
      nil
    (cons (ht049-generic-row n (car rows) columns)
          (ht049-generic-matrix-rows n (cdr rows) columns))))

(defun ht049-generic-matrix (n)
  (let ((indices (ht049-range-from 0 n)))
    (ht049-generic-matrix-rows n indices indices)))

;; Form tI-X, whose determinant is the characteristic polynomial of X.

(defun ht049-characteristic-row (row row-index column-index)
  (if (endp row)
      nil
    (cons (ht049-upoly-from-entry
           (car row)
           (equal row-index column-index))
          (ht049-characteristic-row
           (cdr row) row-index (+ 1 column-index)))))

(defun ht049-characteristic-matrix-rows (matrix row-index)
  (if (endp matrix)
      nil
    (cons (ht049-characteristic-row (car matrix) row-index 0)
          (ht049-characteristic-matrix-rows
           (cdr matrix) (+ 1 row-index)))))

(defun ht049-characteristic-matrix (matrix)
  (ht049-characteristic-matrix-rows matrix 0))

;; The determinant is the signed sum over permutations.

(defun ht049-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (ht049-prefix-each item (cdr lists)))))

(defun ht049-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons (cons item list)
          (ht049-prefix-each
           (car list)
           (ht049-insert-everywhere item (cdr list))))))

(defun ht049-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append (ht049-insert-everywhere item (car lists))
            (ht049-insert-into-each item (cdr lists)))))

(defun ht049-permutations (list)
  (if (endp list)
      (list nil)
    (ht049-insert-into-each
     (car list)
     (ht049-permutations (cdr list)))))

(defun ht049-count-greater (item list)
  (if (endp list)
      0
    (+ (if (> item (car list)) 1 0)
       (ht049-count-greater item (cdr list)))))

(defun ht049-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (ht049-count-greater (car permutation) (cdr permutation))
       (ht049-inversion-count (cdr permutation)))))

(defun ht049-upoly-diagonal-product (matrix permutation row-index)
  (if (endp permutation)
      (ht049-upoly-one)
    (ht049-upoly-mul
     (nth (car permutation) (nth row-index matrix))
     (ht049-upoly-diagonal-product
      matrix (cdr permutation) (+ 1 row-index)))))

(defun ht049-determinant-sum (matrix permutations)
  (if (endp permutations)
      nil
    (let* ((permutation (car permutations))
           (product
            (ht049-upoly-diagonal-product matrix permutation 0))
           (signed-product
            (if (equal (mod (ht049-inversion-count permutation) 2) 0)
                product
              (ht049-upoly-neg product))))
      (ht049-upoly-add
       signed-product
       (ht049-determinant-sum matrix (cdr permutations))))))

(defun ht049-upoly-matrix-det (matrix n)
  (ht049-determinant-sum
   matrix
   (ht049-permutations (ht049-range-from 0 n))))

;; Matrix arithmetic over the multivariate integer polynomial ring.

(defun ht049-zero-row (n)
  (if (zp n)
      nil
    (cons nil (ht049-zero-row (- n 1)))))

(defun ht049-zero-matrix-rows (n count)
  (if (zp count)
      nil
    (cons (ht049-zero-row n)
          (ht049-zero-matrix-rows n (- count 1)))))

(defun ht049-zero-matrix (n)
  (ht049-zero-matrix-rows n n))

(defun ht049-matrix-add-row (left right)
  (if (endp left)
      nil
    (cons (ht049-poly-add (car left) (car right))
          (ht049-matrix-add-row (cdr left) (cdr right)))))

(defun ht049-matrix-add (left right)
  (if (endp left)
      nil
    (cons (ht049-matrix-add-row (car left) (car right))
          (ht049-matrix-add (cdr left) (cdr right)))))

(defun ht049-matrix-column (column matrix)
  (if (endp matrix)
      nil
    (cons (nth column (car matrix))
          (ht049-matrix-column column (cdr matrix)))))

(defun ht049-poly-dot-product (left right)
  (if (or (endp left) (endp right))
      nil
    (ht049-poly-add
     (ht049-poly-mul (car left) (car right))
     (ht049-poly-dot-product (cdr left) (cdr right)))))

(defun ht049-matrix-mul-row (row right column count)
  (if (zp count)
      nil
    (cons (ht049-poly-dot-product
           row
           (ht049-matrix-column column right))
          (ht049-matrix-mul-row
           row right (+ 1 column) (- count 1)))))

(defun ht049-matrix-mul-rows (left right n)
  (if (endp left)
      nil
    (cons (ht049-matrix-mul-row (car left) right 0 n)
          (ht049-matrix-mul-rows (cdr left) right n))))

(defun ht049-matrix-mul (left right n)
  (ht049-matrix-mul-rows left right n))

(defun ht049-scalar-row (coefficient row column count)
  (if (zp count)
      nil
    (cons (if (equal row column) coefficient nil)
          (ht049-scalar-row
           coefficient row (+ 1 column) (- count 1)))))

(defun ht049-scalar-matrix-rows (coefficient row n count)
  (if (zp count)
      nil
    (cons (ht049-scalar-row coefficient row 0 n)
          (ht049-scalar-matrix-rows
           coefficient (+ 1 row) n (- count 1)))))

(defun ht049-scalar-matrix (coefficient n)
  (ht049-scalar-matrix-rows coefficient 0 n n))

(defun ht049-eval-upoly-at-matrix (coefficients matrix n)
  (if (endp coefficients)
      (ht049-zero-matrix n)
    (ht049-matrix-add
     (ht049-scalar-matrix (car coefficients) n)
     (ht049-matrix-mul
      matrix
      (ht049-eval-upoly-at-matrix (cdr coefficients) matrix n)
      n))))

(defun ht049-cayley-hamilton-statement (n)
  (implies
   (natp n)
   (let* ((matrix (ht049-generic-matrix n))
          (characteristic-polynomial
           (ht049-upoly-matrix-det
            (ht049-characteristic-matrix matrix)
            n)))
     (equal
      (ht049-eval-upoly-at-matrix
       characteristic-polynomial matrix n)
      (ht049-zero-matrix n)))))

(value-triple :itpeval-statement-checked)
:q
