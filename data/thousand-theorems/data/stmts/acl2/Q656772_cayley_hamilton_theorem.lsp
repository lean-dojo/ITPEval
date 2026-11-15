;; Statement-only formalization of thousand-theorems artifact Q656772,
;; "Cayley–Hamilton theorem": the characteristic polynomial of every finite
;; square matrix over a commutative unital ring annihilates the matrix.  This
;; is expressed by the equivalent generic-matrix identity over an integer
;; polynomial ring.  This file contains no proof.

(in-package "ACL2")

;; Multivariate integer polynomials are sorted lists of
;; (monomial . coefficient) pairs.  A monomial is a sorted list of variable
;; indices, with repetition recording powers.

(defun q656772-monomial-mul (left right)
  (declare (xargs :measure
                  (+ (acl2-count left) (acl2-count right))))
  (cond ((endp left) right)
        ((endp right) left)
        ((<= (car left) (car right))
         (cons (car left)
               (q656772-monomial-mul (cdr left) right)))
        (t
         (cons (car right)
               (q656772-monomial-mul left (cdr right))))))

(defun q656772-poly-insert-term (monomial coefficient polynomial)
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
               (q656772-poly-insert-term monomial coefficient
                                       (cdr polynomial))))))

(defun q656772-poly-add (left right)
  (if (endp left)
      right
    (q656772-poly-add
     (cdr left)
     (q656772-poly-insert-term (caar left) (cdar left) right))))

(defun q656772-poly-neg (polynomial)
  (if (endp polynomial)
      nil
    (cons (cons (caar polynomial) (- (cdar polynomial)))
          (q656772-poly-neg (cdr polynomial)))))

(defun q656772-poly-mul-term (monomial coefficient polynomial)
  (if (endp polynomial)
      nil
    (q656772-poly-insert-term
     (q656772-monomial-mul monomial (caar polynomial))
     (* coefficient (cdar polynomial))
     (q656772-poly-mul-term monomial coefficient (cdr polynomial)))))

(defun q656772-poly-mul (left right)
  (if (endp left)
      nil
    (q656772-poly-add
     (q656772-poly-mul-term (caar left) (cdar left) right)
     (q656772-poly-mul (cdr left) right))))

(defun q656772-poly-one ()
  (list (cons nil 1)))

(defun q656772-poly-variable (index)
  (list (cons (list index) 1)))

;; Univariate polynomials in the characteristic indeterminate are coefficient
;; lists in ascending degree; their coefficients are the polynomials above.

(defun q656772-upoly-normalize (coefficients)
  (if (endp coefficients)
      nil
    (let ((tail (q656772-upoly-normalize (cdr coefficients))))
      (if (and (equal (car coefficients) nil)
               (endp tail))
          nil
        (cons (car coefficients) tail)))))

(defun q656772-upoly-add (left right)
  (cond ((endp left) right)
        ((endp right) left)
        (t
         (q656772-upoly-normalize
          (cons (q656772-poly-add (car left) (car right))
                (q656772-upoly-add (cdr left) (cdr right)))))))

(defun q656772-upoly-neg (polynomial)
  (if (endp polynomial)
      nil
    (q656772-upoly-normalize
     (cons (q656772-poly-neg (car polynomial))
           (q656772-upoly-neg (cdr polynomial))))))

(defun q656772-upoly-scale (coefficient polynomial)
  (if (or (equal coefficient nil)
          (endp polynomial))
      nil
    (cons (q656772-poly-mul coefficient (car polynomial))
          (q656772-upoly-scale coefficient (cdr polynomial)))))

(defun q656772-upoly-mul (left right)
  (if (endp left)
      nil
    (let ((tail-product (q656772-upoly-mul (cdr left) right)))
      (q656772-upoly-add
       (q656772-upoly-scale (car left) right)
       (if (endp tail-product)
           nil
         (cons nil tail-product))))))

(defun q656772-upoly-one ()
  (list (q656772-poly-one)))

(defun q656772-upoly-from-entry (entry diagonalp)
  (if diagonalp
      (list (q656772-poly-neg entry) (q656772-poly-one))
    (list (q656772-poly-neg entry))))

;; The generic n-by-n matrix has algebraically independent entries x_(i,j).

(defun q656772-range-from (start count)
  (if (zp count)
      nil
    (cons start
          (q656772-range-from (+ 1 start) (- count 1)))))

(defun q656772-generic-row (n row columns)
  (if (endp columns)
      nil
    (cons (q656772-poly-variable
           (+ (* n row) (car columns)))
          (q656772-generic-row n row (cdr columns)))))

(defun q656772-generic-matrix-rows (n rows columns)
  (if (endp rows)
      nil
    (cons (q656772-generic-row n (car rows) columns)
          (q656772-generic-matrix-rows n (cdr rows) columns))))

(defun q656772-generic-matrix (n)
  (let ((indices (q656772-range-from 0 n)))
    (q656772-generic-matrix-rows n indices indices)))

;; Form tI-X, whose determinant is the characteristic polynomial of X.

(defun q656772-characteristic-row (row row-index column-index)
  (if (endp row)
      nil
    (cons (q656772-upoly-from-entry
           (car row)
           (equal row-index column-index))
          (q656772-characteristic-row
           (cdr row) row-index (+ 1 column-index)))))

(defun q656772-characteristic-matrix-rows (matrix row-index)
  (if (endp matrix)
      nil
    (cons (q656772-characteristic-row (car matrix) row-index 0)
          (q656772-characteristic-matrix-rows
           (cdr matrix) (+ 1 row-index)))))

(defun q656772-characteristic-matrix (matrix)
  (q656772-characteristic-matrix-rows matrix 0))

;; The determinant is the signed sum over permutations.

(defun q656772-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (q656772-prefix-each item (cdr lists)))))

(defun q656772-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons (cons item list)
          (q656772-prefix-each
           (car list)
           (q656772-insert-everywhere item (cdr list))))))

(defun q656772-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append (q656772-insert-everywhere item (car lists))
            (q656772-insert-into-each item (cdr lists)))))

(defun q656772-permutations (list)
  (if (endp list)
      (list nil)
    (q656772-insert-into-each
     (car list)
     (q656772-permutations (cdr list)))))

(defun q656772-count-greater (item list)
  (if (endp list)
      0
    (+ (if (> item (car list)) 1 0)
       (q656772-count-greater item (cdr list)))))

(defun q656772-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (q656772-count-greater (car permutation) (cdr permutation))
       (q656772-inversion-count (cdr permutation)))))

(defun q656772-upoly-diagonal-product (matrix permutation row-index)
  (if (endp permutation)
      (q656772-upoly-one)
    (q656772-upoly-mul
     (nth (car permutation) (nth row-index matrix))
     (q656772-upoly-diagonal-product
      matrix (cdr permutation) (+ 1 row-index)))))

(defun q656772-determinant-sum (matrix permutations)
  (if (endp permutations)
      nil
    (let* ((permutation (car permutations))
           (product
            (q656772-upoly-diagonal-product matrix permutation 0))
           (signed-product
            (if (equal (mod (q656772-inversion-count permutation) 2) 0)
                product
              (q656772-upoly-neg product))))
      (q656772-upoly-add
       signed-product
       (q656772-determinant-sum matrix (cdr permutations))))))

(defun q656772-upoly-matrix-det (matrix n)
  (q656772-determinant-sum
   matrix
   (q656772-permutations (q656772-range-from 0 n))))

;; Matrix arithmetic over the multivariate integer polynomial ring.

(defun q656772-zero-row (n)
  (if (zp n)
      nil
    (cons nil (q656772-zero-row (- n 1)))))

(defun q656772-zero-matrix-rows (n count)
  (if (zp count)
      nil
    (cons (q656772-zero-row n)
          (q656772-zero-matrix-rows n (- count 1)))))

(defun q656772-zero-matrix (n)
  (q656772-zero-matrix-rows n n))

(defun q656772-matrix-add-row (left right)
  (if (endp left)
      nil
    (cons (q656772-poly-add (car left) (car right))
          (q656772-matrix-add-row (cdr left) (cdr right)))))

(defun q656772-matrix-add (left right)
  (if (endp left)
      nil
    (cons (q656772-matrix-add-row (car left) (car right))
          (q656772-matrix-add (cdr left) (cdr right)))))

(defun q656772-matrix-column (column matrix)
  (if (endp matrix)
      nil
    (cons (nth column (car matrix))
          (q656772-matrix-column column (cdr matrix)))))

(defun q656772-poly-dot-product (left right)
  (if (or (endp left) (endp right))
      nil
    (q656772-poly-add
     (q656772-poly-mul (car left) (car right))
     (q656772-poly-dot-product (cdr left) (cdr right)))))

(defun q656772-matrix-mul-row (row right column count)
  (if (zp count)
      nil
    (cons (q656772-poly-dot-product
           row
           (q656772-matrix-column column right))
          (q656772-matrix-mul-row
           row right (+ 1 column) (- count 1)))))

(defun q656772-matrix-mul-rows (left right n)
  (if (endp left)
      nil
    (cons (q656772-matrix-mul-row (car left) right 0 n)
          (q656772-matrix-mul-rows (cdr left) right n))))

(defun q656772-matrix-mul (left right n)
  (q656772-matrix-mul-rows left right n))

(defun q656772-scalar-row (coefficient row column count)
  (if (zp count)
      nil
    (cons (if (equal row column) coefficient nil)
          (q656772-scalar-row
           coefficient row (+ 1 column) (- count 1)))))

(defun q656772-scalar-matrix-rows (coefficient row n count)
  (if (zp count)
      nil
    (cons (q656772-scalar-row coefficient row 0 n)
          (q656772-scalar-matrix-rows
           coefficient (+ 1 row) n (- count 1)))))

(defun q656772-scalar-matrix (coefficient n)
  (q656772-scalar-matrix-rows coefficient 0 n n))

(defun q656772-eval-upoly-at-matrix (coefficients matrix n)
  (if (endp coefficients)
      (q656772-zero-matrix n)
    (q656772-matrix-add
     (q656772-scalar-matrix (car coefficients) n)
     (q656772-matrix-mul
      matrix
      (q656772-eval-upoly-at-matrix (cdr coefficients) matrix n)
      n))))

(defun q656772-cayley-hamilton-statement (n)
  (implies
   (natp n)
   (let* ((matrix (q656772-generic-matrix n))
          (characteristic-polynomial
           (q656772-upoly-matrix-det
            (q656772-characteristic-matrix matrix)
            n)))
     (equal
      (q656772-eval-upoly-at-matrix
       characteristic-polynomial matrix n)
      (q656772-zero-matrix n)))))

(value-triple :itpeval-statement-checked)
:q
