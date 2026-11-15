;; Statement-only formalization of PutnamBench corpus artifact putnam_1978_a2:
;; the determinant of the real matrix with constant entries a above the
;; diagonal, b below it, and entries c_i on the diagonal equals
;; (b*p(a)-a*p(b))/(b-a), where p(x) is the product of c_i-x. This file
;; contains no proof.

(in-package "ACL2")

;; The variables a, b, and c_i are represented by algebraically independent
;; indeterminates in a canonical multivariate integer-polynomial ring.
;; Polynomial equality is therefore equality under every real assignment and
;; does not restrict the source variables to ACL2's rational number domain.
;;
;; Since a differs from b, the source conclusion is equivalent to
;;
;;   (b-a) * det(A) = b*p(a) - a*p(b).
;;
;; At a=b this cleared equation is 0=0. Thus its generic polynomial identity
;; is bidirectionally equivalent to the source's universally quantified
;; implication, including the source assumption a != b.

;; A polynomial is a sorted list of (monomial . coefficient) pairs. A
;; monomial is a sorted list of variable indices, repeated to record powers.

(defun putnam-1978-a2-monomial-multiply (left right)
  (declare (xargs :measure
                  (+ (acl2-count left) (acl2-count right))))
  (cond ((endp left) right)
        ((endp right) left)
        ((<= (car left) (car right))
         (cons (car left)
               (putnam-1978-a2-monomial-multiply
                (cdr left) right)))
        (t
         (cons (car right)
               (putnam-1978-a2-monomial-multiply
                left (cdr right))))))

(defun putnam-1978-a2-polynomial-insert
    (monomial coefficient polynomial)
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
               (putnam-1978-a2-polynomial-insert
                monomial coefficient (cdr polynomial))))))

(defun putnam-1978-a2-polynomial-add (left right)
  (if (endp left)
      right
    (putnam-1978-a2-polynomial-add
     (cdr left)
     (putnam-1978-a2-polynomial-insert
      (caar left) (cdar left) right))))

(defun putnam-1978-a2-polynomial-negate (polynomial)
  (if (endp polynomial)
      nil
    (cons (cons (caar polynomial) (- (cdar polynomial)))
          (putnam-1978-a2-polynomial-negate
           (cdr polynomial)))))

(defun putnam-1978-a2-polynomial-subtract (left right)
  (putnam-1978-a2-polynomial-add
   left
   (putnam-1978-a2-polynomial-negate right)))

(defun putnam-1978-a2-polynomial-multiply-term
    (monomial coefficient polynomial)
  (if (endp polynomial)
      nil
    (putnam-1978-a2-polynomial-insert
     (putnam-1978-a2-monomial-multiply
      monomial (caar polynomial))
     (* coefficient (cdar polynomial))
     (putnam-1978-a2-polynomial-multiply-term
      monomial coefficient (cdr polynomial)))))

(defun putnam-1978-a2-polynomial-multiply (left right)
  (if (endp left)
      nil
    (putnam-1978-a2-polynomial-add
     (putnam-1978-a2-polynomial-multiply-term
      (caar left) (cdar left) right)
     (putnam-1978-a2-polynomial-multiply
      (cdr left) right))))

(defun putnam-1978-a2-polynomial-one ()
  (list (cons nil 1)))

(defun putnam-1978-a2-polynomial-variable (index)
  (list (cons (list index) 1)))

;; Variable 0 is a, variable 1 is b, and variable 2+i is c_i.

(defun putnam-1978-a2-a ()
  (putnam-1978-a2-polynomial-variable 0))

(defun putnam-1978-a2-b ()
  (putnam-1978-a2-polynomial-variable 1))

(defun putnam-1978-a2-c (index)
  (putnam-1978-a2-polynomial-variable (+ 2 index)))

(defun putnam-1978-a2-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-1978-a2-range-from
           (+ 1 start) (- count 1)))))

(defun putnam-1978-a2-matrix-row (row columns)
  (if (endp columns)
      nil
    (cons
     (cond ((< row (car columns))
            (putnam-1978-a2-a))
           ((> row (car columns))
            (putnam-1978-a2-b))
           (t
            (putnam-1978-a2-c row)))
     (putnam-1978-a2-matrix-row row (cdr columns)))))

(defun putnam-1978-a2-matrix-rows (rows columns)
  (if (endp rows)
      nil
    (cons (putnam-1978-a2-matrix-row
           (car rows) columns)
          (putnam-1978-a2-matrix-rows
           (cdr rows) columns))))

(defun putnam-1978-a2-matrix (n)
  (let ((indices (putnam-1978-a2-range-from 0 n)))
    (putnam-1978-a2-matrix-rows indices indices)))

;; The determinant is the signed sum over all permutations of the columns.

(defun putnam-1978-a2-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (putnam-1978-a2-prefix-each item (cdr lists)))))

(defun putnam-1978-a2-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons (cons item list)
          (putnam-1978-a2-prefix-each
           (car list)
           (putnam-1978-a2-insert-everywhere
            item (cdr list))))))

(defun putnam-1978-a2-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (putnam-1978-a2-insert-everywhere item (car lists))
     (putnam-1978-a2-insert-into-each
      item (cdr lists)))))

(defun putnam-1978-a2-permutations (list)
  (if (endp list)
      (list nil)
    (putnam-1978-a2-insert-into-each
     (car list)
     (putnam-1978-a2-permutations (cdr list)))))

(defun putnam-1978-a2-count-greater (item list)
  (if (endp list)
      0
    (+ (if (> item (car list)) 1 0)
       (putnam-1978-a2-count-greater item (cdr list)))))

(defun putnam-1978-a2-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (putnam-1978-a2-count-greater
        (car permutation) (cdr permutation))
       (putnam-1978-a2-inversion-count
        (cdr permutation)))))

(defun putnam-1978-a2-diagonal-product
    (matrix permutation row)
  (if (endp permutation)
      (putnam-1978-a2-polynomial-one)
    (putnam-1978-a2-polynomial-multiply
     (nth (car permutation) (nth row matrix))
     (putnam-1978-a2-diagonal-product
      matrix (cdr permutation) (+ 1 row)))))

(defun putnam-1978-a2-determinant-sum
    (matrix permutations)
  (if (endp permutations)
      nil
    (let* ((permutation (car permutations))
           (product
            (putnam-1978-a2-diagonal-product
             matrix permutation 0))
           (signed-product
            (if (equal
                 (mod
                  (putnam-1978-a2-inversion-count permutation)
                  2)
                 0)
                product
              (putnam-1978-a2-polynomial-negate product))))
      (putnam-1978-a2-polynomial-add
       signed-product
       (putnam-1978-a2-determinant-sum
        matrix (cdr permutations))))))

(defun putnam-1978-a2-determinant (matrix n)
  (putnam-1978-a2-determinant-sum
   matrix
   (putnam-1978-a2-permutations
    (putnam-1978-a2-range-from 0 n))))

;; Compute p(x) = product_i (c_i-x) in the same polynomial ring.

(defun putnam-1978-a2-p-value (x index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (putnam-1978-a2-polynomial-one)
    (putnam-1978-a2-polynomial-multiply
     (putnam-1978-a2-polynomial-subtract
      (putnam-1978-a2-c index) x)
     (putnam-1978-a2-p-value
      x (+ 1 index) (- count 1)))))

(defun putnambench-putnam-1978-a2-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (let* ((a (putnam-1978-a2-a))
          (b (putnam-1978-a2-b))
          (matrix (putnam-1978-a2-matrix n))
          (determinant
           (putnam-1978-a2-determinant matrix n))
          (p-at-a (putnam-1978-a2-p-value a 0 n))
          (p-at-b (putnam-1978-a2-p-value b 0 n)))
     (equal
      (putnam-1978-a2-polynomial-multiply
       (putnam-1978-a2-polynomial-subtract b a)
       determinant)
      (putnam-1978-a2-polynomial-subtract
       (putnam-1978-a2-polynomial-multiply b p-at-a)
       (putnam-1978-a2-polynomial-multiply a p-at-b))))))

(value-triple :itpeval-statement-checked)
:q
