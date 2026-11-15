;; Statement-only formalization of PutnamBench corpus artifact putnam_1991_a2:
;; no two distinct real square matrices A and B with A^3 = B^3 and
;; A^2*B = B^2*A have A^2+B^2 invertible. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The annotated source answer is False, so its existential statement is
;; equivalently expressed by universally excluding counterexamples. For each
;; fixed positive dimension, a counterexample is an existential first-order
;; formula over real closed fields with rational coefficients: invertibility
;; is equivalent to a nonzero determinant. Hence a real counterexample exists
;; exactly when one exists over the real algebraic numbers.
;;
;; Every finite tuple of real algebraic matrix entries lies in Q(alpha) for
;; one real algebraic alpha. A rational polynomial and rational isolating
;; interval represent alpha, while rational polynomials in alpha represent all
;; entries. The Sturm-Tarski queries below decide equality at alpha exactly.
;; Thus universal closure of the final predicate is bidirectionally equivalent
;; to the arbitrary-real matrix statement, without restricting the dimension
;; or moving an existential matrix witness to an external parameter.

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-1991-a2-rp-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (putnam-1991-a2-rp-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-1991-a2-rp-normalize (polynomial)
  (if (consp polynomial)
      (if (equal (car polynomial) 0)
          (putnam-1991-a2-rp-normalize (cdr polynomial))
        polynomial)
    nil))

(defun putnam-1991-a2-rp-negate (polynomial)
  (if (consp polynomial)
      (cons (- (car polynomial))
            (putnam-1991-a2-rp-negate (cdr polynomial)))
    nil))

(defun putnam-1991-a2-rp-add-raw (left right)
  (declare
   (xargs :measure (+ (acl2-count left) (acl2-count right))))
  (cond
   ((endp left) right)
   ((endp right) left)
   ((< (len left) (len right))
    (cons (car right)
          (putnam-1991-a2-rp-add-raw left (cdr right))))
   ((< (len right) (len left))
    (cons (car left)
          (putnam-1991-a2-rp-add-raw (cdr left) right)))
   (t
    (cons (+ (car left) (car right))
          (putnam-1991-a2-rp-add-raw
           (cdr left) (cdr right))))))

(defun putnam-1991-a2-rp-add (left right)
  (putnam-1991-a2-rp-normalize
   (putnam-1991-a2-rp-add-raw left right)))

(defun putnam-1991-a2-rp-subtract (left right)
  (putnam-1991-a2-rp-add
   left (putnam-1991-a2-rp-negate right)))

(defun putnam-1991-a2-rp-scale (coefficient polynomial)
  (if (consp polynomial)
      (cons (* coefficient (car polynomial))
            (putnam-1991-a2-rp-scale
             coefficient (cdr polynomial)))
    nil))

(defun putnam-1991-a2-zeroes (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0 (putnam-1991-a2-zeroes (- count 1)))))

(defun putnam-1991-a2-rp-scale-shift
    (coefficient polynomial shift)
  (append
   (putnam-1991-a2-rp-scale coefficient polynomial)
   (putnam-1991-a2-zeroes shift)))

(defun putnam-1991-a2-rp-multiply-raw (left right)
  (if (consp left)
      (putnam-1991-a2-rp-add
       (putnam-1991-a2-rp-scale-shift
        (car left) right (len (cdr left)))
       (putnam-1991-a2-rp-multiply-raw (cdr left) right))
    nil))

(defun putnam-1991-a2-rp-multiply (left right)
  (putnam-1991-a2-rp-normalize
   (putnam-1991-a2-rp-multiply-raw left right)))

(defun putnam-1991-a2-rp-eval-aux
    (polynomial x accumulator)
  (if (consp polynomial)
      (putnam-1991-a2-rp-eval-aux
       (cdr polynomial)
       x
       (+ (* accumulator x) (car polynomial)))
    accumulator))

(defun putnam-1991-a2-rp-eval (polynomial x)
  (putnam-1991-a2-rp-eval-aux polynomial x 0))

(defun putnam-1991-a2-rp-derivative-aux
    (polynomial degree)
  (if (consp polynomial)
      (if (zp degree)
          nil
        (cons
         (* degree (car polynomial))
         (putnam-1991-a2-rp-derivative-aux
          (cdr polynomial) (- degree 1))))
    nil))

(defun putnam-1991-a2-rp-derivative (polynomial)
  (let ((normalized
         (putnam-1991-a2-rp-normalize polynomial)))
    (putnam-1991-a2-rp-normalize
     (putnam-1991-a2-rp-derivative-aux
      normalized
      (nfix (- (len normalized) 1))))))

(defun putnam-1991-a2-rp-remainder-fuel
    (left right fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((left (putnam-1991-a2-rp-normalize left))
        (right (putnam-1991-a2-rp-normalize right)))
    (if (or (zp fuel)
            (endp right)
            (< (len left) (len right)))
        left
      (putnam-1991-a2-rp-remainder-fuel
       (putnam-1991-a2-rp-subtract
        left
        (putnam-1991-a2-rp-scale-shift
         (/ (car left) (car right))
         right
         (- (len left) (len right))))
       right
       (- fuel 1)))))

(defun putnam-1991-a2-rp-remainder (left right)
  (putnam-1991-a2-rp-remainder-fuel
   left
   right
   (+ 1 (len (putnam-1991-a2-rp-normalize left)))))

(defun putnam-1991-a2-rp-sturm-tail
    (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current
         (putnam-1991-a2-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-1991-a2-rp-sturm-tail
        current
        (putnam-1991-a2-rp-negate
         (putnam-1991-a2-rp-remainder previous current))
        (- fuel 1))))))

(defun putnam-1991-a2-rp-sturm-sequence
    (polynomial query)
  (let ((polynomial
         (putnam-1991-a2-rp-normalize polynomial))
        (query
         (putnam-1991-a2-rp-normalize query)))
    (if (endp polynomial)
        nil
      (cons
       polynomial
       (if (endp query)
           nil
         (cons
          query
          (putnam-1991-a2-rp-sturm-tail
           polynomial
           query
           (+ 1 (len polynomial) (len query)))))))))

(defun putnam-1991-a2-rational-sign (value)
  (cond ((< value 0) -1)
        ((< 0 value) 1)
        (t 0)))

(defun putnam-1991-a2-rp-variations-aux
    (polynomials x previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-1991-a2-rational-sign
              (putnam-1991-a2-rp-eval
               (car polynomials) x))))
        (if (equal sign 0)
            (putnam-1991-a2-rp-variations-aux
             (cdr polynomials) x previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-1991-a2-rp-variations-aux
              (cdr polynomials) x sign))))
    0))

(defun putnam-1991-a2-rp-variations (polynomials x)
  (putnam-1991-a2-rp-variations-aux
   polynomials x 0))

(defun putnam-1991-a2-rp-cauchy-index
    (polynomial query lower upper)
  (let ((sequence
         (putnam-1991-a2-rp-sturm-sequence
          polynomial query)))
    (- (putnam-1991-a2-rp-variations sequence lower)
       (putnam-1991-a2-rp-variations sequence upper))))

(defun putnam-1991-a2-rp-root-count
    (polynomial lower upper)
  (putnam-1991-a2-rp-cauchy-index
   polynomial
   (putnam-1991-a2-rp-derivative polynomial)
   lower
   upper))

(defun putnam-1991-a2-primitive-p
    (primitive lower upper)
  (and
   (putnam-1991-a2-rp-p primitive)
   (consp (putnam-1991-a2-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not (equal
         (putnam-1991-a2-rp-eval primitive lower)
         0))
   (not (equal
         (putnam-1991-a2-rp-eval primitive upper)
         0))
   (equal
    (putnam-1991-a2-rp-root-count
     primitive lower upper)
    1)
   (not
    (equal
     (putnam-1991-a2-rp-cauchy-index
      primitive
      (putnam-1991-a2-rp-multiply
       (putnam-1991-a2-rp-derivative primitive)
       (putnam-1991-a2-rp-derivative primitive))
      lower
      upper)
     0))))

;; For the unique isolated simple root alpha, this Sturm-Tarski query is the
;; sign of VALUE(alpha).
(defun putnam-1991-a2-algebraic-sign
    (primitive lower upper value)
  (putnam-1991-a2-rp-cauchy-index
   primitive
   (putnam-1991-a2-rp-multiply
    (putnam-1991-a2-rp-derivative primitive)
    value)
   lower
   upper))

(defun putnam-1991-a2-rp-zero-at-alpha-p
    (primitive lower upper value)
  (equal
   (putnam-1991-a2-algebraic-sign
    primitive lower upper value)
   0))

(defun putnam-1991-a2-rp-equal-at-alpha-p
    (primitive lower upper left right)
  (putnam-1991-a2-rp-zero-at-alpha-p
   primitive
   lower
   upper
   (putnam-1991-a2-rp-subtract left right)))

;; Matrices are true lists of N rows, each a true list of N rational
;; polynomials in alpha.

(defun putnam-1991-a2-row-p (row count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (equal row nil)
    (and
     (consp row)
     (putnam-1991-a2-rp-p (car row))
     (putnam-1991-a2-row-p (cdr row) (- count 1)))))

(defun putnam-1991-a2-matrix-p
    (matrix rows columns)
  (declare (xargs :measure (nfix rows)))
  (if (zp rows)
      (equal matrix nil)
    (and
     (consp matrix)
     (putnam-1991-a2-row-p (car matrix) columns)
     (putnam-1991-a2-matrix-p
      (cdr matrix) (- rows 1) columns))))

(defun putnam-1991-a2-row-equal-at-alpha-p
    (primitive lower upper left right)
  (if (consp left)
      (and
       (consp right)
       (putnam-1991-a2-rp-equal-at-alpha-p
        primitive lower upper (car left) (car right))
       (putnam-1991-a2-row-equal-at-alpha-p
        primitive lower upper (cdr left) (cdr right)))
    (equal right nil)))

(defun putnam-1991-a2-matrix-equal-at-alpha-p
    (primitive lower upper left right)
  (if (consp left)
      (and
       (consp right)
       (putnam-1991-a2-row-equal-at-alpha-p
        primitive lower upper (car left) (car right))
       (putnam-1991-a2-matrix-equal-at-alpha-p
        primitive lower upper (cdr left) (cdr right)))
    (equal right nil)))

(defun putnam-1991-a2-row-add (left right)
  (if (consp left)
      (cons
       (putnam-1991-a2-rp-add (car left) (car right))
       (putnam-1991-a2-row-add (cdr left) (cdr right)))
    nil))

(defun putnam-1991-a2-matrix-add (left right)
  (if (consp left)
      (cons
       (putnam-1991-a2-row-add (car left) (car right))
       (putnam-1991-a2-matrix-add
        (cdr left) (cdr right)))
    nil))

(defun putnam-1991-a2-matrix-column
    (column matrix)
  (if (consp matrix)
      (cons
       (nth column (car matrix))
       (putnam-1991-a2-matrix-column
        column (cdr matrix)))
    nil))

(defun putnam-1991-a2-rp-dot-product (left right)
  (if (consp left)
      (putnam-1991-a2-rp-add
       (putnam-1991-a2-rp-multiply
        (car left) (car right))
       (putnam-1991-a2-rp-dot-product
        (cdr left) (cdr right)))
    nil))

(defun putnam-1991-a2-matrix-multiply-row
    (row right column remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (putnam-1991-a2-rp-dot-product
      row
      (putnam-1991-a2-matrix-column column right))
     (putnam-1991-a2-matrix-multiply-row
      row right (+ column 1) (- remaining 1)))))

(defun putnam-1991-a2-matrix-multiply-rows
    (left right n)
  (if (consp left)
      (cons
       (putnam-1991-a2-matrix-multiply-row
        (car left) right 0 n)
       (putnam-1991-a2-matrix-multiply-rows
        (cdr left) right n))
    nil))

(defun putnam-1991-a2-matrix-multiply
    (left right n)
  (putnam-1991-a2-matrix-multiply-rows left right n))

;; The determinant is the signed sum over all column permutations.

(defun putnam-1991-a2-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-1991-a2-range-from
           (+ 1 start) (- count 1)))))

(defun putnam-1991-a2-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (putnam-1991-a2-prefix-each item (cdr lists)))))

(defun putnam-1991-a2-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons (cons item list)
          (putnam-1991-a2-prefix-each
           (car list)
           (putnam-1991-a2-insert-everywhere
            item (cdr list))))))

(defun putnam-1991-a2-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (putnam-1991-a2-insert-everywhere item (car lists))
     (putnam-1991-a2-insert-into-each
      item (cdr lists)))))

(defun putnam-1991-a2-permutations (list)
  (if (endp list)
      (list nil)
    (putnam-1991-a2-insert-into-each
     (car list)
     (putnam-1991-a2-permutations (cdr list)))))

(defun putnam-1991-a2-count-greater (item list)
  (if (endp list)
      0
    (+ (if (> item (car list)) 1 0)
       (putnam-1991-a2-count-greater item (cdr list)))))

(defun putnam-1991-a2-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (putnam-1991-a2-count-greater
        (car permutation) (cdr permutation))
       (putnam-1991-a2-inversion-count
        (cdr permutation)))))

(defun putnam-1991-a2-diagonal-product
    (matrix permutation row)
  (if (endp permutation)
      (list 1)
    (putnam-1991-a2-rp-multiply
     (nth (car permutation) (nth row matrix))
     (putnam-1991-a2-diagonal-product
      matrix (cdr permutation) (+ 1 row)))))

(defun putnam-1991-a2-determinant-sum
    (matrix permutations)
  (if (endp permutations)
      nil
    (let* ((permutation (car permutations))
           (product
            (putnam-1991-a2-diagonal-product
             matrix permutation 0))
           (signed-product
            (if (equal
                 (mod
                  (putnam-1991-a2-inversion-count permutation)
                  2)
                 0)
                product
              (putnam-1991-a2-rp-negate product))))
      (putnam-1991-a2-rp-add
       signed-product
       (putnam-1991-a2-determinant-sum
        matrix (cdr permutations))))))

(defun putnam-1991-a2-determinant (matrix n)
  (putnam-1991-a2-determinant-sum
   matrix
   (putnam-1991-a2-permutations
    (putnam-1991-a2-range-from 0 n))))

(defun putnambench-putnam-1991-a2-statement
    (primitive lower upper n a b)
  (implies
   (and
    (putnam-1991-a2-primitive-p primitive lower upper)
    (posp n)
    (putnam-1991-a2-matrix-p a n n)
    (putnam-1991-a2-matrix-p b n n))
   (let* ((a-squared
           (putnam-1991-a2-matrix-multiply a a n))
          (b-squared
           (putnam-1991-a2-matrix-multiply b b n))
          (a-cubed
           (putnam-1991-a2-matrix-multiply
            a-squared a n))
          (b-cubed
           (putnam-1991-a2-matrix-multiply
            b-squared b n))
          (a-squared-b
           (putnam-1991-a2-matrix-multiply
            a-squared b n))
          (b-squared-a
           (putnam-1991-a2-matrix-multiply
            b-squared a n))
          (sum-of-squares
           (putnam-1991-a2-matrix-add
            a-squared b-squared)))
     (implies
      (and
       (not
        (putnam-1991-a2-matrix-equal-at-alpha-p
         primitive lower upper a b))
       (putnam-1991-a2-matrix-equal-at-alpha-p
        primitive lower upper a-cubed b-cubed)
       (putnam-1991-a2-matrix-equal-at-alpha-p
        primitive lower upper a-squared-b b-squared-a))
      (putnam-1991-a2-rp-zero-at-alpha-p
       primitive
       lower
       upper
       (putnam-1991-a2-determinant sum-of-squares n))))))

(value-triple :itpeval-statement-checked)
:q
