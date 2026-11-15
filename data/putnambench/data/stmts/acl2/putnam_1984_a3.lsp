;; Statement-only formalization of PutnamBench corpus artifact putnam_1984_a3:
;; the punctured real limit of a parity-patterned 2n-by-2n determinant,
;; expressed as the polynomial n^2*(a^2-b^2). This file contains no proof.

(in-package "ACL2")

;; Variables 0, 1, and 2 below are the formal indeterminates A, B, and
;; H = X-A. A monomial is a sorted list of variable indices, with repetition
;; denoting powers. A polynomial is a canonical sorted list of
;; (monomial . rational-coefficient) pairs.
;;
;; For fixed positive n, let D(A,B,H) be the determinant of the source matrix
;; after substituting X=A+H. The source limit is equivalent to saying that
;;
;;   D(A,B,H) - H^(2*n-2) * n^2*(A^2-B^2)
;;
;; has H-order greater than 2*n-2. One direction follows by evaluating the
;; formal identity at arbitrary real A and B. Conversely, if the source limit
;; holds for every real A != B, every coefficient through that H-degree
;; vanishes on the open set A != B and is therefore the zero polynomial.
;; Thus this formal-polynomial encoding is bidirectionally equivalent to the
;; arbitrary-real statement and does not restrict A or B to rational values.

(defun putnam-1984-a3-monomial-multiply (left right)
  (declare (xargs :measure
                  (+ (acl2-count left) (acl2-count right))))
  (cond
   ((endp left) right)
   ((endp right) left)
   ((<= (car left) (car right))
    (cons (car left)
          (putnam-1984-a3-monomial-multiply
           (cdr left) right)))
   (t
    (cons (car right)
          (putnam-1984-a3-monomial-multiply
           left (cdr right))))))

(defun putnam-1984-a3-polynomial-insert
    (monomial coefficient polynomial)
  (cond
   ((equal coefficient 0) polynomial)
   ((endp polynomial)
    (list (cons monomial coefficient)))
   ((equal monomial (caar polynomial))
    (let ((sum (+ coefficient (cdar polynomial))))
      (if (equal sum 0)
          (cdr polynomial)
        (cons (cons monomial sum)
              (cdr polynomial)))))
   ((lexorder monomial (caar polynomial))
    (cons (cons monomial coefficient) polynomial))
   (t
    (cons (car polynomial)
          (putnam-1984-a3-polynomial-insert
           monomial coefficient (cdr polynomial))))))

(defun putnam-1984-a3-polynomial-add (left right)
  (if (endp left)
      right
    (putnam-1984-a3-polynomial-add
     (cdr left)
     (putnam-1984-a3-polynomial-insert
      (caar left) (cdar left) right))))

(defun putnam-1984-a3-polynomial-negate (polynomial)
  (if (endp polynomial)
      nil
    (cons
     (cons (caar polynomial) (- (cdar polynomial)))
     (putnam-1984-a3-polynomial-negate
      (cdr polynomial)))))

(defun putnam-1984-a3-polynomial-subtract (left right)
  (putnam-1984-a3-polynomial-add
   left
   (putnam-1984-a3-polynomial-negate right)))

(defun putnam-1984-a3-polynomial-scale (scalar polynomial)
  (if (or (equal scalar 0)
          (endp polynomial))
      nil
    (cons
     (cons (caar polynomial)
           (* scalar (cdar polynomial)))
     (putnam-1984-a3-polynomial-scale
      scalar (cdr polynomial)))))

(defun putnam-1984-a3-polynomial-multiply-term
    (monomial coefficient polynomial)
  (if (endp polynomial)
      nil
    (putnam-1984-a3-polynomial-insert
     (putnam-1984-a3-monomial-multiply
      monomial (caar polynomial))
     (* coefficient (cdar polynomial))
     (putnam-1984-a3-polynomial-multiply-term
      monomial coefficient (cdr polynomial)))))

(defun putnam-1984-a3-polynomial-multiply (left right)
  (if (endp left)
      nil
    (putnam-1984-a3-polynomial-add
     (putnam-1984-a3-polynomial-multiply-term
      (caar left) (cdar left) right)
     (putnam-1984-a3-polynomial-multiply
      (cdr left) right))))

(defun putnam-1984-a3-polynomial-power (polynomial exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (list (cons nil 1))
    (putnam-1984-a3-polynomial-multiply
     polynomial
     (putnam-1984-a3-polynomial-power
      polynomial (- exponent 1)))))

(defun putnam-1984-a3-polynomial-variable (index)
  (list (cons (list index) 1)))

(defun putnam-1984-a3-indices (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons (- n 1)
          (putnam-1984-a3-indices (- n 1)))))

(defun putnam-1984-a3-prepend-each (value lists)
  (if (endp lists)
      nil
    (cons
     (cons value (car lists))
     (putnam-1984-a3-prepend-each
      value (cdr lists)))))

(defun putnam-1984-a3-insert-everywhere (value values)
  (if (endp values)
      (list (list value))
    (cons
     (cons value values)
     (putnam-1984-a3-prepend-each
      (car values)
      (putnam-1984-a3-insert-everywhere
       value (cdr values))))))

(defun putnam-1984-a3-insert-into-permutations
    (value permutations)
  (if (endp permutations)
      nil
    (append
     (putnam-1984-a3-insert-everywhere
      value (car permutations))
     (putnam-1984-a3-insert-into-permutations
      value (cdr permutations)))))

(defun putnam-1984-a3-permutations (values)
  (if (endp values)
      (list nil)
    (putnam-1984-a3-insert-into-permutations
     (car values)
     (putnam-1984-a3-permutations (cdr values)))))

(defun putnam-1984-a3-smaller-count (value values)
  (if (endp values)
      0
    (+ (if (< (car values) value) 1 0)
       (putnam-1984-a3-smaller-count
        value (cdr values)))))

(defun putnam-1984-a3-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (putnam-1984-a3-smaller-count
        (car permutation) (cdr permutation))
       (putnam-1984-a3-inversion-count
        (cdr permutation)))))

(defun putnam-1984-a3-permutation-sign (permutation)
  (if (equal
       (mod (putnam-1984-a3-inversion-count permutation) 2)
       0)
      1
    -1))

;; Zero-based and one-based indices give the same parity for i+j, so this is
;; definitionally the matrix shared by the Lean and Isabelle sources.
(defun putnam-1984-a3-entry (row column)
  (let ((a (putnam-1984-a3-polynomial-variable 0))
        (b (putnam-1984-a3-polynomial-variable 1))
        (h (putnam-1984-a3-polynomial-variable 2)))
    (if (equal row column)
        (putnam-1984-a3-polynomial-add a h)
      (if (equal (mod (+ row column) 2) 0)
          a
        b))))

(defun putnam-1984-a3-determinant-product
    (row permutation)
  (if (endp permutation)
      (list (cons nil 1))
    (putnam-1984-a3-polynomial-multiply
     (putnam-1984-a3-entry row (car permutation))
     (putnam-1984-a3-determinant-product
      (+ row 1) (cdr permutation)))))

(defun putnam-1984-a3-determinant-sum (permutations)
  (if (endp permutations)
      nil
    (putnam-1984-a3-polynomial-add
     (putnam-1984-a3-polynomial-scale
      (putnam-1984-a3-permutation-sign
       (car permutations))
      (putnam-1984-a3-determinant-product
       0 (car permutations)))
     (putnam-1984-a3-determinant-sum
      (cdr permutations)))))

(defun putnam-1984-a3-determinant (n)
  (putnam-1984-a3-determinant-sum
   (putnam-1984-a3-permutations
    (putnam-1984-a3-indices (* 2 n)))))

(defun putnam-1984-a3-solution (n)
  (let* ((a (putnam-1984-a3-polynomial-variable 0))
         (b (putnam-1984-a3-polynomial-variable 1))
         (a-squared
          (putnam-1984-a3-polynomial-power a 2))
         (b-squared
          (putnam-1984-a3-polynomial-power b 2)))
    (putnam-1984-a3-polynomial-scale
     (* n n)
     (putnam-1984-a3-polynomial-subtract
      a-squared b-squared))))

(defun putnam-1984-a3-h-degree (monomial)
  (if (endp monomial)
      0
    (+ (if (equal (car monomial) 2) 1 0)
       (putnam-1984-a3-h-degree (cdr monomial)))))

(defun putnam-1984-a3-h-order-greater-p
    (polynomial degree)
  (if (endp polynomial)
      t
    (and
     (< degree
        (putnam-1984-a3-h-degree (caar polynomial)))
     (putnam-1984-a3-h-order-greater-p
      (cdr polynomial) degree))))

(defun putnambench-putnam-1984-a3-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (let* ((degree (- (* 2 n) 2))
          (h (putnam-1984-a3-polynomial-variable 2))
          (claimed-leading-term
           (putnam-1984-a3-polynomial-multiply
            (putnam-1984-a3-polynomial-power h degree)
            (putnam-1984-a3-solution n)))
          (remainder
           (putnam-1984-a3-polynomial-subtract
            (putnam-1984-a3-determinant n)
            claimed-leading-term)))
     (putnam-1984-a3-h-order-greater-p
      remainder degree))))

(value-triple :itpeval-statement-checked)
:q
