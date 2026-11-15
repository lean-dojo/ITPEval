;; Statement-only formalization of PutnamBench corpus artifact putnam_2009_a3:
;; the determinants of the n-by-n real cosine matrices with entry
;; cos(1+n*i+j), in radians, converge to 0. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Standard ACL2 has exact rational arithmetic rather than primitive real
;; cosine.  The rational pairs below form an unbounded Cauchy approximation
;; to (cos(1),sin(1)).  Exact complex powering then approximates cos(k) for
;; every natural k, so no real value is replaced by a fixed rational sample.

(defun putnam-2009-a3-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-2009-a3-factorial (- n 1)))))

(defun putnam-2009-a3-cosine-one-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (* 2 index))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-2009-a3-cosine-one-prefix index)
         (/ sign
            (putnam-2009-a3-factorial degree))))))

(defun putnam-2009-a3-sine-one-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (+ (* 2 index) 1))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-2009-a3-sine-one-prefix index)
         (/ sign
            (putnam-2009-a3-factorial degree))))))

(defun putnam-2009-a3-complex-multiply (left right)
  (let ((a (car left))
        (b (cdr left))
        (c (car right))
        (d (cdr right)))
    (cons (- (* a c) (* b d))
          (+ (* a d) (* b c)))))

(defun putnam-2009-a3-complex-power (base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (cons 1 0)
    (putnam-2009-a3-complex-multiply
     base
     (putnam-2009-a3-complex-power
      base (- exponent 1)))))

(defun putnam-2009-a3-cosine-integer-prefix
    (integer terms)
  (car
   (putnam-2009-a3-complex-power
    (cons
     (putnam-2009-a3-cosine-one-prefix terms)
     (putnam-2009-a3-sine-one-prefix terms))
    integer)))

;; This precision grows without bound as the rational tolerance tends to zero
;; and also dominates the largest angle, n^2, in the matrix.  The alternating
;; Taylor remainder and continuity of finite products therefore make the
;; rational matrix below a Cauchy name for the source real cosine matrix.
(defun putnam-2009-a3-approximation-terms
    (epsilon n)
  (if (and (rationalp epsilon)
           (< 0 epsilon))
      (+ 1
         (* 2
            (+ (denominator epsilon)
               (* (+ 1 (nfix n))
                  (+ 1 (nfix n))))))
    1))

(defun putnam-2009-a3-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-2009-a3-range-from
           (+ 1 start) (- count 1)))))

(defun putnam-2009-a3-matrix-row
    (n row columns terms)
  (if (endp columns)
      nil
    (cons
     (putnam-2009-a3-cosine-integer-prefix
      (+ 1 (* n row) (car columns))
      terms)
     (putnam-2009-a3-matrix-row
      n row (cdr columns) terms))))

(defun putnam-2009-a3-matrix-rows
    (n rows columns terms)
  (if (endp rows)
      nil
    (cons
     (putnam-2009-a3-matrix-row
      n (car rows) columns terms)
     (putnam-2009-a3-matrix-rows
      n (cdr rows) columns terms))))

(defun putnam-2009-a3-matrix (n terms)
  (let ((indices
         (putnam-2009-a3-range-from 0 n)))
    (putnam-2009-a3-matrix-rows
     n indices indices terms)))

;; The determinant is the full Leibniz signed sum over all permutations.

(defun putnam-2009-a3-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (putnam-2009-a3-prefix-each
           item (cdr lists)))))

(defun putnam-2009-a3-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons
     (cons item list)
     (putnam-2009-a3-prefix-each
      (car list)
      (putnam-2009-a3-insert-everywhere
       item (cdr list))))))

(defun putnam-2009-a3-insert-into-each
    (item lists)
  (if (endp lists)
      nil
    (append
     (putnam-2009-a3-insert-everywhere
      item (car lists))
     (putnam-2009-a3-insert-into-each
      item (cdr lists)))))

(defun putnam-2009-a3-permutations (list)
  (if (endp list)
      (list nil)
    (putnam-2009-a3-insert-into-each
     (car list)
     (putnam-2009-a3-permutations
      (cdr list)))))

(defun putnam-2009-a3-count-greater (item list)
  (if (endp list)
      0
    (+ (if (> item (car list)) 1 0)
       (putnam-2009-a3-count-greater
        item (cdr list)))))

(defun putnam-2009-a3-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (putnam-2009-a3-count-greater
        (car permutation) (cdr permutation))
       (putnam-2009-a3-inversion-count
        (cdr permutation)))))

(defun putnam-2009-a3-diagonal-product
    (matrix permutation row)
  (if (endp permutation)
      1
    (* (nth (car permutation) (nth row matrix))
       (putnam-2009-a3-diagonal-product
        matrix (cdr permutation) (+ 1 row)))))

(defun putnam-2009-a3-determinant-sum
    (matrix permutations)
  (if (endp permutations)
      0
    (let* ((permutation (car permutations))
           (product
            (putnam-2009-a3-diagonal-product
             matrix permutation 0))
           (signed-product
            (if (equal
                 (mod
                  (putnam-2009-a3-inversion-count
                   permutation)
                  2)
                 0)
                product
              (- product))))
      (+ signed-product
         (putnam-2009-a3-determinant-sum
          matrix (cdr permutations))))))

(defun putnam-2009-a3-determinant-prefix
    (n terms)
  (putnam-2009-a3-determinant-sum
   (putnam-2009-a3-matrix n terms)
   (putnam-2009-a3-permutations
    (putnam-2009-a3-range-from 0 n))))

;; The determinant prefixes form a regular-Cauchy name for each source real
;; determinant. The tail predicate separates the requested limit tolerance
;; EPSILON from the independent approximation tolerance ETA. Requiring
;;
;;   |approximation| <= epsilon/2 + eta
;;
;; for every positive ETA implies that the exact determinant has absolute
;; value at most epsilon/2, hence strictly below epsilon. Conversely, ordinary
;; convergence to zero supplies such a tail after shrinking the tolerance.
;; Positive rational tolerances are cofinal among positive real tolerances.

(defun-sk putnam-2009-a3-tail-p (epsilon cutoff)
  (forall
   (n eta)
   (implies
    (and
     (natp n)
     (natp cutoff)
     (<= cutoff n)
     (rationalp eta)
     (< 0 eta))
    (<=
     (abs
      (putnam-2009-a3-determinant-prefix
       n
       (putnam-2009-a3-approximation-terms
        eta n)))
     (+ (/ epsilon 2) eta)))))

(defun-sk putnam-2009-a3-cutoff-exists-p (epsilon)
  (exists
   (cutoff)
   (and
    (natp cutoff)
    (putnam-2009-a3-tail-p epsilon cutoff))))

(defun-sk putnambench-putnam-2009-a3-statement ()
  (forall
   (epsilon)
   (implies
    (and
     (rationalp epsilon)
     (< 0 epsilon))
    (putnam-2009-a3-cutoff-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
