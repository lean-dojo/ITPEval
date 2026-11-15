;; Statement-only formalization of PutnamBench corpus artifact putnam_1999_b5:
;; the determinant of the identity plus the n-by-n cosine matrix at equally
;; spaced angles has value 1 - n^2/4. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Let zeta = exp(2*pi*i/n).  It is a primitive n-th root of unity, and
;;
;;   cos((j+k+2)*2*pi/n)
;;     = (zeta^(j+k+2) + zeta^(-(j+k+2)))/2.
;;
;; The polynomial matrix below replaces zeta by X and reduces exponents
;; modulo n using zeta^n = 1.  Its determinant polynomial D_n therefore
;; evaluates at zeta to the source determinant.  Since Phi_n is the minimal
;; polynomial of zeta over the rationals,
;;
;;   D_n(zeta) = 1 - n^2/4
;;
;; holds exactly when Phi_n divides D_n(X) - (1 - n^2/4).  Thus this
;; rational-polynomial encoding is bidirectionally equivalent to the real
;; cosine statement; it does not restrict the source values to rationals.
;; The zero-based rows and columns below correspond to the source indices
;; 1 through n.  The Isabelle index bijection only reorders both matrix axes,
;; which leaves the determinant unchanged.

;; Polynomials are rational coefficient lists in ascending degree order.

(defun putnam-1999-b5-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (putnam-1999-b5-poly-normalize
              (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun putnam-1999-b5-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (putnam-1999-b5-poly-add
               (cdr left) (cdr right)))
      left))
   (t right)))

(defun putnam-1999-b5-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-1999-b5-poly-scale
             scalar (cdr polynomial)))
    nil))

(defun putnam-1999-b5-poly-negate (polynomial)
  (putnam-1999-b5-poly-scale -1 polynomial))

(defun putnam-1999-b5-poly-subtract (left right)
  (putnam-1999-b5-poly-normalize
   (putnam-1999-b5-poly-add
    left
    (putnam-1999-b5-poly-negate right))))

(defun putnam-1999-b5-poly-multiply (left right)
  (if (consp left)
      (putnam-1999-b5-poly-normalize
       (putnam-1999-b5-poly-add
        (putnam-1999-b5-poly-scale (car left) right)
        (cons 0
              (putnam-1999-b5-poly-multiply
               (cdr left) right))))
    nil))

(defun putnam-1999-b5-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (putnam-1999-b5-zero-list (- count 1)))))

(defun putnam-1999-b5-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append
     (putnam-1999-b5-zero-list degree)
     (list coefficient))))

(defun putnam-1999-b5-poly-degree (polynomial)
  (let ((normalized
         (putnam-1999-b5-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun putnam-1999-b5-poly-leading-coefficient (polynomial)
  (let ((normalized
         (putnam-1999-b5-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (putnam-1999-b5-poly-degree normalized)
             normalized)
      0)))

;; The step bound exceeds the number of degree reductions required by
;; polynomial long division with a nonzero divisor.
(defun putnam-1999-b5-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons (putnam-1999-b5-poly-normalize quotient)
            (putnam-1999-b5-poly-normalize remainder))
    (let* ((normalized-remainder
            (putnam-1999-b5-poly-normalize remainder))
           (normalized-divisor
            (putnam-1999-b5-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (putnam-1999-b5-poly-degree
                  normalized-remainder)
                 (putnam-1999-b5-poly-degree
                  normalized-divisor)))
          (cons (putnam-1999-b5-poly-normalize quotient)
                normalized-remainder)
        (let* ((degree-difference
                (- (putnam-1999-b5-poly-degree
                    normalized-remainder)
                   (putnam-1999-b5-poly-degree
                    normalized-divisor)))
               (coefficient
                (/ (putnam-1999-b5-poly-leading-coefficient
                    normalized-remainder)
                   (putnam-1999-b5-poly-leading-coefficient
                    normalized-divisor)))
               (term
                (putnam-1999-b5-poly-monomial
                 coefficient degree-difference)))
          (putnam-1999-b5-poly-divmod-steps
           (putnam-1999-b5-poly-subtract
            normalized-remainder
            (putnam-1999-b5-poly-multiply
             term normalized-divisor))
           normalized-divisor
           (putnam-1999-b5-poly-add quotient term)
           (- steps 1)))))))

(defun putnam-1999-b5-poly-divmod (dividend divisor)
  (putnam-1999-b5-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1
      (len (putnam-1999-b5-poly-normalize dividend)))))

(defun putnam-1999-b5-poly-quotient (dividend divisor)
  (car (putnam-1999-b5-poly-divmod dividend divisor)))

(defun putnam-1999-b5-poly-remainder (dividend divisor)
  (cdr (putnam-1999-b5-poly-divmod dividend divisor)))

(defun putnam-1999-b5-x-to-n-minus-one (n)
  (putnam-1999-b5-poly-add
   (list -1)
   (putnam-1999-b5-poly-monomial 1 n)))

;; The list PRECEDING contains Phi_1 through Phi_(n-1).
(defun putnam-1999-b5-proper-divisor-product
    (n divisor preceding)
  (declare (xargs :measure (nfix divisor)))
  (if (zp divisor)
      (list 1)
    (let ((remaining
           (putnam-1999-b5-proper-divisor-product
            n (- divisor 1) preceding)))
      (if (equal (mod n divisor) 0)
          (putnam-1999-b5-poly-multiply
           (nth (- divisor 1) preceding)
           remaining)
        remaining))))

;; Phi_n = (X^n - 1) / product_(d | n, d < n) Phi_d.
(defun putnam-1999-b5-cyclotomic-list (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (let* ((preceding
            (putnam-1999-b5-cyclotomic-list (- n 1)))
           (proper-divisor-product
            (putnam-1999-b5-proper-divisor-product
             n (- n 1) preceding))
           (phi-n
            (putnam-1999-b5-poly-quotient
             (putnam-1999-b5-x-to-n-minus-one n)
             proper-divisor-product)))
      (append
       preceding
       (list (putnam-1999-b5-poly-normalize phi-n))))))

(defun putnam-1999-b5-cyclotomic-polynomial (n)
  (if (zp n)
      nil
    (nth (- n 1)
         (putnam-1999-b5-cyclotomic-list n))))

(defun putnam-1999-b5-indices (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons (- n 1)
          (putnam-1999-b5-indices (- n 1)))))

(defun putnam-1999-b5-prepend-each (value lists)
  (if (endp lists)
      nil
    (cons
     (cons value (car lists))
     (putnam-1999-b5-prepend-each
      value (cdr lists)))))

(defun putnam-1999-b5-insert-everywhere (value values)
  (if (endp values)
      (list (list value))
    (cons
     (cons value values)
     (putnam-1999-b5-prepend-each
      (car values)
      (putnam-1999-b5-insert-everywhere
       value (cdr values))))))

(defun putnam-1999-b5-insert-into-permutations
    (value permutations)
  (if (endp permutations)
      nil
    (append
     (putnam-1999-b5-insert-everywhere
      value (car permutations))
     (putnam-1999-b5-insert-into-permutations
      value (cdr permutations)))))

(defun putnam-1999-b5-permutations (values)
  (if (endp values)
      (list nil)
    (putnam-1999-b5-insert-into-permutations
     (car values)
     (putnam-1999-b5-permutations (cdr values)))))

(defun putnam-1999-b5-smaller-count (value values)
  (if (endp values)
      0
    (+ (if (< (car values) value) 1 0)
       (putnam-1999-b5-smaller-count
        value (cdr values)))))

(defun putnam-1999-b5-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (putnam-1999-b5-smaller-count
        (car permutation) (cdr permutation))
       (putnam-1999-b5-inversion-count
        (cdr permutation)))))

(defun putnam-1999-b5-permutation-sign (permutation)
  (if (equal
       (mod (putnam-1999-b5-inversion-count permutation) 2)
       0)
      1
    -1))

(defun putnam-1999-b5-entry (n row column)
  (let* ((angle-index (+ row column 2))
         (positive-exponent (mod angle-index n))
         (negative-exponent (mod (- angle-index) n))
         (cosine-polynomial
          (putnam-1999-b5-poly-add
           (putnam-1999-b5-poly-monomial
            1/2 positive-exponent)
           (putnam-1999-b5-poly-monomial
            1/2 negative-exponent))))
    (if (equal row column)
        (putnam-1999-b5-poly-add
         (list 1) cosine-polynomial)
      cosine-polynomial)))

(defun putnam-1999-b5-determinant-product
    (n row permutation)
  (if (endp permutation)
      (list 1)
    (putnam-1999-b5-poly-multiply
     (putnam-1999-b5-entry
      n row (car permutation))
     (putnam-1999-b5-determinant-product
      n (+ row 1) (cdr permutation)))))

(defun putnam-1999-b5-determinant-sum
    (n permutations)
  (if (endp permutations)
      nil
    (putnam-1999-b5-poly-add
     (putnam-1999-b5-poly-scale
      (putnam-1999-b5-permutation-sign
       (car permutations))
      (putnam-1999-b5-determinant-product
       n 0 (car permutations)))
     (putnam-1999-b5-determinant-sum
      n (cdr permutations)))))

(defun putnam-1999-b5-determinant-polynomial (n)
  (putnam-1999-b5-determinant-sum
   n
   (putnam-1999-b5-permutations
    (putnam-1999-b5-indices n))))

(defun putnam-1999-b5-solution (n)
  (- 1 (/ (* n n) 4)))

(defun putnam-1999-b5-equation-polynomial (n)
  (putnam-1999-b5-poly-subtract
   (putnam-1999-b5-determinant-polynomial n)
   (list (putnam-1999-b5-solution n))))

(defun putnambench-putnam-1999-b5-statement (n)
  (implies
   (and (natp n)
        (<= 3 n))
   (equal
    (putnam-1999-b5-poly-remainder
     (putnam-1999-b5-equation-polynomial n)
     (putnam-1999-b5-cyclotomic-polynomial n))
    nil)))

(value-triple :itpeval-statement-checked)
:q
