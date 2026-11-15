;; Statement-only formalization of miniF2F corpus artifact
;; imosl_2007_algebra_p6: a cyclic cubic sum of 100 real terms whose
;; squares sum to one is strictly less than 12/25. This file contains no
;; proof.
;;
;; Rocq states the result for arbitrary real terms, while Lean uses
;; nonnegative reals. These are equivalent: replacing every term by its
;; absolute value preserves the sum of squares and can only increase each
;; summand a_i^2*a_(i+1).
;;
;; Standard ACL2 has exact rational arithmetic but no primitive real sort.
;; The finite real tuple is therefore encoded without restricting it to
;; rationals: an isolating polynomial p and rational interval select one
;; real algebraic number alpha, and each term is a rational polynomial in
;; alpha. Exact Sturm root counts determine equality and order at alpha.
;; Every finite tuple of real algebraic numbers has such a common primitive
;; element representation. Conversely, each valid representation denotes a
;; real tuple. Since the source and its negation are first-order formulas
;; over the real closed field with rational coefficients, real-closed-field
;; transfer says that a real counterexample exists exactly when a real
;; algebraic counterexample exists.

(in-package "ACL2")

;; Polynomials are proper lists of rational coefficients in ascending degree
;; order. The empty list is the zero polynomial.
(defun imosl-2007-algebra-p6-rational-polynomial-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (imosl-2007-algebra-p6-rational-polynomial-p
            (cdr polynomial)))
    (equal polynomial nil)))

(defun imosl-2007-algebra-p6-polynomial-list-p (polynomials)
  (if (consp polynomials)
      (and
       (imosl-2007-algebra-p6-rational-polynomial-p
        (car polynomials))
       (imosl-2007-algebra-p6-polynomial-list-p
        (cdr polynomials)))
    (equal polynomials nil)))

(defun imosl-2007-algebra-p6-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (imosl-2007-algebra-p6-poly-normalize
              (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun imosl-2007-algebra-p6-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (imosl-2007-algebra-p6-poly-add
               (cdr left) (cdr right)))
      left))
   (t right)))

(defun imosl-2007-algebra-p6-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (imosl-2007-algebra-p6-poly-scale
             scalar (cdr polynomial)))
    nil))

(defun imosl-2007-algebra-p6-poly-negate (polynomial)
  (imosl-2007-algebra-p6-poly-scale -1 polynomial))

(defun imosl-2007-algebra-p6-poly-subtract (left right)
  (imosl-2007-algebra-p6-poly-normalize
   (imosl-2007-algebra-p6-poly-add
    left
    (imosl-2007-algebra-p6-poly-negate right))))

(defun imosl-2007-algebra-p6-poly-multiply (left right)
  (if (consp left)
      (imosl-2007-algebra-p6-poly-normalize
       (imosl-2007-algebra-p6-poly-add
        (imosl-2007-algebra-p6-poly-scale
         (car left) right)
        (cons
         0
         (imosl-2007-algebra-p6-poly-multiply
          (cdr left) right))))
    nil))

(defun imosl-2007-algebra-p6-poly-derivative-aux
    (coefficients degree)
  (if (consp coefficients)
      (cons (* degree (car coefficients))
            (imosl-2007-algebra-p6-poly-derivative-aux
             (cdr coefficients) (+ degree 1)))
    nil))

(defun imosl-2007-algebra-p6-poly-derivative (polynomial)
  (if (consp polynomial)
      (imosl-2007-algebra-p6-poly-normalize
       (imosl-2007-algebra-p6-poly-derivative-aux
        (cdr polynomial) 1))
    nil))

(defun imosl-2007-algebra-p6-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (imosl-2007-algebra-p6-zero-list
           (- count 1)))))

(defun imosl-2007-algebra-p6-poly-monomial
    (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append
     (imosl-2007-algebra-p6-zero-list degree)
     (list coefficient))))

(defun imosl-2007-algebra-p6-poly-degree (polynomial)
  (let ((normalized
         (imosl-2007-algebra-p6-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun imosl-2007-algebra-p6-poly-leading-coefficient
    (polynomial)
  (let ((normalized
         (imosl-2007-algebra-p6-poly-normalize polynomial)))
    (if (consp normalized)
        (nth
         (imosl-2007-algebra-p6-poly-degree normalized)
         normalized)
      0)))

;; The step bound makes polynomial long division total in ACL2. Each
;; nonterminal step lowers the degree of the current remainder.
(defun imosl-2007-algebra-p6-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons
       (imosl-2007-algebra-p6-poly-normalize quotient)
       (imosl-2007-algebra-p6-poly-normalize remainder))
    (let* ((normalized-remainder
            (imosl-2007-algebra-p6-poly-normalize
             remainder))
           (normalized-divisor
            (imosl-2007-algebra-p6-poly-normalize
             divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (<
               (imosl-2007-algebra-p6-poly-degree
                normalized-remainder)
               (imosl-2007-algebra-p6-poly-degree
                normalized-divisor)))
          (cons
           (imosl-2007-algebra-p6-poly-normalize quotient)
           normalized-remainder)
        (let* ((degree-difference
                (-
                 (imosl-2007-algebra-p6-poly-degree
                  normalized-remainder)
                 (imosl-2007-algebra-p6-poly-degree
                  normalized-divisor)))
               (coefficient
                (/
                 (imosl-2007-algebra-p6-poly-leading-coefficient
                  normalized-remainder)
                 (imosl-2007-algebra-p6-poly-leading-coefficient
                  normalized-divisor)))
               (term
                (imosl-2007-algebra-p6-poly-monomial
                 coefficient degree-difference)))
          (imosl-2007-algebra-p6-poly-divmod-steps
           (imosl-2007-algebra-p6-poly-subtract
            normalized-remainder
            (imosl-2007-algebra-p6-poly-multiply
             term normalized-divisor))
           normalized-divisor
           (imosl-2007-algebra-p6-poly-add quotient term)
           (- steps 1)))))))

(defun imosl-2007-algebra-p6-poly-divmod
    (dividend divisor)
  (imosl-2007-algebra-p6-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1
      (len
       (imosl-2007-algebra-p6-poly-normalize
        dividend)))))

(defun imosl-2007-algebra-p6-poly-remainder
    (dividend divisor)
  (cdr
   (imosl-2007-algebra-p6-poly-divmod
    dividend divisor)))

(defun imosl-2007-algebra-p6-poly-gcd-steps
    (left right steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-left
         (imosl-2007-algebra-p6-poly-normalize left))
        (normalized-right
         (imosl-2007-algebra-p6-poly-normalize right)))
    (if (or (zp steps)
            (not (consp normalized-right)))
        normalized-left
      (imosl-2007-algebra-p6-poly-gcd-steps
       normalized-right
       (imosl-2007-algebra-p6-poly-remainder
        normalized-left normalized-right)
       (- steps 1)))))

(defun imosl-2007-algebra-p6-poly-gcd (left right)
  (imosl-2007-algebra-p6-poly-gcd-steps
   left
   right
   (+ 2
      (len
       (imosl-2007-algebra-p6-poly-normalize left))
      (len
       (imosl-2007-algebra-p6-poly-normalize right)))))

(defun imosl-2007-algebra-p6-sturm-tail
    (previous current steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-current
         (imosl-2007-algebra-p6-poly-normalize current)))
    (if (or (zp steps)
            (not (consp normalized-current)))
        nil
      (cons
       normalized-current
       (imosl-2007-algebra-p6-sturm-tail
        normalized-current
        (imosl-2007-algebra-p6-poly-negate
         (imosl-2007-algebra-p6-poly-remainder
          previous normalized-current))
        (- steps 1))))))

(defun imosl-2007-algebra-p6-sturm-chain (polynomial)
  (let ((normalized
         (imosl-2007-algebra-p6-poly-normalize polynomial)))
    (if (consp normalized)
        (cons
         normalized
         (imosl-2007-algebra-p6-sturm-tail
          normalized
          (imosl-2007-algebra-p6-poly-derivative normalized)
          (+ 1 (len normalized))))
      nil)))

(defun imosl-2007-algebra-p6-poly-evaluate
    (polynomial value)
  (if (consp polynomial)
      (+ (car polynomial)
         (* value
            (imosl-2007-algebra-p6-poly-evaluate
             (cdr polynomial) value)))
    0))

(defun imosl-2007-algebra-p6-chain-values-at
    (chain value)
  (if (consp chain)
      (cons
       (imosl-2007-algebra-p6-poly-evaluate
        (car chain) value)
       (imosl-2007-algebra-p6-chain-values-at
        (cdr chain) value))
    nil))

(defun imosl-2007-algebra-p6-sign (value)
  (cond
   ((< value 0) -1)
   ((< 0 value) 1)
   (t 0)))

(defun imosl-2007-algebra-p6-sign-variations-aux
    (values previous-sign)
  (if (consp values)
      (let ((current-sign
             (imosl-2007-algebra-p6-sign
              (car values))))
        (cond
         ((equal current-sign 0)
          (imosl-2007-algebra-p6-sign-variations-aux
           (cdr values) previous-sign))
         ((equal previous-sign 0)
          (imosl-2007-algebra-p6-sign-variations-aux
           (cdr values) current-sign))
         (t
          (+
           (if (equal current-sign previous-sign) 0 1)
           (imosl-2007-algebra-p6-sign-variations-aux
            (cdr values) current-sign)))))
    0))

(defun imosl-2007-algebra-p6-sign-variations (values)
  (imosl-2007-algebra-p6-sign-variations-aux
   values 0))

;; The caller separately requires nonzero endpoint values. Under that
;; condition, Sturm's variation difference counts distinct roots in the
;; open interval.
(defun imosl-2007-algebra-p6-open-root-count
    (polynomial lower upper)
  (let ((chain
         (imosl-2007-algebra-p6-sturm-chain
          polynomial)))
    (-
     (imosl-2007-algebra-p6-sign-variations
      (imosl-2007-algebra-p6-chain-values-at
       chain lower))
     (imosl-2007-algebra-p6-sign-variations
      (imosl-2007-algebra-p6-chain-values-at
       chain upper)))))

(defun imosl-2007-algebra-p6-isolates-one-root-p
    (polynomial lower upper)
  (let ((normalized
         (imosl-2007-algebra-p6-poly-normalize
          polynomial)))
    (and
     (imosl-2007-algebra-p6-rational-polynomial-p
      normalized)
     (consp normalized)
     (< 0
        (imosl-2007-algebra-p6-poly-degree
         normalized))
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not
      (equal
       (imosl-2007-algebra-p6-poly-evaluate
        normalized lower)
       0))
     (not
      (equal
       (imosl-2007-algebra-p6-poly-evaluate
        normalized upper)
       0))
     (equal
      (imosl-2007-algebra-p6-open-root-count
       normalized lower upper)
      1))))

(defun imosl-2007-algebra-p6-root-free-p
    (polynomial lower upper)
  (let ((normalized
         (imosl-2007-algebra-p6-poly-normalize
          polynomial)))
    (and
     (imosl-2007-algebra-p6-rational-polynomial-p
      normalized)
     (consp normalized)
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not
      (equal
       (imosl-2007-algebra-p6-poly-evaluate
        normalized lower)
       0))
     (not
      (equal
       (imosl-2007-algebra-p6-poly-evaluate
        normalized upper)
       0))
     (equal
      (imosl-2007-algebra-p6-open-root-count
       normalized lower upper)
      0))))

;; The isolated root of p is a zero of r exactly when gcd(p,r) has its
;; unique interval root there.
(defun imosl-2007-algebra-p6-zero-at-isolated-root-p
    (p r lower upper)
  (let ((normalized-r
         (imosl-2007-algebra-p6-poly-normalize r)))
    (or
     (not (consp normalized-r))
     (imosl-2007-algebra-p6-isolates-one-root-p
      (imosl-2007-algebra-p6-poly-gcd
       p normalized-r)
      lower upper))))

;; If r is not zero at the selected root, a sufficiently refined rational
;; isolating interval contains no root of r. Thus this condition is part of
;; a surjective representation of every finite algebraic-real tuple.
(defun imosl-2007-algebra-p6-sign-decidable-p
    (p r lower upper)
  (or
   (imosl-2007-algebra-p6-zero-at-isolated-root-p
    p r lower upper)
   (imosl-2007-algebra-p6-root-free-p
    r lower upper)))

(defun imosl-2007-algebra-p6-sign-at-isolated-root
    (p r lower upper)
  (if
      (imosl-2007-algebra-p6-zero-at-isolated-root-p
       p r lower upper)
      0
    (imosl-2007-algebra-p6-sign
     (imosl-2007-algebra-p6-poly-evaluate
      r lower))))

(defun imosl-2007-algebra-p6-sum-of-squares
    (coordinates)
  (if (consp coordinates)
      (imosl-2007-algebra-p6-poly-add
       (imosl-2007-algebra-p6-poly-multiply
        (car coordinates)
        (car coordinates))
       (imosl-2007-algebra-p6-sum-of-squares
        (cdr coordinates)))
    nil))

(defun imosl-2007-algebra-p6-chain-cubic-sum
    (coordinates)
  (if (and (consp coordinates)
           (consp (cdr coordinates)))
      (imosl-2007-algebra-p6-poly-add
       (imosl-2007-algebra-p6-poly-multiply
        (imosl-2007-algebra-p6-poly-multiply
         (car coordinates)
         (car coordinates))
        (cadr coordinates))
       (imosl-2007-algebra-p6-chain-cubic-sum
        (cdr coordinates)))
    nil))

(defun imosl-2007-algebra-p6-last-polynomial
    (coordinates)
  (if (and (consp coordinates)
           (consp (cdr coordinates)))
      (imosl-2007-algebra-p6-last-polynomial
       (cdr coordinates))
    (if (consp coordinates)
        (car coordinates)
      nil)))

(defun imosl-2007-algebra-p6-cyclic-cubic-sum
    (coordinates)
  (if (consp coordinates)
      (let ((last
             (imosl-2007-algebra-p6-last-polynomial
              coordinates)))
        (imosl-2007-algebra-p6-poly-add
         (imosl-2007-algebra-p6-chain-cubic-sum
          coordinates)
         (imosl-2007-algebra-p6-poly-multiply
          (imosl-2007-algebra-p6-poly-multiply
           last last)
          (car coordinates))))
    nil))

(defun imosl-2007-algebra-p6-statement
    (isolating-polynomial lower upper coordinates)
  (let* ((sphere-equation
          (imosl-2007-algebra-p6-poly-subtract
           (imosl-2007-algebra-p6-sum-of-squares
            coordinates)
           (list 1)))
         (inequality-gap
          (imosl-2007-algebra-p6-poly-subtract
           (list (/ 12 25))
           (imosl-2007-algebra-p6-cyclic-cubic-sum
            coordinates))))
    (implies
     (and
      (imosl-2007-algebra-p6-isolates-one-root-p
       isolating-polynomial lower upper)
      (imosl-2007-algebra-p6-polynomial-list-p
       coordinates)
      (equal (len coordinates) 100)
      (imosl-2007-algebra-p6-sign-decidable-p
       isolating-polynomial sphere-equation lower upper)
      (imosl-2007-algebra-p6-sign-decidable-p
       isolating-polynomial inequality-gap lower upper)
      (equal
       (imosl-2007-algebra-p6-sign-at-isolated-root
        isolating-polynomial sphere-equation lower upper)
       0))
     (equal
      (imosl-2007-algebra-p6-sign-at-isolated-root
       isolating-polynomial inequality-gap lower upper)
      1))))

(value-triple :itpeval-statement-checked)
:q
