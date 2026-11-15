;; Statement-only formalization of PutnamBench corpus artifact
;; putnam_1966_a2: an inequality relating the side complements of a
;; nondegenerate real Euclidean triangle to its inradius. This file contains
;; no proof.
;;
;; Put x = p-a, y = p-b, and z = p-c. Nondegenerate triangles correspond
;; bidirectionally to x,y,z > 0: their side lengths are y+z, z+x, and x+y.
;; The geometric inradius hypothesis is equivalent to r > 0 together with
;;
;;   r^2 (x+y+z) = xyz.
;;
;; Indeed, the triangle area is r p, while Heron's identity gives area^2 =
;; pxyz; conversely these positive side complements determine a triangle
;; whose positive inradius satisfies the displayed equation. The requested
;; inequality is equivalently
;;
;;   r^2 (y^2 z^2 + z^2 x^2 + x^2 y^2) >= x^2 y^2 z^2,
;;
;; after multiplication by the positive quantity r^2 x^2 y^2 z^2.
;;
;; Standard ACL2 has no primitive real sort. A rational polynomial and a
;; rational isolating interval therefore select one real algebraic number
;; alpha, and x,y,z,r are rational polynomials in alpha. Exact Sturm root
;; counts decide equality and order at alpha. Every finite algebraic-real
;; tuple has such a common primitive-element representation, and every valid
;; representation denotes a real tuple. Since the formula and its negation
;; are first-order formulas over a real closed field, transfer between the
;; reals and the real algebraic numbers makes this encoding bidirectionally
;; equivalent to the arbitrary-real statement, not a rational restriction.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Polynomials are proper lists of rational coefficients in ascending degree
;; order. The empty list is the zero polynomial.
(defun putnam-1966-a2-rational-polynomial-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (putnam-1966-a2-rational-polynomial-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-1966-a2-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail (putnam-1966-a2-poly-normalize (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun putnam-1966-a2-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (putnam-1966-a2-poly-add (cdr left) (cdr right)))
      left))
   (t right)))

(defun putnam-1966-a2-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-1966-a2-poly-scale scalar (cdr polynomial)))
    nil))

(defun putnam-1966-a2-poly-negate (polynomial)
  (putnam-1966-a2-poly-scale -1 polynomial))

(defun putnam-1966-a2-poly-subtract (left right)
  (putnam-1966-a2-poly-normalize
   (putnam-1966-a2-poly-add
    left
    (putnam-1966-a2-poly-negate right))))

(defun putnam-1966-a2-poly-multiply (left right)
  (if (consp left)
      (putnam-1966-a2-poly-normalize
       (putnam-1966-a2-poly-add
        (putnam-1966-a2-poly-scale (car left) right)
        (cons 0
              (putnam-1966-a2-poly-multiply (cdr left) right))))
    nil))

(defun putnam-1966-a2-poly-derivative-aux (coefficients degree)
  (if (consp coefficients)
      (cons (* degree (car coefficients))
            (putnam-1966-a2-poly-derivative-aux
             (cdr coefficients) (+ degree 1)))
    nil))

(defun putnam-1966-a2-poly-derivative (polynomial)
  (if (consp polynomial)
      (putnam-1966-a2-poly-normalize
       (putnam-1966-a2-poly-derivative-aux
        (cdr polynomial) 1))
    nil))

(defun putnam-1966-a2-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (putnam-1966-a2-zero-list (- count 1)))))

(defun putnam-1966-a2-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append
     (putnam-1966-a2-zero-list degree)
     (list coefficient))))

(defun putnam-1966-a2-poly-degree (polynomial)
  (let ((normalized (putnam-1966-a2-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun putnam-1966-a2-poly-leading-coefficient (polynomial)
  (let ((normalized (putnam-1966-a2-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (putnam-1966-a2-poly-degree normalized) normalized)
      0)))

(defun putnam-1966-a2-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons
       (putnam-1966-a2-poly-normalize quotient)
       (putnam-1966-a2-poly-normalize remainder))
    (let* ((normalized-remainder
            (putnam-1966-a2-poly-normalize remainder))
           (normalized-divisor
            (putnam-1966-a2-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (putnam-1966-a2-poly-degree normalized-remainder)
                 (putnam-1966-a2-poly-degree normalized-divisor)))
          (cons
           (putnam-1966-a2-poly-normalize quotient)
           normalized-remainder)
        (let* ((degree-difference
                (- (putnam-1966-a2-poly-degree normalized-remainder)
                   (putnam-1966-a2-poly-degree normalized-divisor)))
               (coefficient
                (/ (putnam-1966-a2-poly-leading-coefficient
                    normalized-remainder)
                   (putnam-1966-a2-poly-leading-coefficient
                    normalized-divisor)))
               (term
                (putnam-1966-a2-poly-monomial
                 coefficient degree-difference)))
          (putnam-1966-a2-poly-divmod-steps
           (putnam-1966-a2-poly-subtract
            normalized-remainder
            (putnam-1966-a2-poly-multiply
             term normalized-divisor))
           normalized-divisor
           (putnam-1966-a2-poly-add quotient term)
           (- steps 1)))))))

(defun putnam-1966-a2-poly-divmod (dividend divisor)
  (putnam-1966-a2-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1 (len (putnam-1966-a2-poly-normalize dividend)))))

(defun putnam-1966-a2-poly-remainder (dividend divisor)
  (cdr (putnam-1966-a2-poly-divmod dividend divisor)))

(defun putnam-1966-a2-poly-gcd-steps (left right steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-left (putnam-1966-a2-poly-normalize left))
        (normalized-right (putnam-1966-a2-poly-normalize right)))
    (if (or (zp steps)
            (not (consp normalized-right)))
        normalized-left
      (putnam-1966-a2-poly-gcd-steps
       normalized-right
       (putnam-1966-a2-poly-remainder
        normalized-left normalized-right)
       (- steps 1)))))

(defun putnam-1966-a2-poly-gcd (left right)
  (putnam-1966-a2-poly-gcd-steps
   left
   right
   (+ 2
      (len (putnam-1966-a2-poly-normalize left))
      (len (putnam-1966-a2-poly-normalize right)))))

(defun putnam-1966-a2-sturm-tail (previous current steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-current
         (putnam-1966-a2-poly-normalize current)))
    (if (or (zp steps)
            (not (consp normalized-current)))
        nil
      (cons
       normalized-current
       (putnam-1966-a2-sturm-tail
        normalized-current
        (putnam-1966-a2-poly-negate
         (putnam-1966-a2-poly-remainder
          previous normalized-current))
        (- steps 1))))))

(defun putnam-1966-a2-sturm-chain (polynomial)
  (let ((normalized (putnam-1966-a2-poly-normalize polynomial)))
    (if (consp normalized)
        (cons
         normalized
         (putnam-1966-a2-sturm-tail
          normalized
          (putnam-1966-a2-poly-derivative normalized)
          (+ 1 (len normalized))))
      nil)))

(defun putnam-1966-a2-poly-evaluate (polynomial value)
  (if (consp polynomial)
      (+ (car polynomial)
         (* value
            (putnam-1966-a2-poly-evaluate
             (cdr polynomial) value)))
    0))

(defun putnam-1966-a2-chain-values-at (chain value)
  (if (consp chain)
      (cons
       (putnam-1966-a2-poly-evaluate (car chain) value)
       (putnam-1966-a2-chain-values-at (cdr chain) value))
    nil))

(defun putnam-1966-a2-sign (value)
  (cond
   ((< value 0) -1)
   ((< 0 value) 1)
   (t 0)))

(defun putnam-1966-a2-sign-variations-aux (values previous-sign)
  (if (consp values)
      (let ((current-sign (putnam-1966-a2-sign (car values))))
        (cond
         ((equal current-sign 0)
          (putnam-1966-a2-sign-variations-aux
           (cdr values) previous-sign))
         ((equal previous-sign 0)
          (putnam-1966-a2-sign-variations-aux
           (cdr values) current-sign))
         (t
          (+ (if (equal current-sign previous-sign) 0 1)
             (putnam-1966-a2-sign-variations-aux
              (cdr values) current-sign)))))
    0))

(defun putnam-1966-a2-sign-variations (values)
  (putnam-1966-a2-sign-variations-aux values 0))

(defun putnam-1966-a2-open-root-count (polynomial lower upper)
  (let ((chain (putnam-1966-a2-sturm-chain polynomial)))
    (- (putnam-1966-a2-sign-variations
        (putnam-1966-a2-chain-values-at chain lower))
       (putnam-1966-a2-sign-variations
        (putnam-1966-a2-chain-values-at chain upper)))))

(defun putnam-1966-a2-isolates-one-root-p
    (polynomial lower upper)
  (let ((normalized (putnam-1966-a2-poly-normalize polynomial)))
    (and
     (putnam-1966-a2-rational-polynomial-p normalized)
     (consp normalized)
     (< 0 (putnam-1966-a2-poly-degree normalized))
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not (equal
           (putnam-1966-a2-poly-evaluate normalized lower)
           0))
     (not (equal
           (putnam-1966-a2-poly-evaluate normalized upper)
           0))
     (equal
      (putnam-1966-a2-open-root-count normalized lower upper)
      1))))

(defun putnam-1966-a2-root-free-p (polynomial lower upper)
  (let ((normalized (putnam-1966-a2-poly-normalize polynomial)))
    (and
     (putnam-1966-a2-rational-polynomial-p normalized)
     (consp normalized)
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not (equal
           (putnam-1966-a2-poly-evaluate normalized lower)
           0))
     (not (equal
           (putnam-1966-a2-poly-evaluate normalized upper)
           0))
     (equal
      (putnam-1966-a2-open-root-count normalized lower upper)
      0))))

(defun putnam-1966-a2-zero-at-isolated-root-p
    (primitive value lower upper)
  (let ((normalized-value
         (putnam-1966-a2-poly-normalize value)))
    (or
     (not (consp normalized-value))
     (putnam-1966-a2-isolates-one-root-p
      (putnam-1966-a2-poly-gcd primitive normalized-value)
      lower
      upper))))

(defun putnam-1966-a2-sign-decidable-p
    (primitive value lower upper)
  (or
   (putnam-1966-a2-zero-at-isolated-root-p
    primitive value lower upper)
   (putnam-1966-a2-root-free-p value lower upper)))

(defun putnam-1966-a2-sign-at-isolated-root
    (primitive value lower upper)
  (if (putnam-1966-a2-zero-at-isolated-root-p
       primitive value lower upper)
      0
    (putnam-1966-a2-sign
     (putnam-1966-a2-poly-evaluate value lower))))

(defun putnam-1966-a2-positive-at-root-p
    (primitive value lower upper)
  (equal
   (putnam-1966-a2-sign-at-isolated-root
    primitive value lower upper)
   1))

(defun putnambench-putnam-1966-a2-statement
    (primitive lower upper x y z r)
  (let* ((x-squared (putnam-1966-a2-poly-multiply x x))
         (y-squared (putnam-1966-a2-poly-multiply y y))
         (z-squared (putnam-1966-a2-poly-multiply z z))
         (r-squared (putnam-1966-a2-poly-multiply r r))
         (x-plus-y-plus-z
          (putnam-1966-a2-poly-add
           x
           (putnam-1966-a2-poly-add y z)))
         (xyz
          (putnam-1966-a2-poly-multiply
           (putnam-1966-a2-poly-multiply x y)
           z))
         (inradius-equation
          (putnam-1966-a2-poly-subtract
           (putnam-1966-a2-poly-multiply
            r-squared x-plus-y-plus-z)
           xyz))
         (pair-square-sum
          (putnam-1966-a2-poly-add
           (putnam-1966-a2-poly-multiply y-squared z-squared)
           (putnam-1966-a2-poly-add
            (putnam-1966-a2-poly-multiply z-squared x-squared)
            (putnam-1966-a2-poly-multiply x-squared y-squared))))
         (inequality-gap
          (putnam-1966-a2-poly-subtract
           (putnam-1966-a2-poly-multiply
            r-squared pair-square-sum)
           (putnam-1966-a2-poly-multiply
            (putnam-1966-a2-poly-multiply x-squared y-squared)
            z-squared))))
    (implies
     (and
      (putnam-1966-a2-isolates-one-root-p
       primitive lower upper)
      (putnam-1966-a2-rational-polynomial-p x)
      (putnam-1966-a2-rational-polynomial-p y)
      (putnam-1966-a2-rational-polynomial-p z)
      (putnam-1966-a2-rational-polynomial-p r)
      (putnam-1966-a2-sign-decidable-p
       primitive x lower upper)
      (putnam-1966-a2-sign-decidable-p
       primitive y lower upper)
      (putnam-1966-a2-sign-decidable-p
       primitive z lower upper)
      (putnam-1966-a2-sign-decidable-p
       primitive r lower upper)
      (putnam-1966-a2-sign-decidable-p
       primitive inradius-equation lower upper)
      (putnam-1966-a2-sign-decidable-p
       primitive inequality-gap lower upper)
      (putnam-1966-a2-positive-at-root-p
       primitive x lower upper)
      (putnam-1966-a2-positive-at-root-p
       primitive y lower upper)
      (putnam-1966-a2-positive-at-root-p
       primitive z lower upper)
      (putnam-1966-a2-positive-at-root-p
       primitive r lower upper)
      (equal
       (putnam-1966-a2-sign-at-isolated-root
        primitive inradius-equation lower upper)
       0))
     (not
      (equal
       (putnam-1966-a2-sign-at-isolated-root
        primitive inequality-gap lower upper)
       -1)))))

(value-triple :itpeval-statement-checked)
:q
