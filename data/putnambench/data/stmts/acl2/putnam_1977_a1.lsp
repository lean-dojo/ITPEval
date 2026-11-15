;; Statement-only formalization of PutnamBench corpus artifact putnam_1977_a1:
;; four distinct points on the real quartic y=2x^4+7x^3+3x-5 that lie on
;; one line have average x-coordinate -7/8. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A rational polynomial and a rational isolating interval represent one real
;; algebraic generator alpha. The four abscissas, slope, and intercept are
;; rational polynomials in alpha. Every finite tuple of real algebraic numbers
;; has such a common primitive representation, and every accepted
;; representation denotes an actual tuple. The source implication and its
;; negation are first-order formulas over real closed fields, so transfer
;; between the reals and the real algebraic numbers makes this encoding
;; equivalent to universal quantification over arbitrary reals.
;;
;; Pairwise inequality encodes a four-element set. For four distinct graph
;; points, collinearity is equivalent to lying on y=slope*x+intercept. Moving
;; that line's existential parameters to universal statement arguments is
;; bidirectionally valid because the conclusion does not depend on them:
;; (exists slope intercept, H) -> C iff
;; (forall slope intercept, H -> C).

(defun putnam-1977-a1-rational-polynomial-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (putnam-1977-a1-rational-polynomial-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-1977-a1-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail (putnam-1977-a1-poly-normalize (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun putnam-1977-a1-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (putnam-1977-a1-poly-add (cdr left) (cdr right)))
      left))
   (t right)))

(defun putnam-1977-a1-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-1977-a1-poly-scale scalar (cdr polynomial)))
    nil))

(defun putnam-1977-a1-poly-negate (polynomial)
  (putnam-1977-a1-poly-scale -1 polynomial))

(defun putnam-1977-a1-poly-subtract (left right)
  (putnam-1977-a1-poly-normalize
   (putnam-1977-a1-poly-add
    left
    (putnam-1977-a1-poly-negate right))))

(defun putnam-1977-a1-poly-multiply (left right)
  (if (consp left)
      (putnam-1977-a1-poly-normalize
       (putnam-1977-a1-poly-add
        (putnam-1977-a1-poly-scale (car left) right)
        (cons 0
              (putnam-1977-a1-poly-multiply (cdr left) right))))
    nil))

(defun putnam-1977-a1-poly-derivative-aux (coefficients degree)
  (if (consp coefficients)
      (cons (* degree (car coefficients))
            (putnam-1977-a1-poly-derivative-aux
             (cdr coefficients) (+ degree 1)))
    nil))

(defun putnam-1977-a1-poly-derivative (polynomial)
  (if (consp polynomial)
      (putnam-1977-a1-poly-normalize
       (putnam-1977-a1-poly-derivative-aux
        (cdr polynomial) 1))
    nil))

(defun putnam-1977-a1-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (putnam-1977-a1-zero-list (- count 1)))))

(defun putnam-1977-a1-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append
     (putnam-1977-a1-zero-list degree)
     (list coefficient))))

(defun putnam-1977-a1-poly-degree (polynomial)
  (let ((normalized (putnam-1977-a1-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun putnam-1977-a1-poly-leading-coefficient (polynomial)
  (let ((normalized (putnam-1977-a1-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (putnam-1977-a1-poly-degree normalized) normalized)
      0)))

(defun putnam-1977-a1-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons
       (putnam-1977-a1-poly-normalize quotient)
       (putnam-1977-a1-poly-normalize remainder))
    (let* ((normalized-remainder
            (putnam-1977-a1-poly-normalize remainder))
           (normalized-divisor
            (putnam-1977-a1-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (putnam-1977-a1-poly-degree normalized-remainder)
                 (putnam-1977-a1-poly-degree normalized-divisor)))
          (cons
           (putnam-1977-a1-poly-normalize quotient)
           normalized-remainder)
        (let* ((degree-difference
                (- (putnam-1977-a1-poly-degree normalized-remainder)
                   (putnam-1977-a1-poly-degree normalized-divisor)))
               (coefficient
                (/ (putnam-1977-a1-poly-leading-coefficient
                    normalized-remainder)
                   (putnam-1977-a1-poly-leading-coefficient
                    normalized-divisor)))
               (term
                (putnam-1977-a1-poly-monomial
                 coefficient degree-difference)))
          (putnam-1977-a1-poly-divmod-steps
           (putnam-1977-a1-poly-subtract
            normalized-remainder
            (putnam-1977-a1-poly-multiply
             term normalized-divisor))
           normalized-divisor
           (putnam-1977-a1-poly-add quotient term)
           (- steps 1)))))))

(defun putnam-1977-a1-poly-divmod (dividend divisor)
  (putnam-1977-a1-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1 (len (putnam-1977-a1-poly-normalize dividend)))))

(defun putnam-1977-a1-poly-remainder (dividend divisor)
  (cdr (putnam-1977-a1-poly-divmod dividend divisor)))

(defun putnam-1977-a1-poly-gcd-steps (left right steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-left (putnam-1977-a1-poly-normalize left))
        (normalized-right (putnam-1977-a1-poly-normalize right)))
    (if (or (zp steps)
            (not (consp normalized-right)))
        normalized-left
      (putnam-1977-a1-poly-gcd-steps
       normalized-right
       (putnam-1977-a1-poly-remainder
        normalized-left normalized-right)
       (- steps 1)))))

(defun putnam-1977-a1-poly-gcd (left right)
  (putnam-1977-a1-poly-gcd-steps
   left
   right
   (+ 2
      (len (putnam-1977-a1-poly-normalize left))
      (len (putnam-1977-a1-poly-normalize right)))))

(defun putnam-1977-a1-sturm-tail (previous current steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-current
         (putnam-1977-a1-poly-normalize current)))
    (if (or (zp steps)
            (not (consp normalized-current)))
        nil
      (cons
       normalized-current
       (putnam-1977-a1-sturm-tail
        normalized-current
        (putnam-1977-a1-poly-negate
         (putnam-1977-a1-poly-remainder
          previous normalized-current))
        (- steps 1))))))

(defun putnam-1977-a1-sturm-chain (polynomial)
  (let ((normalized (putnam-1977-a1-poly-normalize polynomial)))
    (if (consp normalized)
        (cons
         normalized
         (putnam-1977-a1-sturm-tail
          normalized
          (putnam-1977-a1-poly-derivative normalized)
          (+ 1 (len normalized))))
      nil)))

(defun putnam-1977-a1-poly-evaluate (polynomial value)
  (if (consp polynomial)
      (+ (car polynomial)
         (* value
            (putnam-1977-a1-poly-evaluate
             (cdr polynomial) value)))
    0))

(defun putnam-1977-a1-chain-values-at (chain value)
  (if (consp chain)
      (cons
       (putnam-1977-a1-poly-evaluate (car chain) value)
       (putnam-1977-a1-chain-values-at (cdr chain) value))
    nil))

(defun putnam-1977-a1-sign (value)
  (cond
   ((< value 0) -1)
   ((< 0 value) 1)
   (t 0)))

(defun putnam-1977-a1-sign-variations-aux
    (values previous-sign)
  (if (consp values)
      (let ((current-sign (putnam-1977-a1-sign (car values))))
        (cond
         ((equal current-sign 0)
          (putnam-1977-a1-sign-variations-aux
           (cdr values) previous-sign))
         ((equal previous-sign 0)
          (putnam-1977-a1-sign-variations-aux
           (cdr values) current-sign))
         (t
          (+ (if (equal current-sign previous-sign) 0 1)
             (putnam-1977-a1-sign-variations-aux
              (cdr values) current-sign)))))
    0))

(defun putnam-1977-a1-sign-variations (values)
  (putnam-1977-a1-sign-variations-aux values 0))

(defun putnam-1977-a1-open-root-count
    (polynomial lower upper)
  (let ((chain (putnam-1977-a1-sturm-chain polynomial)))
    (- (putnam-1977-a1-sign-variations
        (putnam-1977-a1-chain-values-at chain lower))
       (putnam-1977-a1-sign-variations
        (putnam-1977-a1-chain-values-at chain upper)))))

(defun putnam-1977-a1-isolates-one-root-p
    (polynomial lower upper)
  (let ((normalized (putnam-1977-a1-poly-normalize polynomial)))
    (and
     (putnam-1977-a1-rational-polynomial-p normalized)
     (consp normalized)
     (< 0 (putnam-1977-a1-poly-degree normalized))
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not (equal
           (putnam-1977-a1-poly-evaluate normalized lower)
           0))
     (not (equal
           (putnam-1977-a1-poly-evaluate normalized upper)
           0))
     (equal
      (putnam-1977-a1-open-root-count normalized lower upper)
      1))))

(defun putnam-1977-a1-zero-at-isolated-root-p
    (primitive value lower upper)
  (let ((normalized-value
         (putnam-1977-a1-poly-normalize value)))
    (or
     (not (consp normalized-value))
     (putnam-1977-a1-isolates-one-root-p
      (putnam-1977-a1-poly-gcd primitive normalized-value)
      lower
      upper))))

(defun putnam-1977-a1-quartic-minus-line
    (x slope intercept)
  (let* ((x-squared
          (putnam-1977-a1-poly-multiply x x))
         (x-cubed
          (putnam-1977-a1-poly-multiply x-squared x))
         (x-fourth
          (putnam-1977-a1-poly-multiply x-cubed x))
         (quartic
          (putnam-1977-a1-poly-add
           (putnam-1977-a1-poly-scale 2 x-fourth)
           (putnam-1977-a1-poly-add
            (putnam-1977-a1-poly-scale 7 x-cubed)
            (putnam-1977-a1-poly-add
             (putnam-1977-a1-poly-scale 3 x)
             (list -5))))))
    (putnam-1977-a1-poly-subtract
     quartic
     (putnam-1977-a1-poly-add
      (putnam-1977-a1-poly-multiply slope x)
      intercept))))

(defun putnambench-putnam-1977-a1-statement
    (primitive lower upper x1 x2 x3 x4 slope intercept)
  (let* ((x1-minus-x2
          (putnam-1977-a1-poly-subtract x1 x2))
         (x1-minus-x3
          (putnam-1977-a1-poly-subtract x1 x3))
         (x1-minus-x4
          (putnam-1977-a1-poly-subtract x1 x4))
         (x2-minus-x3
          (putnam-1977-a1-poly-subtract x2 x3))
         (x2-minus-x4
          (putnam-1977-a1-poly-subtract x2 x4))
         (x3-minus-x4
          (putnam-1977-a1-poly-subtract x3 x4))
         (sum-plus-seven-halves
          (putnam-1977-a1-poly-add
           (putnam-1977-a1-poly-add
            (putnam-1977-a1-poly-add x1 x2)
            (putnam-1977-a1-poly-add x3 x4))
           (list 7/2))))
    (implies
     (and
      (putnam-1977-a1-isolates-one-root-p
       primitive lower upper)
      (putnam-1977-a1-rational-polynomial-p x1)
      (putnam-1977-a1-rational-polynomial-p x2)
      (putnam-1977-a1-rational-polynomial-p x3)
      (putnam-1977-a1-rational-polynomial-p x4)
      (putnam-1977-a1-rational-polynomial-p slope)
      (putnam-1977-a1-rational-polynomial-p intercept)
      (not
       (putnam-1977-a1-zero-at-isolated-root-p
        primitive x1-minus-x2 lower upper))
      (not
       (putnam-1977-a1-zero-at-isolated-root-p
        primitive x1-minus-x3 lower upper))
      (not
       (putnam-1977-a1-zero-at-isolated-root-p
        primitive x1-minus-x4 lower upper))
      (not
       (putnam-1977-a1-zero-at-isolated-root-p
        primitive x2-minus-x3 lower upper))
      (not
       (putnam-1977-a1-zero-at-isolated-root-p
        primitive x2-minus-x4 lower upper))
      (not
       (putnam-1977-a1-zero-at-isolated-root-p
        primitive x3-minus-x4 lower upper))
      (putnam-1977-a1-zero-at-isolated-root-p
       primitive
       (putnam-1977-a1-quartic-minus-line x1 slope intercept)
       lower upper)
      (putnam-1977-a1-zero-at-isolated-root-p
       primitive
       (putnam-1977-a1-quartic-minus-line x2 slope intercept)
       lower upper)
      (putnam-1977-a1-zero-at-isolated-root-p
       primitive
       (putnam-1977-a1-quartic-minus-line x3 slope intercept)
       lower upper)
      (putnam-1977-a1-zero-at-isolated-root-p
       primitive
       (putnam-1977-a1-quartic-minus-line x4 slope intercept)
       lower upper))
     (putnam-1977-a1-zero-at-isolated-root-p
      primitive sum-plus-seven-halves lower upper))))

(value-triple :itpeval-statement-checked)
:q
