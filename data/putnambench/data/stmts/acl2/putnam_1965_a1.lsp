;; Statement-only formalization of PutnamBench artifact putnam_1965_a1:
;; a triangle angle determined by two external-angle bisector incidences
;; and equal-length conditions is pi/15. This file contains no proof.
;;
;; Dot products, squared distances, and orientations give an exact
;; semialgebraic presentation of the real-plane geometry. For nonzero rays,
;; angle order is recovered from dot-product signs and squared normalized
;; cosines. If theta = (pi-phi)/2, then
;;
;;   2*cos(theta)^2 - 1 = -cos(phi).
;;
;; Squaring this identity together with the signs of both sides selects the
;; intended principal-angle branch. Finally, t = cos(pi/15)^2 is the unique
;; root above 9/10 of
;;
;;   256*t^4 - 576*t^3 + 416*t^2 - 96*t + 1.
;;
;; Standard ACL2 has no primitive arbitrary-real sort. A rational polynomial
;; and rational isolating interval therefore select one real algebraic
;; generator alpha, and rational polynomials in alpha encode every coordinate.
;; Exact Sturm root counts decide equality and order at alpha.
;; Every finite algebraic-real tuple has a common primitive-element
;; representation. Since this implication and its negation are first-order
;; formulas over real closed fields with rational coefficients, transfer
;; between the real algebraic numbers and the reals makes the encoding
;; bidirectionally equivalent to arbitrary real coordinates.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Polynomials are proper lists of rational coefficients in ascending degree
;; order. The empty list is the zero polynomial.
(defun p1965-rational-polynomial-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (p1965-rational-polynomial-p (cdr polynomial)))
    (equal polynomial nil)))

(defun p1965-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail (p1965-poly-normalize (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun p1965-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (p1965-poly-add (cdr left) (cdr right)))
      left))
   (t right)))

(defun p1965-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (p1965-poly-scale scalar (cdr polynomial)))
    nil))

(defun p1965-poly-negate (polynomial)
  (p1965-poly-scale -1 polynomial))

(defun p1965-poly-subtract (left right)
  (p1965-poly-normalize
   (p1965-poly-add left (p1965-poly-negate right))))

(defun p1965-poly-multiply (left right)
  (if (consp left)
      (p1965-poly-normalize
       (p1965-poly-add
        (p1965-poly-scale (car left) right)
        (cons 0 (p1965-poly-multiply (cdr left) right))))
    nil))

(defun p1965-poly-square (polynomial)
  (p1965-poly-multiply polynomial polynomial))

(defun p1965-poly-derivative-aux (coefficients degree)
  (if (consp coefficients)
      (cons (* degree (car coefficients))
            (p1965-poly-derivative-aux
             (cdr coefficients) (+ degree 1)))
    nil))

(defun p1965-poly-derivative (polynomial)
  (if (consp polynomial)
      (p1965-poly-normalize
       (p1965-poly-derivative-aux (cdr polynomial) 1))
    nil))

(defun p1965-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0 (p1965-zero-list (- count 1)))))

(defun p1965-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append (p1965-zero-list degree) (list coefficient))))

(defun p1965-poly-degree (polynomial)
  (let ((normalized (p1965-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun p1965-poly-leading-coefficient (polynomial)
  (let ((normalized (p1965-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (p1965-poly-degree normalized) normalized)
      0)))

(defun p1965-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons (p1965-poly-normalize quotient)
            (p1965-poly-normalize remainder))
    (let* ((normalized-remainder
            (p1965-poly-normalize remainder))
           (normalized-divisor
            (p1965-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (p1965-poly-degree normalized-remainder)
                 (p1965-poly-degree normalized-divisor)))
          (cons (p1965-poly-normalize quotient)
                normalized-remainder)
        (let* ((degree-difference
                (- (p1965-poly-degree normalized-remainder)
                   (p1965-poly-degree normalized-divisor)))
               (coefficient
                (/ (p1965-poly-leading-coefficient
                    normalized-remainder)
                   (p1965-poly-leading-coefficient
                    normalized-divisor)))
               (term
                (p1965-poly-monomial
                 coefficient degree-difference)))
          (p1965-poly-divmod-steps
           (p1965-poly-subtract
            normalized-remainder
            (p1965-poly-multiply term normalized-divisor))
           normalized-divisor
           (p1965-poly-add quotient term)
           (- steps 1)))))))

(defun p1965-poly-divmod (dividend divisor)
  (p1965-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1 (len (p1965-poly-normalize dividend)))))

(defun p1965-poly-remainder (dividend divisor)
  (cdr (p1965-poly-divmod dividend divisor)))

(defun p1965-poly-gcd-steps (left right steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-left (p1965-poly-normalize left))
        (normalized-right (p1965-poly-normalize right)))
    (if (or (zp steps)
            (not (consp normalized-right)))
        normalized-left
      (p1965-poly-gcd-steps
       normalized-right
       (p1965-poly-remainder normalized-left normalized-right)
       (- steps 1)))))

(defun p1965-poly-gcd (left right)
  (p1965-poly-gcd-steps
   left
   right
   (+ 2
      (len (p1965-poly-normalize left))
      (len (p1965-poly-normalize right)))))

(defun p1965-sturm-tail (previous current steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-current (p1965-poly-normalize current)))
    (if (or (zp steps)
            (not (consp normalized-current)))
        nil
      (cons
       normalized-current
       (p1965-sturm-tail
        normalized-current
        (p1965-poly-negate
         (p1965-poly-remainder previous normalized-current))
        (- steps 1))))))

(defun p1965-sturm-chain (polynomial)
  (let ((normalized (p1965-poly-normalize polynomial)))
    (if (consp normalized)
        (cons
         normalized
         (p1965-sturm-tail
          normalized
          (p1965-poly-derivative normalized)
          (+ 1 (len normalized))))
      nil)))

(defun p1965-poly-evaluate (polynomial value)
  (if (consp polynomial)
      (+ (car polynomial)
         (* value
            (p1965-poly-evaluate (cdr polynomial) value)))
    0))

(defun p1965-chain-values-at (chain value)
  (if (consp chain)
      (cons (p1965-poly-evaluate (car chain) value)
            (p1965-chain-values-at (cdr chain) value))
    nil))

(defun p1965-sign (value)
  (cond
   ((< value 0) -1)
   ((< 0 value) 1)
   (t 0)))

(defun p1965-sign-variations-aux (values previous-sign)
  (if (consp values)
      (let ((current-sign (p1965-sign (car values))))
        (cond
         ((equal current-sign 0)
          (p1965-sign-variations-aux
           (cdr values) previous-sign))
         ((equal previous-sign 0)
          (p1965-sign-variations-aux
           (cdr values) current-sign))
         (t
          (+ (if (equal current-sign previous-sign) 0 1)
             (p1965-sign-variations-aux
              (cdr values) current-sign)))))
    0))

(defun p1965-sign-variations (values)
  (p1965-sign-variations-aux values 0))

(defun p1965-open-root-count (polynomial lower upper)
  (let ((chain (p1965-sturm-chain polynomial)))
    (- (p1965-sign-variations
        (p1965-chain-values-at chain lower))
       (p1965-sign-variations
        (p1965-chain-values-at chain upper)))))

(defun p1965-isolates-one-root-p
    (polynomial lower upper)
  (let ((normalized (p1965-poly-normalize polynomial)))
    (and
     (p1965-rational-polynomial-p normalized)
     (consp normalized)
     (< 0 (p1965-poly-degree normalized))
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not (equal (p1965-poly-evaluate normalized lower) 0))
     (not (equal (p1965-poly-evaluate normalized upper) 0))
     (equal
      (p1965-open-root-count normalized lower upper)
      1))))

(defun p1965-root-free-p (polynomial lower upper)
  (let ((normalized (p1965-poly-normalize polynomial)))
    (and
     (p1965-rational-polynomial-p normalized)
     (consp normalized)
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not (equal (p1965-poly-evaluate normalized lower) 0))
     (not (equal (p1965-poly-evaluate normalized upper) 0))
     (equal
      (p1965-open-root-count normalized lower upper)
      0))))

;; The selected root of primitive is a zero of value exactly when their gcd
;; has the same unique root in the isolating interval.
(defun p1965-zero-at-isolated-root-p
    (primitive value lower upper)
  (let ((normalized-value (p1965-poly-normalize value)))
    (or
     (not (consp normalized-value))
     (p1965-isolates-one-root-p
      (p1965-poly-gcd primitive normalized-value)
      lower
      upper))))

;; A sufficiently refined isolating interval is root-free for every
;; represented polynomial that is nonzero at the selected root.
(defun p1965-sign-decidable-p
    (primitive value lower upper)
  (or
   (p1965-zero-at-isolated-root-p
    primitive value lower upper)
   (p1965-root-free-p value lower upper)))

(defun p1965-sign-at-isolated-root
    (primitive value lower upper)
  (if (p1965-zero-at-isolated-root-p
       primitive value lower upper)
      0
    (p1965-sign (p1965-poly-evaluate value lower))))

(defun p1965-nonnegative-at-isolated-root-p
    (primitive value lower upper)
  (and
   (p1965-sign-decidable-p
    primitive value lower upper)
   (not
    (equal
     (p1965-sign-at-isolated-root
     primitive value lower upper)
     -1))))

(defun p1965-positive-at-isolated-root-p
    (primitive value lower upper)
  (and
   (p1965-sign-decidable-p
    primitive value lower upper)
   (equal
    (p1965-sign-at-isolated-root
     primitive value lower upper)
    1)))

;; A valid isolating interval for the primitive element can still contain an
;; unrelated root of VALUE. Refine the interval before reading VALUE's sign;
;; the unique primitive root in every such subinterval is the same selected
;; algebraic number.
(defun-sk p1965-positive-after-refinement-p
    (primitive value lower upper)
  (exists (refined-lower refined-upper)
    (and
     (rationalp refined-lower)
     (rationalp refined-upper)
     (<= lower refined-lower)
     (< refined-lower refined-upper)
     (<= refined-upper upper)
     (p1965-isolates-one-root-p
      primitive refined-lower refined-upper)
     (p1965-positive-at-isolated-root-p
      primitive value refined-lower refined-upper))))

(defun p1965-negative-at-isolated-root-p
    (primitive value lower upper)
  (and
   (p1965-sign-decidable-p
    primitive value lower upper)
   (equal
    (p1965-sign-at-isolated-root
     primitive value lower upper)
    -1)))

(defun p1965-squared-distance
    (first-x first-y second-x second-y)
  (p1965-poly-add
   (p1965-poly-square
    (p1965-poly-subtract first-x second-x))
   (p1965-poly-square
    (p1965-poly-subtract first-y second-y))))

(defun p1965-angle-dot
    (left-x left-y vertex-x vertex-y right-x right-y)
  (p1965-poly-add
   (p1965-poly-multiply
    (p1965-poly-subtract left-x vertex-x)
    (p1965-poly-subtract right-x vertex-x))
   (p1965-poly-multiply
    (p1965-poly-subtract left-y vertex-y)
    (p1965-poly-subtract right-y vertex-y))))

(defun p1965-angle-scale
    (left-x left-y vertex-x vertex-y right-x right-y)
  (p1965-poly-multiply
   (p1965-squared-distance
    left-x left-y vertex-x vertex-y)
   (p1965-squared-distance
    right-x right-y vertex-x vertex-y)))

(defun p1965-orientation
    (ax ay bx by cx cy)
  (p1965-poly-subtract
   (p1965-poly-multiply
    (p1965-poly-subtract bx ax)
    (p1965-poly-subtract cy ay))
   (p1965-poly-multiply
    (p1965-poly-subtract by ay)
    (p1965-poly-subtract cx ax))))

(defun p1965-geometric-implication-p
    (primitive lower upper
     ax ay bx by cx cy xx xy yx yy)
  (let* ((orientation-abc
          (p1965-orientation ax ay bx by cx cy))
         (a-dot
          (p1965-angle-dot
           cx cy ax ay bx by))
         (a-scale
          (p1965-angle-scale
           cx cy ax ay bx by))
         (c-dot
          (p1965-angle-dot
           bx by cx cy ax ay))
         (c-scale
          (p1965-angle-scale
           bx by cx cy ax ay))
         (b-dot
          (p1965-angle-dot
           ax ay bx by cx cy))
         (b-scale
          (p1965-angle-scale
           ax ay bx by cx cy))
         (a-dot-squared
          (p1965-poly-square a-dot))
         (c-dot-squared
          (p1965-poly-square c-dot))
         (angle-order-difference
          (p1965-poly-subtract
           (p1965-poly-multiply
            a-dot-squared c-scale)
           (p1965-poly-multiply
            c-dot-squared a-scale)))
         (x-collinearity
          (p1965-orientation xx xy bx by cx cy))
         (x-dot
          (p1965-angle-dot
           xx xy ax ay bx by))
         (x-scale
          (p1965-angle-scale
           xx xy ax ay bx by))
         (x-double-angle-defect
          (p1965-poly-subtract
           (p1965-poly-scale
            2 (p1965-poly-square x-dot))
           x-scale))
         (x-half-supplement-sign
          (p1965-poly-multiply
           x-double-angle-defect a-dot))
         (x-half-supplement-equation
          (p1965-poly-subtract
           (p1965-poly-multiply
            (p1965-poly-square
             x-double-angle-defect)
            a-scale)
           (p1965-poly-multiply
            (p1965-poly-square x-scale)
            a-dot-squared)))
         (x-distance-equation
          (p1965-poly-subtract
           (p1965-squared-distance
            ax ay xx xy)
           (p1965-squared-distance
            ax ay bx by)))
         (y-collinearity
          (p1965-orientation yx yy cx cy ax ay))
         (y-dot
          (p1965-angle-dot
           yx yy bx by cx cy))
         (y-scale
          (p1965-angle-scale
           yx yy bx by cx cy))
         (y-double-angle-defect
          (p1965-poly-subtract
           (p1965-poly-scale
            2 (p1965-poly-square y-dot))
           y-scale))
         (y-half-supplement-sign
          (p1965-poly-multiply
           y-double-angle-defect b-dot))
         (y-half-supplement-equation
          (p1965-poly-subtract
           (p1965-poly-multiply
            (p1965-poly-square
             y-double-angle-defect)
            b-scale)
           (p1965-poly-multiply
            (p1965-poly-square y-scale)
            (p1965-poly-square b-dot))))
         (y-distance-equation
          (p1965-poly-subtract
           (p1965-squared-distance
            bx by yx yy)
           (p1965-squared-distance
            ax ay bx by)))
         (a-dot-fourth
          (p1965-poly-square a-dot-squared))
         (a-scale-squared
          (p1965-poly-square a-scale))
         (pi-over-15-isolation
          (p1965-poly-subtract
           (p1965-poly-scale
            10 a-dot-squared)
           (p1965-poly-scale
            9 a-scale)))
         (pi-over-15-equation
          (p1965-poly-add
           (p1965-poly-scale
            256 (p1965-poly-square a-dot-fourth))
           (p1965-poly-add
            (p1965-poly-scale
             -576
             (p1965-poly-multiply
              a-dot-fourth
              (p1965-poly-multiply
               a-dot-squared a-scale)))
            (p1965-poly-add
             (p1965-poly-scale
              416
              (p1965-poly-multiply
               a-dot-fourth a-scale-squared))
             (p1965-poly-add
              (p1965-poly-scale
               -96
               (p1965-poly-multiply
                a-dot-squared
                (p1965-poly-multiply
                 a-scale-squared a-scale)))
              (p1965-poly-square
               a-scale-squared)))))))
    (implies
     (and
      (p1965-isolates-one-root-p
       primitive lower upper)
      (p1965-rational-polynomial-p ax)
      (p1965-rational-polynomial-p ay)
      (p1965-rational-polynomial-p bx)
      (p1965-rational-polynomial-p by)
      (p1965-rational-polynomial-p cx)
      (p1965-rational-polynomial-p cy)
      (p1965-rational-polynomial-p xx)
      (p1965-rational-polynomial-p xy)
      (p1965-rational-polynomial-p yx)
      (p1965-rational-polynomial-p yy)
      (not
       (p1965-zero-at-isolated-root-p
        primitive orientation-abc lower upper))
      (p1965-positive-at-isolated-root-p
       primitive a-dot lower upper)
      (p1965-positive-at-isolated-root-p
       primitive c-dot lower upper)
      (p1965-negative-at-isolated-root-p
       primitive b-dot lower upper)
      (p1965-positive-at-isolated-root-p
       primitive angle-order-difference lower upper)
      (p1965-zero-at-isolated-root-p
       primitive x-collinearity lower upper)
      (p1965-positive-at-isolated-root-p
       primitive x-dot lower upper)
      (p1965-negative-at-isolated-root-p
       primitive
       x-half-supplement-sign
       lower upper)
      (p1965-zero-at-isolated-root-p
       primitive
       x-half-supplement-equation
       lower upper)
      (p1965-zero-at-isolated-root-p
       primitive x-distance-equation lower upper)
      (p1965-zero-at-isolated-root-p
       primitive y-collinearity lower upper)
      (p1965-positive-at-isolated-root-p
       primitive y-dot lower upper)
      (p1965-negative-at-isolated-root-p
       primitive
       y-half-supplement-sign
       lower upper)
      (p1965-zero-at-isolated-root-p
       primitive
       y-half-supplement-equation
       lower upper)
      (p1965-zero-at-isolated-root-p
       primitive y-distance-equation lower upper))
    (and
     (p1965-positive-after-refinement-p
      primitive pi-over-15-isolation lower upper)
     (p1965-zero-at-isolated-root-p
      primitive pi-over-15-equation lower upper)))))

(defun-sk putnambench-putnam-1965-a1-statement ()
  (forall
   (primitive lower upper
    ax ay bx by cx cy xx xy yx yy)
   (p1965-geometric-implication-p
    primitive lower upper
    ax ay bx by cx cy xx xy yx yy)))

(value-triple :itpeval-statement-checked)
:q
