;; Statement-only formalization of the hundred-theorems corpus artifact
;; hundred-theorems__acl2__095, "Ptolemy's Theorem": four cyclically ordered
;; points on a circle in the real Euclidean plane satisfy Ptolemy's
;; diagonal-and-side length identity. This file contains no proof.
;;
;; The circle equations, counterclockwise orientations, and a point on both
;; closed diagonals give a polynomial presentation of the source geometry.
;; If X, Y, and Z are respectively the products of the squared diagonal
;; lengths and the two products of squared opposite-side lengths, then
;; sqrt(X) = sqrt(Y) + sqrt(Z) is equivalent to
;;
;;   X - Y - Z >= 0
;;   (X - Y - Z)^2 = 4*Y*Z.
;;
;; Standard ACL2 has no primitive arbitrary-real sort. A rational polynomial
;; and rational isolating interval therefore select one real algebraic
;; generator alpha, and rational polynomials in alpha encode every coordinate
;; and scalar. Exact Sturm root counts decide equality and order at alpha.
;; Every finite algebraic-real tuple has a common primitive-element
;; representation. Since this implication and its negation are first-order
;; formulas over real closed fields with rational coefficients, transfer
;; between the real algebraic numbers and the reals makes the encoding
;; bidirectionally equivalent to arbitrary real coordinates.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Polynomials are proper lists of rational coefficients in ascending degree
;; order. The empty list is the zero polynomial.
(defun ht095-rational-polynomial-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (ht095-rational-polynomial-p (cdr polynomial)))
    (equal polynomial nil)))

(defun ht095-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail (ht095-poly-normalize (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun ht095-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (ht095-poly-add (cdr left) (cdr right)))
      left))
   (t right)))

(defun ht095-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (ht095-poly-scale scalar (cdr polynomial)))
    nil))

(defun ht095-poly-negate (polynomial)
  (ht095-poly-scale -1 polynomial))

(defun ht095-poly-subtract (left right)
  (ht095-poly-normalize
   (ht095-poly-add left (ht095-poly-negate right))))

(defun ht095-poly-multiply (left right)
  (if (consp left)
      (ht095-poly-normalize
       (ht095-poly-add
        (ht095-poly-scale (car left) right)
        (cons 0 (ht095-poly-multiply (cdr left) right))))
    nil))

(defun ht095-poly-square (polynomial)
  (ht095-poly-multiply polynomial polynomial))

(defun ht095-poly-derivative-aux (coefficients degree)
  (if (consp coefficients)
      (cons (* degree (car coefficients))
            (ht095-poly-derivative-aux
             (cdr coefficients) (+ degree 1)))
    nil))

(defun ht095-poly-derivative (polynomial)
  (if (consp polynomial)
      (ht095-poly-normalize
       (ht095-poly-derivative-aux (cdr polynomial) 1))
    nil))

(defun ht095-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0 (ht095-zero-list (- count 1)))))

(defun ht095-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append (ht095-zero-list degree) (list coefficient))))

(defun ht095-poly-degree (polynomial)
  (let ((normalized (ht095-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun ht095-poly-leading-coefficient (polynomial)
  (let ((normalized (ht095-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (ht095-poly-degree normalized) normalized)
      0)))

(defun ht095-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons (ht095-poly-normalize quotient)
            (ht095-poly-normalize remainder))
    (let* ((normalized-remainder
            (ht095-poly-normalize remainder))
           (normalized-divisor
            (ht095-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (ht095-poly-degree normalized-remainder)
                 (ht095-poly-degree normalized-divisor)))
          (cons (ht095-poly-normalize quotient)
                normalized-remainder)
        (let* ((degree-difference
                (- (ht095-poly-degree normalized-remainder)
                   (ht095-poly-degree normalized-divisor)))
               (coefficient
                (/ (ht095-poly-leading-coefficient
                    normalized-remainder)
                   (ht095-poly-leading-coefficient
                    normalized-divisor)))
               (term
                (ht095-poly-monomial
                 coefficient degree-difference)))
          (ht095-poly-divmod-steps
           (ht095-poly-subtract
            normalized-remainder
            (ht095-poly-multiply term normalized-divisor))
           normalized-divisor
           (ht095-poly-add quotient term)
           (- steps 1)))))))

(defun ht095-poly-divmod (dividend divisor)
  (ht095-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1 (len (ht095-poly-normalize dividend)))))

(defun ht095-poly-remainder (dividend divisor)
  (cdr (ht095-poly-divmod dividend divisor)))

(defun ht095-poly-gcd-steps (left right steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-left (ht095-poly-normalize left))
        (normalized-right (ht095-poly-normalize right)))
    (if (or (zp steps)
            (not (consp normalized-right)))
        normalized-left
      (ht095-poly-gcd-steps
       normalized-right
       (ht095-poly-remainder normalized-left normalized-right)
       (- steps 1)))))

(defun ht095-poly-gcd (left right)
  (ht095-poly-gcd-steps
   left
   right
   (+ 2
      (len (ht095-poly-normalize left))
      (len (ht095-poly-normalize right)))))

(defun ht095-sturm-tail (previous current steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-current (ht095-poly-normalize current)))
    (if (or (zp steps)
            (not (consp normalized-current)))
        nil
      (cons
       normalized-current
       (ht095-sturm-tail
        normalized-current
        (ht095-poly-negate
         (ht095-poly-remainder previous normalized-current))
        (- steps 1))))))

(defun ht095-sturm-chain (polynomial)
  (let ((normalized (ht095-poly-normalize polynomial)))
    (if (consp normalized)
        (cons
         normalized
         (ht095-sturm-tail
          normalized
          (ht095-poly-derivative normalized)
          (+ 1 (len normalized))))
      nil)))

(defun ht095-poly-evaluate (polynomial value)
  (if (consp polynomial)
      (+ (car polynomial)
         (* value
            (ht095-poly-evaluate (cdr polynomial) value)))
    0))

(defun ht095-chain-values-at (chain value)
  (if (consp chain)
      (cons (ht095-poly-evaluate (car chain) value)
            (ht095-chain-values-at (cdr chain) value))
    nil))

(defun ht095-sign (value)
  (cond
   ((< value 0) -1)
   ((< 0 value) 1)
   (t 0)))

(defun ht095-sign-variations-aux (values previous-sign)
  (if (consp values)
      (let ((current-sign (ht095-sign (car values))))
        (cond
         ((equal current-sign 0)
          (ht095-sign-variations-aux
           (cdr values) previous-sign))
         ((equal previous-sign 0)
          (ht095-sign-variations-aux
           (cdr values) current-sign))
         (t
          (+ (if (equal current-sign previous-sign) 0 1)
             (ht095-sign-variations-aux
              (cdr values) current-sign)))))
    0))

(defun ht095-sign-variations (values)
  (ht095-sign-variations-aux values 0))

(defun ht095-open-root-count (polynomial lower upper)
  (let ((chain (ht095-sturm-chain polynomial)))
    (- (ht095-sign-variations
        (ht095-chain-values-at chain lower))
       (ht095-sign-variations
        (ht095-chain-values-at chain upper)))))

(defun ht095-isolates-one-root-p
    (polynomial lower upper)
  (let ((normalized (ht095-poly-normalize polynomial)))
    (and
     (ht095-rational-polynomial-p normalized)
     (consp normalized)
     (< 0 (ht095-poly-degree normalized))
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not (equal (ht095-poly-evaluate normalized lower) 0))
     (not (equal (ht095-poly-evaluate normalized upper) 0))
     (equal
      (ht095-open-root-count normalized lower upper)
      1))))

(defun ht095-root-free-p (polynomial lower upper)
  (let ((normalized (ht095-poly-normalize polynomial)))
    (and
     (ht095-rational-polynomial-p normalized)
     (consp normalized)
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not (equal (ht095-poly-evaluate normalized lower) 0))
     (not (equal (ht095-poly-evaluate normalized upper) 0))
     (equal
      (ht095-open-root-count normalized lower upper)
      0))))

;; The selected root of primitive is a zero of value exactly when their gcd
;; has the same unique root in the isolating interval.
(defun ht095-zero-at-isolated-root-p
    (primitive value lower upper)
  (let ((normalized-value (ht095-poly-normalize value)))
    (or
     (not (consp normalized-value))
     (ht095-isolates-one-root-p
      (ht095-poly-gcd primitive normalized-value)
      lower
      upper))))

;; A sufficiently refined isolating interval is root-free for every
;; represented polynomial that is nonzero at the selected root.
(defun ht095-sign-decidable-p
    (primitive value lower upper)
  (or
   (ht095-zero-at-isolated-root-p
    primitive value lower upper)
   (ht095-root-free-p value lower upper)))

(defun ht095-sign-at-isolated-root
    (primitive value lower upper)
  (if (ht095-zero-at-isolated-root-p
       primitive value lower upper)
      0
    (ht095-sign (ht095-poly-evaluate value lower))))

(defun ht095-nonnegative-at-isolated-root-p
    (primitive value lower upper)
  (and
   (ht095-sign-decidable-p
    primitive value lower upper)
   (not
    (equal
     (ht095-sign-at-isolated-root
      primitive value lower upper)
     -1))))

(defun ht095-squared-distance
    (first-x first-y second-x second-y)
  (ht095-poly-add
   (ht095-poly-square
    (ht095-poly-subtract first-x second-x))
   (ht095-poly-square
    (ht095-poly-subtract first-y second-y))))

(defun ht095-orientation
    (ax ay bx by cx cy)
  (ht095-poly-subtract
   (ht095-poly-multiply
    (ht095-poly-subtract bx ax)
    (ht095-poly-subtract cy ay))
   (ht095-poly-multiply
    (ht095-poly-subtract by ay)
    (ht095-poly-subtract cx ax))))

(defun ht095-segment-cross
    (ax ay bx by px py)
  (ht095-orientation ax ay bx by px py))

(defun ht095-segment-dot
    (ax ay bx by px py)
  (ht095-poly-add
   (ht095-poly-multiply
    (ht095-poly-subtract px ax)
    (ht095-poly-subtract px bx))
   (ht095-poly-multiply
    (ht095-poly-subtract py ay)
    (ht095-poly-subtract py by))))

(defun ht095-ptolemy-implication-p
    (primitive lower upper
     ax ay bx by cx cy dx dy center-x center-y radius
     intersection-x intersection-y)
  (let* ((radius-squared
          (ht095-poly-square radius))
         (s-oa
          (ht095-squared-distance
           ax ay center-x center-y))
         (s-ob
          (ht095-squared-distance
           bx by center-x center-y))
         (s-oc
          (ht095-squared-distance
           cx cy center-x center-y))
         (s-od
          (ht095-squared-distance
           dx dy center-x center-y))
         (s-ab (ht095-squared-distance ax ay bx by))
         (s-bc (ht095-squared-distance bx by cx cy))
         (s-cd (ht095-squared-distance cx cy dx dy))
         (s-ad (ht095-squared-distance ax ay dx dy))
         (s-ac (ht095-squared-distance ax ay cx cy))
         (s-bd (ht095-squared-distance bx by dx dy))
         (orientation-abc
          (ht095-orientation ax ay bx by cx cy))
         (orientation-bcd
          (ht095-orientation bx by cx cy dx dy))
         (orientation-cda
          (ht095-orientation cx cy dx dy ax ay))
         (orientation-dab
          (ht095-orientation dx dy ax ay bx by))
         (intersection-on-ac-cross
          (ht095-segment-cross
           ax ay cx cy intersection-x intersection-y))
         (intersection-on-ac-dot
          (ht095-segment-dot
           ax ay cx cy intersection-x intersection-y))
         (intersection-on-bd-cross
          (ht095-segment-cross
           bx by dx dy intersection-x intersection-y))
         (intersection-on-bd-dot
          (ht095-segment-dot
           bx by dx dy intersection-x intersection-y))
         (diagonal-product
          (ht095-poly-multiply s-ac s-bd))
         (first-side-product
          (ht095-poly-multiply s-ab s-cd))
         (second-side-product
          (ht095-poly-multiply s-ad s-bc))
         (ptolemy-difference
          (ht095-poly-subtract
           (ht095-poly-subtract
            diagonal-product first-side-product)
           second-side-product))
         (ptolemy-square-equation
          (ht095-poly-subtract
           (ht095-poly-square ptolemy-difference)
           (ht095-poly-scale
            4
            (ht095-poly-multiply
             first-side-product second-side-product)))))
    (implies
     (and
      (ht095-isolates-one-root-p
       primitive lower upper)
      (ht095-rational-polynomial-p ax)
      (ht095-rational-polynomial-p ay)
      (ht095-rational-polynomial-p bx)
      (ht095-rational-polynomial-p by)
      (ht095-rational-polynomial-p cx)
      (ht095-rational-polynomial-p cy)
      (ht095-rational-polynomial-p dx)
      (ht095-rational-polynomial-p dy)
      (ht095-rational-polynomial-p center-x)
      (ht095-rational-polynomial-p center-y)
      (ht095-rational-polynomial-p radius)
      (ht095-rational-polynomial-p intersection-x)
      (ht095-rational-polynomial-p intersection-y)
      (ht095-zero-at-isolated-root-p
       primitive
       (ht095-poly-subtract s-oa radius-squared)
       lower upper)
      (ht095-zero-at-isolated-root-p
       primitive
       (ht095-poly-subtract s-ob radius-squared)
       lower upper)
      (ht095-zero-at-isolated-root-p
       primitive
       (ht095-poly-subtract s-oc radius-squared)
       lower upper)
      (ht095-zero-at-isolated-root-p
       primitive
       (ht095-poly-subtract s-od radius-squared)
       lower upper)
      (ht095-nonnegative-at-isolated-root-p
       primitive radius lower upper)
      (ht095-nonnegative-at-isolated-root-p
       primitive orientation-abc lower upper)
      (ht095-nonnegative-at-isolated-root-p
       primitive orientation-bcd lower upper)
      (ht095-nonnegative-at-isolated-root-p
       primitive orientation-cda lower upper)
      (ht095-nonnegative-at-isolated-root-p
       primitive orientation-dab lower upper)
      (ht095-zero-at-isolated-root-p
       primitive intersection-on-ac-cross lower upper)
      (ht095-nonnegative-at-isolated-root-p
       primitive
       (ht095-poly-negate intersection-on-ac-dot)
       lower upper)
      (ht095-zero-at-isolated-root-p
       primitive intersection-on-bd-cross lower upper)
      (ht095-nonnegative-at-isolated-root-p
       primitive
       (ht095-poly-negate intersection-on-bd-dot)
       lower upper)
      ;; This refinement condition only makes the conclusion sign readable;
      ;; every represented tuple admits such a refinement.
      (ht095-sign-decidable-p
       primitive ptolemy-difference lower upper))
     (and
      (not
       (equal
        (ht095-sign-at-isolated-root
         primitive ptolemy-difference lower upper)
        -1))
      (ht095-zero-at-isolated-root-p
       primitive ptolemy-square-equation lower upper)))))

(defun-sk hundred-theorems-095-ptolemys-theorem-statement ()
  (forall
   (primitive lower upper
    ax ay bx by cx cy dx dy center-x center-y radius
    intersection-x intersection-y)
   (ht095-ptolemy-implication-p
    primitive lower upper
    ax ay bx by cx cy dx dy center-x center-y radius
    intersection-x intersection-y)))

(value-triple :itpeval-statement-checked)
:q
