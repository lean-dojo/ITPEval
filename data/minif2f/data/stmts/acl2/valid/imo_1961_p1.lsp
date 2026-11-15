;; Statement-only formalization of miniF2F corpus artifact imo_1961_p1:
;; positive pairwise-distinct real numbers x, y, and z satisfying x*y = z^2,
;; with a = x+y+z and b^2 = x^2+y^2+z^2, obey
;; 0 < a, b^2 < a^2, and a^2 < 3*b^2. This file contains no proof.
;;
;; Standard ACL2 has no primitive arbitrary-real sort. This encoding does not
;; restrict the source variables to rationals: one rational polynomial and a
;; rational isolating interval select a real algebraic primitive alpha, and
;; rational polynomials in alpha encode x, y, z, a, and b. Sturm root counts
;; decide their equalities and strict orders exactly. Every finite tuple of
;; real algebraic numbers has such a common primitive representation, and the
;; interval can be refined to decide all finitely many signs used below.
;; Conversely, every valid representation denotes an actual real tuple.
;; Since the statement and its negation are first-order formulas over real
;; closed fields with rational coefficients, real-closed-field transfer makes
;; this universal algebraic-real encoding bidirectionally equivalent to the
;; source theorem over all real numbers.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Polynomials are proper lists of rational coefficients in ascending degree
;; order. The empty list is the zero polynomial.
(defun imo-1961-p1-rational-polynomial-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (imo-1961-p1-rational-polynomial-p (cdr polynomial)))
    (equal polynomial nil)))

(defun imo-1961-p1-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (imo-1961-p1-poly-normalize (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun imo-1961-p1-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (imo-1961-p1-poly-add (cdr left) (cdr right)))
      left))
   (t right)))

(defun imo-1961-p1-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (imo-1961-p1-poly-scale scalar (cdr polynomial)))
    nil))

(defun imo-1961-p1-poly-negate (polynomial)
  (imo-1961-p1-poly-scale -1 polynomial))

(defun imo-1961-p1-poly-subtract (left right)
  (imo-1961-p1-poly-normalize
   (imo-1961-p1-poly-add
    left
    (imo-1961-p1-poly-negate right))))

(defun imo-1961-p1-poly-multiply (left right)
  (if (consp left)
      (imo-1961-p1-poly-normalize
       (imo-1961-p1-poly-add
        (imo-1961-p1-poly-scale (car left) right)
        (cons
         0
         (imo-1961-p1-poly-multiply (cdr left) right))))
    nil))

(defun imo-1961-p1-poly-square (polynomial)
  (imo-1961-p1-poly-multiply polynomial polynomial))

(defun imo-1961-p1-poly-derivative-aux (coefficients degree)
  (if (consp coefficients)
      (cons (* degree (car coefficients))
            (imo-1961-p1-poly-derivative-aux
             (cdr coefficients) (+ degree 1)))
    nil))

(defun imo-1961-p1-poly-derivative (polynomial)
  (if (consp polynomial)
      (imo-1961-p1-poly-normalize
       (imo-1961-p1-poly-derivative-aux
        (cdr polynomial) 1))
    nil))

(defun imo-1961-p1-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (imo-1961-p1-zero-list (- count 1)))))

(defun imo-1961-p1-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append
     (imo-1961-p1-zero-list degree)
     (list coefficient))))

(defun imo-1961-p1-poly-degree (polynomial)
  (let ((normalized
         (imo-1961-p1-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun imo-1961-p1-poly-leading-coefficient (polynomial)
  (let ((normalized
         (imo-1961-p1-poly-normalize polynomial)))
    (if (consp normalized)
        (nth
         (imo-1961-p1-poly-degree normalized)
         normalized)
      0)))

;; The step bound makes polynomial long division total in ACL2. Each
;; nonterminal step lowers the degree of the current remainder.
(defun imo-1961-p1-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons
       (imo-1961-p1-poly-normalize quotient)
       (imo-1961-p1-poly-normalize remainder))
    (let* ((normalized-remainder
            (imo-1961-p1-poly-normalize remainder))
           (normalized-divisor
            (imo-1961-p1-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (<
               (imo-1961-p1-poly-degree normalized-remainder)
               (imo-1961-p1-poly-degree normalized-divisor)))
          (cons
           (imo-1961-p1-poly-normalize quotient)
           normalized-remainder)
        (let* ((degree-difference
                (-
                 (imo-1961-p1-poly-degree normalized-remainder)
                 (imo-1961-p1-poly-degree normalized-divisor)))
               (coefficient
                (/
                 (imo-1961-p1-poly-leading-coefficient
                  normalized-remainder)
                 (imo-1961-p1-poly-leading-coefficient
                  normalized-divisor)))
               (term
                (imo-1961-p1-poly-monomial
                 coefficient degree-difference)))
          (imo-1961-p1-poly-divmod-steps
           (imo-1961-p1-poly-subtract
            normalized-remainder
            (imo-1961-p1-poly-multiply
             term normalized-divisor))
           normalized-divisor
           (imo-1961-p1-poly-add quotient term)
           (- steps 1)))))))

(defun imo-1961-p1-poly-divmod (dividend divisor)
  (imo-1961-p1-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1
      (len
       (imo-1961-p1-poly-normalize dividend)))))

(defun imo-1961-p1-poly-remainder (dividend divisor)
  (cdr
   (imo-1961-p1-poly-divmod dividend divisor)))

(defun imo-1961-p1-poly-gcd-steps (left right steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-left
         (imo-1961-p1-poly-normalize left))
        (normalized-right
         (imo-1961-p1-poly-normalize right)))
    (if (or (zp steps)
            (not (consp normalized-right)))
        normalized-left
      (imo-1961-p1-poly-gcd-steps
       normalized-right
       (imo-1961-p1-poly-remainder
        normalized-left normalized-right)
       (- steps 1)))))

(defun imo-1961-p1-poly-gcd (left right)
  (imo-1961-p1-poly-gcd-steps
   left
   right
   (+ 2
      (len (imo-1961-p1-poly-normalize left))
      (len (imo-1961-p1-poly-normalize right)))))

(defun imo-1961-p1-sturm-tail (previous current steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-current
         (imo-1961-p1-poly-normalize current)))
    (if (or (zp steps)
            (not (consp normalized-current)))
        nil
      (cons
       normalized-current
       (imo-1961-p1-sturm-tail
        normalized-current
        (imo-1961-p1-poly-negate
         (imo-1961-p1-poly-remainder
          previous normalized-current))
        (- steps 1))))))

(defun imo-1961-p1-sturm-chain (polynomial)
  (let ((normalized
         (imo-1961-p1-poly-normalize polynomial)))
    (if (consp normalized)
        (cons
         normalized
         (imo-1961-p1-sturm-tail
          normalized
          (imo-1961-p1-poly-derivative normalized)
          (+ 1 (len normalized))))
      nil)))

(defun imo-1961-p1-poly-evaluate (polynomial value)
  (if (consp polynomial)
      (+ (car polynomial)
         (* value
            (imo-1961-p1-poly-evaluate
             (cdr polynomial) value)))
    0))

(defun imo-1961-p1-chain-values-at (chain value)
  (if (consp chain)
      (cons
       (imo-1961-p1-poly-evaluate (car chain) value)
       (imo-1961-p1-chain-values-at (cdr chain) value))
    nil))

(defun imo-1961-p1-sign (value)
  (cond
   ((< value 0) -1)
   ((< 0 value) 1)
   (t 0)))

(defun imo-1961-p1-sign-variations-aux
    (values previous-sign)
  (if (consp values)
      (let ((current-sign
             (imo-1961-p1-sign (car values))))
        (cond
         ((equal current-sign 0)
          (imo-1961-p1-sign-variations-aux
           (cdr values) previous-sign))
         ((equal previous-sign 0)
          (imo-1961-p1-sign-variations-aux
           (cdr values) current-sign))
         (t
          (+
           (if (equal current-sign previous-sign) 0 1)
           (imo-1961-p1-sign-variations-aux
            (cdr values) current-sign)))))
    0))

(defun imo-1961-p1-sign-variations (values)
  (imo-1961-p1-sign-variations-aux values 0))

;; With nonzero endpoint values, the variation difference counts distinct
;; roots in the open interval.
(defun imo-1961-p1-open-root-count
    (polynomial lower upper)
  (let ((chain
         (imo-1961-p1-sturm-chain polynomial)))
    (-
     (imo-1961-p1-sign-variations
      (imo-1961-p1-chain-values-at chain lower))
     (imo-1961-p1-sign-variations
      (imo-1961-p1-chain-values-at chain upper)))))

(defun imo-1961-p1-isolates-one-root-p
    (polynomial lower upper)
  (let ((normalized
         (imo-1961-p1-poly-normalize polynomial)))
    (and
     (imo-1961-p1-rational-polynomial-p normalized)
     (consp normalized)
     (< 0 (imo-1961-p1-poly-degree normalized))
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not
      (equal
       (imo-1961-p1-poly-evaluate normalized lower)
       0))
     (not
      (equal
       (imo-1961-p1-poly-evaluate normalized upper)
       0))
     (equal
      (imo-1961-p1-open-root-count
       normalized lower upper)
      1))))

(defun imo-1961-p1-root-free-p
    (polynomial lower upper)
  (let ((normalized
         (imo-1961-p1-poly-normalize polynomial)))
    (and
     (imo-1961-p1-rational-polynomial-p normalized)
     (consp normalized)
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not
      (equal
       (imo-1961-p1-poly-evaluate normalized lower)
       0))
     (not
      (equal
       (imo-1961-p1-poly-evaluate normalized upper)
       0))
     (equal
      (imo-1961-p1-open-root-count
       normalized lower upper)
      0))))

;; The isolated root of p is a zero of r exactly when gcd(p,r) has that
;; unique interval root.
(defun imo-1961-p1-zero-at-isolated-root-p
    (p r lower upper)
  (let ((normalized-r
         (imo-1961-p1-poly-normalize r)))
    (or
     (not (consp normalized-r))
     (imo-1961-p1-isolates-one-root-p
      (imo-1961-p1-poly-gcd p normalized-r)
      lower upper))))

;; If r is nonzero at the selected root, a sufficiently refined rational
;; isolating interval is root-free for r.
(defun imo-1961-p1-sign-decidable-p
    (p r lower upper)
  (or
   (imo-1961-p1-zero-at-isolated-root-p
    p r lower upper)
   (imo-1961-p1-root-free-p r lower upper)))

(defun imo-1961-p1-sign-at-isolated-root
    (p r lower upper)
  (if
      (imo-1961-p1-zero-at-isolated-root-p
       p r lower upper)
      0
    (imo-1961-p1-sign
     (imo-1961-p1-poly-evaluate r lower))))

(defun imo-1961-p1-positive-at-isolated-root-p
    (p r lower upper)
  (and
   (imo-1961-p1-sign-decidable-p p r lower upper)
   (equal
    (imo-1961-p1-sign-at-isolated-root
     p r lower upper)
    1)))

(defun imo-1961-p1-statement
    (isolating-polynomial lower upper x y z a b)
  (let* ((x-minus-y
          (imo-1961-p1-poly-subtract x y))
         (y-minus-z
          (imo-1961-p1-poly-subtract y z))
         (z-minus-x
          (imo-1961-p1-poly-subtract z x))
         (x-square
          (imo-1961-p1-poly-square x))
         (y-square
          (imo-1961-p1-poly-square y))
         (z-square
          (imo-1961-p1-poly-square z))
         (a-square
          (imo-1961-p1-poly-square a))
         (b-square
          (imo-1961-p1-poly-square b))
         (sum-minus-a
          (imo-1961-p1-poly-subtract
           (imo-1961-p1-poly-add
            (imo-1961-p1-poly-add x y)
            z)
           a))
         (square-sum-minus-b-square
          (imo-1961-p1-poly-subtract
           (imo-1961-p1-poly-add
            (imo-1961-p1-poly-add x-square y-square)
            z-square)
           b-square))
         (xy-minus-z-square
          (imo-1961-p1-poly-subtract
           (imo-1961-p1-poly-multiply x y)
           z-square))
         (a-square-minus-b-square
          (imo-1961-p1-poly-subtract
           a-square b-square))
         (three-b-square-minus-a-square
          (imo-1961-p1-poly-subtract
           (imo-1961-p1-poly-scale 3 b-square)
           a-square)))
    (implies
     (and
      (imo-1961-p1-isolates-one-root-p
       isolating-polynomial lower upper)
      (imo-1961-p1-rational-polynomial-p x)
      (imo-1961-p1-rational-polynomial-p y)
      (imo-1961-p1-rational-polynomial-p z)
      (imo-1961-p1-rational-polynomial-p a)
      (imo-1961-p1-rational-polynomial-p b)
      (imo-1961-p1-positive-at-isolated-root-p
       isolating-polynomial x lower upper)
      (imo-1961-p1-positive-at-isolated-root-p
       isolating-polynomial y lower upper)
      (imo-1961-p1-positive-at-isolated-root-p
       isolating-polynomial z lower upper)
      (not
       (imo-1961-p1-zero-at-isolated-root-p
        isolating-polynomial x-minus-y lower upper))
      (not
       (imo-1961-p1-zero-at-isolated-root-p
        isolating-polynomial y-minus-z lower upper))
      (not
       (imo-1961-p1-zero-at-isolated-root-p
        isolating-polynomial z-minus-x lower upper))
      (imo-1961-p1-zero-at-isolated-root-p
       isolating-polynomial sum-minus-a lower upper)
      (imo-1961-p1-zero-at-isolated-root-p
       isolating-polynomial square-sum-minus-b-square
       lower upper)
      (imo-1961-p1-zero-at-isolated-root-p
       isolating-polynomial xy-minus-z-square lower upper)
      ;; These refinement conditions only make the three conclusion signs
      ;; readable from the selected interval; every represented tuple admits
      ;; such a refinement.
      (imo-1961-p1-sign-decidable-p
       isolating-polynomial a lower upper)
      (imo-1961-p1-sign-decidable-p
       isolating-polynomial a-square-minus-b-square
       lower upper)
      (imo-1961-p1-sign-decidable-p
       isolating-polynomial three-b-square-minus-a-square
       lower upper))
     (and
      (equal
       (imo-1961-p1-sign-at-isolated-root
        isolating-polynomial a lower upper)
       1)
      (equal
       (imo-1961-p1-sign-at-isolated-root
        isolating-polynomial a-square-minus-b-square
        lower upper)
       1)
      (equal
       (imo-1961-p1-sign-at-isolated-root
        isolating-polynomial three-b-square-minus-a-square
        lower upper)
       1)))))

(value-triple :itpeval-statement-checked)
:q
