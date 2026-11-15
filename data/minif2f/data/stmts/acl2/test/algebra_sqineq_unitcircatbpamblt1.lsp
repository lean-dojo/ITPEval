;; Statement-only formalization of miniF2F corpus artifact
;; algebra_sqineq_unitcircatbpamblt1: real numbers a and b on the unit circle
;; satisfy a*b + (a - b) <= 1. This file contains no proof.
;;
;; Standard ACL2 has no primitive arbitrary-real sort. This encoding does not
;; restrict a and b to rationals: a rational polynomial and rational isolating
;; interval select a real algebraic primitive alpha, while two rational
;; polynomials in alpha encode a and b. Exact Sturm root counts decide the
;; equation and order below. Every finite tuple of real algebraic numbers has
;; such a common primitive representation, and every accepted representation
;; denotes an actual real tuple. Since the statement and its negation are
;; first-order formulas over real closed fields with rational coefficients,
;; real-closed-field transfer makes this encoding bidirectionally equivalent
;; to the source theorem over all real numbers.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Polynomials are proper lists of rational coefficients in ascending degree
;; order. The empty list is the zero polynomial.
(defun asu-rational-polynomial-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (asu-rational-polynomial-p (cdr polynomial)))
    (equal polynomial nil)))

(defun asu-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail (asu-poly-normalize (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun asu-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (asu-poly-add (cdr left) (cdr right)))
      left))
   (t right)))

(defun asu-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (asu-poly-scale scalar (cdr polynomial)))
    nil))

(defun asu-poly-negate (polynomial)
  (asu-poly-scale -1 polynomial))

(defun asu-poly-subtract (left right)
  (asu-poly-normalize
   (asu-poly-add left (asu-poly-negate right))))

(defun asu-poly-multiply (left right)
  (if (consp left)
      (asu-poly-normalize
       (asu-poly-add
        (asu-poly-scale (car left) right)
        (cons 0 (asu-poly-multiply (cdr left) right))))
    nil))

(defun asu-poly-square (polynomial)
  (asu-poly-multiply polynomial polynomial))

(defun asu-poly-derivative-aux (coefficients degree)
  (if (consp coefficients)
      (cons (* degree (car coefficients))
            (asu-poly-derivative-aux
             (cdr coefficients) (+ degree 1)))
    nil))

(defun asu-poly-derivative (polynomial)
  (if (consp polynomial)
      (asu-poly-normalize
       (asu-poly-derivative-aux (cdr polynomial) 1))
    nil))

(defun asu-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0 (asu-zero-list (- count 1)))))

(defun asu-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append (asu-zero-list degree) (list coefficient))))

(defun asu-poly-degree (polynomial)
  (let ((normalized (asu-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun asu-poly-leading-coefficient (polynomial)
  (let ((normalized (asu-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (asu-poly-degree normalized) normalized)
      0)))

(defun asu-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons (asu-poly-normalize quotient)
            (asu-poly-normalize remainder))
    (let* ((normalized-remainder
            (asu-poly-normalize remainder))
           (normalized-divisor
            (asu-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (asu-poly-degree normalized-remainder)
                 (asu-poly-degree normalized-divisor)))
          (cons (asu-poly-normalize quotient)
                normalized-remainder)
        (let* ((degree-difference
                (- (asu-poly-degree normalized-remainder)
                   (asu-poly-degree normalized-divisor)))
               (coefficient
                (/ (asu-poly-leading-coefficient
                    normalized-remainder)
                   (asu-poly-leading-coefficient
                    normalized-divisor)))
               (term
                (asu-poly-monomial
                 coefficient degree-difference)))
          (asu-poly-divmod-steps
           (asu-poly-subtract
            normalized-remainder
            (asu-poly-multiply term normalized-divisor))
           normalized-divisor
           (asu-poly-add quotient term)
           (- steps 1)))))))

(defun asu-poly-divmod (dividend divisor)
  (asu-poly-divmod-steps
   dividend divisor nil
   (+ 1 (len (asu-poly-normalize dividend)))))

(defun asu-poly-remainder (dividend divisor)
  (cdr (asu-poly-divmod dividend divisor)))

(defun asu-poly-gcd-steps (left right steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-left (asu-poly-normalize left))
        (normalized-right (asu-poly-normalize right)))
    (if (or (zp steps)
            (not (consp normalized-right)))
        normalized-left
      (asu-poly-gcd-steps
       normalized-right
       (asu-poly-remainder normalized-left normalized-right)
       (- steps 1)))))

(defun asu-poly-gcd (left right)
  (asu-poly-gcd-steps
   left right
   (+ 2
      (len (asu-poly-normalize left))
      (len (asu-poly-normalize right)))))

(defun asu-sturm-tail (previous current steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-current (asu-poly-normalize current)))
    (if (or (zp steps)
            (not (consp normalized-current)))
        nil
      (cons
       normalized-current
       (asu-sturm-tail
        normalized-current
        (asu-poly-negate
         (asu-poly-remainder previous normalized-current))
        (- steps 1))))))

(defun asu-sturm-chain (polynomial)
  (let ((normalized (asu-poly-normalize polynomial)))
    (if (consp normalized)
        (cons
         normalized
         (asu-sturm-tail
          normalized
          (asu-poly-derivative normalized)
          (+ 1 (len normalized))))
      nil)))

(defun asu-poly-evaluate (polynomial value)
  (if (consp polynomial)
      (+ (car polynomial)
         (* value (asu-poly-evaluate (cdr polynomial) value)))
    0))

(defun asu-chain-values-at (chain value)
  (if (consp chain)
      (cons (asu-poly-evaluate (car chain) value)
            (asu-chain-values-at (cdr chain) value))
    nil))

(defun asu-sign (value)
  (cond
   ((< value 0) -1)
   ((< 0 value) 1)
   (t 0)))

(defun asu-sign-variations-aux (values previous-sign)
  (if (consp values)
      (let ((current-sign (asu-sign (car values))))
        (cond
         ((equal current-sign 0)
          (asu-sign-variations-aux
           (cdr values) previous-sign))
         ((equal previous-sign 0)
          (asu-sign-variations-aux
           (cdr values) current-sign))
         (t
          (+ (if (equal current-sign previous-sign) 0 1)
             (asu-sign-variations-aux
              (cdr values) current-sign)))))
    0))

(defun asu-sign-variations (values)
  (asu-sign-variations-aux values 0))

(defun asu-open-root-count (polynomial lower upper)
  (let ((chain (asu-sturm-chain polynomial)))
    (- (asu-sign-variations
        (asu-chain-values-at chain lower))
       (asu-sign-variations
        (asu-chain-values-at chain upper)))))

(defun asu-isolates-one-root-p (polynomial lower upper)
  (let ((normalized (asu-poly-normalize polynomial)))
    (and
     (asu-rational-polynomial-p normalized)
     (consp normalized)
     (< 0 (asu-poly-degree normalized))
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not (equal (asu-poly-evaluate normalized lower) 0))
     (not (equal (asu-poly-evaluate normalized upper) 0))
     (equal
      (asu-open-root-count normalized lower upper)
      1))))

(defun asu-root-free-p (polynomial lower upper)
  (let ((normalized (asu-poly-normalize polynomial)))
    (and
     (asu-rational-polynomial-p normalized)
     (consp normalized)
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not (equal (asu-poly-evaluate normalized lower) 0))
     (not (equal (asu-poly-evaluate normalized upper) 0))
     (equal
      (asu-open-root-count normalized lower upper)
      0))))

(defun asu-zero-at-isolated-root-p (p r lower upper)
  (let ((normalized-r (asu-poly-normalize r)))
    (or
     (not (consp normalized-r))
     (asu-isolates-one-root-p
      (asu-poly-gcd p normalized-r)
      lower upper))))

(defun asu-sign-decidable-p (p r lower upper)
  (or
   (asu-zero-at-isolated-root-p p r lower upper)
   (asu-root-free-p r lower upper)))

(defun asu-sign-at-isolated-root (p r lower upper)
  (if (asu-zero-at-isolated-root-p p r lower upper)
      0
    (asu-sign (asu-poly-evaluate r lower))))

(defun asu-nonnegative-at-isolated-root-p
    (p r lower upper)
  (and
   (asu-sign-decidable-p p r lower upper)
   (not
    (equal
     (asu-sign-at-isolated-root p r lower upper)
     -1))))

(defun algebra-sqineq-unitcircatbpamblt1-statement
    (isolating-polynomial lower upper a b)
  (let* ((one (list 1))
         (circle-equation
          (asu-poly-subtract
           (asu-poly-add
            (asu-poly-square a)
            (asu-poly-square b))
           one))
         (left-hand-side
          (asu-poly-add
           (asu-poly-multiply a b)
           (asu-poly-subtract a b)))
         (conclusion-gap
          (asu-poly-subtract one left-hand-side)))
    (implies
     (and
      (asu-isolates-one-root-p
       isolating-polynomial lower upper)
      (asu-rational-polynomial-p a)
      (asu-rational-polynomial-p b)
      (asu-zero-at-isolated-root-p
       isolating-polynomial circle-equation lower upper)
      ;; This only makes the conclusion sign readable; every represented pair
      ;; admits such a rational isolating-interval refinement.
      (asu-sign-decidable-p
       isolating-polynomial conclusion-gap lower upper))
     (asu-nonnegative-at-isolated-root-p
      isolating-polynomial conclusion-gap lower upper))))

(value-triple :itpeval-statement-checked)
:q
