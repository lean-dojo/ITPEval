;; Statement-only formalization of PutnamBench corpus artifact putnam_1981_a5:
;; every real polynomial P with n distinct roots greater than 1 gives
;; Q=(x^2+1)P P'+x(P^2+(P')^2) at least 2n-1 distinct real roots.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The statement is encoded by excluding its counterexamples. For any fixed
;; degrees and factor counts, existence of a counterexample is a first-order
;; sentence over real closed fields. Hence a real counterexample exists iff
;; one exists over the real algebraic numbers. Every finite tuple of real
;; algebraic numbers lies in Q(alpha) for one real algebraic alpha.
;;
;; PRIMITIVE with the rational interval (LOWER,UPPER) isolates alpha, and each
;; coefficient is a rational polynomial in alpha. Complete real factorizations
;; of P and Q list their distinct linear roots with positive multiplicities;
;; the remaining monic quadratic factors have negative discriminant. Thus the
;; linear lists count exactly all distinct real roots, without sampling roots,
;; bounding the degree, or restricting the source coefficients to rationals.

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-1981-a5-rp-p (p)
  (if (consp p)
      (and (rationalp (car p))
           (putnam-1981-a5-rp-p (cdr p)))
    (equal p nil)))

(defun putnam-1981-a5-rp-normalize (p)
  (if (consp p)
      (if (equal (car p) 0)
          (putnam-1981-a5-rp-normalize (cdr p))
        p)
    nil))

(defun putnam-1981-a5-rp-negate (p)
  (if (consp p)
      (cons (- (car p))
            (putnam-1981-a5-rp-negate (cdr p)))
    nil))

(defun putnam-1981-a5-rp-add-raw (p q)
  (declare (xargs :measure (+ (acl2-count p) (acl2-count q))))
  (cond
   ((endp p) q)
   ((endp q) p)
   ((< (len p) (len q))
    (cons (car q)
          (putnam-1981-a5-rp-add-raw p (cdr q))))
   ((< (len q) (len p))
    (cons (car p)
          (putnam-1981-a5-rp-add-raw (cdr p) q)))
   (t
    (cons (+ (car p) (car q))
          (putnam-1981-a5-rp-add-raw (cdr p) (cdr q))))))

(defun putnam-1981-a5-rp-add (p q)
  (putnam-1981-a5-rp-normalize
   (putnam-1981-a5-rp-add-raw p q)))

(defun putnam-1981-a5-rp-subtract (p q)
  (putnam-1981-a5-rp-add
   p (putnam-1981-a5-rp-negate q)))

(defun putnam-1981-a5-rp-scale (coefficient p)
  (if (consp p)
      (cons (* coefficient (car p))
            (putnam-1981-a5-rp-scale coefficient (cdr p)))
    nil))

(defun putnam-1981-a5-zeroes (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (putnam-1981-a5-zeroes (- n 1)))))

(defun putnam-1981-a5-rp-scale-shift (coefficient p shift)
  (append
   (putnam-1981-a5-rp-scale coefficient p)
   (putnam-1981-a5-zeroes shift)))

(defun putnam-1981-a5-rp-multiply-raw (p q)
  (if (consp p)
      (putnam-1981-a5-rp-add
       (putnam-1981-a5-rp-scale-shift
        (car p) q (len (cdr p)))
       (putnam-1981-a5-rp-multiply-raw (cdr p) q))
    nil))

(defun putnam-1981-a5-rp-multiply (p q)
  (putnam-1981-a5-rp-normalize
   (putnam-1981-a5-rp-multiply-raw p q)))

(defun putnam-1981-a5-rp-eval-aux (p x accumulator)
  (if (consp p)
      (putnam-1981-a5-rp-eval-aux
       (cdr p) x (+ (* accumulator x) (car p)))
    accumulator))

(defun putnam-1981-a5-rp-eval (p x)
  (putnam-1981-a5-rp-eval-aux p x 0))

(defun putnam-1981-a5-rp-derivative-aux (p degree)
  (if (consp p)
      (if (zp degree)
          nil
        (cons (* degree (car p))
              (putnam-1981-a5-rp-derivative-aux
               (cdr p) (- degree 1))))
    nil))

(defun putnam-1981-a5-rp-derivative (p)
  (let ((normalized (putnam-1981-a5-rp-normalize p)))
    (putnam-1981-a5-rp-normalize
     (putnam-1981-a5-rp-derivative-aux
      normalized
      (nfix (- (len normalized) 1))))))

(defun putnam-1981-a5-rp-remainder-fuel (p q fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((p (putnam-1981-a5-rp-normalize p))
        (q (putnam-1981-a5-rp-normalize q)))
    (if (or (zp fuel)
            (endp q)
            (< (len p) (len q)))
        p
      (putnam-1981-a5-rp-remainder-fuel
       (putnam-1981-a5-rp-subtract
        p
        (putnam-1981-a5-rp-scale-shift
         (/ (car p) (car q))
         q
         (- (len p) (len q))))
       q
       (- fuel 1)))))

(defun putnam-1981-a5-rp-remainder (p q)
  (putnam-1981-a5-rp-remainder-fuel
   p q (+ 1 (len (putnam-1981-a5-rp-normalize p)))))

(defun putnam-1981-a5-rp-sturm-tail (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current (putnam-1981-a5-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-1981-a5-rp-sturm-tail
        current
        (putnam-1981-a5-rp-negate
         (putnam-1981-a5-rp-remainder previous current))
        (- fuel 1))))))

(defun putnam-1981-a5-rp-sturm-sequence (p q)
  (let ((p (putnam-1981-a5-rp-normalize p))
        (q (putnam-1981-a5-rp-normalize q)))
    (if (endp p)
        nil
      (cons
       p
       (if (endp q)
           nil
         (cons
          q
          (putnam-1981-a5-rp-sturm-tail
           p q (+ 1 (len p) (len q)))))))))

(defun putnam-1981-a5-rational-sign (x)
  (cond ((< x 0) -1)
        ((< 0 x) 1)
        (t 0)))

(defun putnam-1981-a5-rp-variations-aux
    (polynomials x previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-1981-a5-rational-sign
              (putnam-1981-a5-rp-eval
               (car polynomials) x))))
        (if (equal sign 0)
            (putnam-1981-a5-rp-variations-aux
             (cdr polynomials) x previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-1981-a5-rp-variations-aux
              (cdr polynomials) x sign))))
    0))

(defun putnam-1981-a5-rp-variations (polynomials x)
  (putnam-1981-a5-rp-variations-aux polynomials x 0))

(defun putnam-1981-a5-rp-cauchy-index (p q lower upper)
  (let ((sequence
         (putnam-1981-a5-rp-sturm-sequence p q)))
    (- (putnam-1981-a5-rp-variations sequence lower)
       (putnam-1981-a5-rp-variations sequence upper))))

(defun putnam-1981-a5-rp-root-count (p lower upper)
  (putnam-1981-a5-rp-cauchy-index
   p (putnam-1981-a5-rp-derivative p) lower upper))

(defun putnam-1981-a5-primitive-p (primitive lower upper)
  (and
   (putnam-1981-a5-rp-p primitive)
   (consp (putnam-1981-a5-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not (equal
         (putnam-1981-a5-rp-eval primitive lower) 0))
   (not (equal
         (putnam-1981-a5-rp-eval primitive upper) 0))
   (equal
    (putnam-1981-a5-rp-root-count primitive lower upper)
    1)
   (equal
    (putnam-1981-a5-rp-cauchy-index
     primitive
     (putnam-1981-a5-rp-multiply
      (putnam-1981-a5-rp-derivative primitive)
      (putnam-1981-a5-rp-derivative primitive))
     lower
     upper)
    1)))

;; For the single isolated root alpha, this Sturm-Tarski query is the sign of
;; VALUE(alpha).
(defun putnam-1981-a5-algebraic-sign
    (primitive lower upper value)
  (putnam-1981-a5-rp-cauchy-index
   primitive
   (putnam-1981-a5-rp-multiply
    (putnam-1981-a5-rp-derivative primitive)
    value)
   lower
   upper))

(defun putnam-1981-a5-algebraic-zero-p
    (primitive lower upper value)
  (equal
   (putnam-1981-a5-algebraic-sign
    primitive lower upper value)
   0))

(defun putnam-1981-a5-algebraic-equal-p
    (primitive lower upper left right)
  (putnam-1981-a5-algebraic-zero-p
   primitive lower upper
   (putnam-1981-a5-rp-subtract left right)))

(defun putnam-1981-a5-algebraic-list-p (values)
  (if (consp values)
      (and (putnam-1981-a5-rp-p (car values))
           (putnam-1981-a5-algebraic-list-p (cdr values)))
    (equal values nil)))

;; Polynomials in x use ascending coefficient order. Each coefficient is a
;; rational polynomial in alpha.

(defun putnam-1981-a5-polynomial-normalize
    (primitive lower upper coefficients)
  (if (consp coefficients)
      (let ((tail
             (putnam-1981-a5-polynomial-normalize
              primitive lower upper (cdr coefficients))))
        (if (and (endp tail)
                 (putnam-1981-a5-algebraic-zero-p
                  primitive lower upper (car coefficients)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun putnam-1981-a5-polynomial-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons
         (putnam-1981-a5-rp-add (car left) (car right))
         (putnam-1981-a5-polynomial-add
          (cdr left) (cdr right)))
      left))
   (t right)))

(defun putnam-1981-a5-polynomial-negate (polynomial)
  (if (consp polynomial)
      (cons
       (putnam-1981-a5-rp-negate (car polynomial))
       (putnam-1981-a5-polynomial-negate
        (cdr polynomial)))
    nil))

(defun putnam-1981-a5-polynomial-subtract (left right)
  (putnam-1981-a5-polynomial-add
   left
   (putnam-1981-a5-polynomial-negate right)))

(defun putnam-1981-a5-polynomial-scale
    (coefficient polynomial)
  (if (consp polynomial)
      (cons
       (putnam-1981-a5-rp-multiply
        coefficient (car polynomial))
       (putnam-1981-a5-polynomial-scale
        coefficient (cdr polynomial)))
    nil))

(defun putnam-1981-a5-polynomial-multiply (left right)
  (if (consp left)
      (putnam-1981-a5-polynomial-add
       (putnam-1981-a5-polynomial-scale
        (car left) right)
       (cons
        nil
        (putnam-1981-a5-polynomial-multiply
         (cdr left) right)))
    nil))

(defun putnam-1981-a5-polynomial-power
    (polynomial exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (list (list 1))
    (putnam-1981-a5-polynomial-multiply
     polynomial
     (putnam-1981-a5-polynomial-power
      polynomial (- exponent 1)))))

(defun putnam-1981-a5-polynomial-derivative-aux
    (coefficients degree)
  (if (consp coefficients)
      (cons
       (putnam-1981-a5-rp-scale degree (car coefficients))
       (putnam-1981-a5-polynomial-derivative-aux
        (cdr coefficients) (+ degree 1)))
    nil))

(defun putnam-1981-a5-polynomial-derivative (polynomial)
  (if (consp polynomial)
      (putnam-1981-a5-polynomial-derivative-aux
       (cdr polynomial) 1)
    nil))

(defun putnam-1981-a5-polynomial-zero-at-alpha-p
    (primitive lower upper polynomial)
  (if (consp polynomial)
      (and
       (putnam-1981-a5-algebraic-zero-p
        primitive lower upper (car polynomial))
       (putnam-1981-a5-polynomial-zero-at-alpha-p
        primitive lower upper (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-1981-a5-polynomial-equal-at-alpha-p
    (primitive lower upper left right)
  (putnam-1981-a5-polynomial-zero-at-alpha-p
   primitive lower upper
   (putnam-1981-a5-polynomial-subtract left right)))

(defun putnam-1981-a5-q-polynomial (polynomial)
  (let* ((derivative
          (putnam-1981-a5-polynomial-derivative polynomial))
         (x-squared-plus-one
          (list (list 1) nil (list 1)))
         (x-polynomial
          (list nil (list 1))))
    (putnam-1981-a5-polynomial-add
     (putnam-1981-a5-polynomial-multiply
      x-squared-plus-one
      (putnam-1981-a5-polynomial-multiply
       polynomial derivative))
     (putnam-1981-a5-polynomial-multiply
      x-polynomial
      (putnam-1981-a5-polynomial-add
       (putnam-1981-a5-polynomial-multiply
        polynomial polynomial)
       (putnam-1981-a5-polynomial-multiply
        derivative derivative))))))

(defun putnam-1981-a5-positive-nat-list-p (values)
  (if (consp values)
      (and (posp (car values))
           (putnam-1981-a5-positive-nat-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1981-a5-distinct-from-p
    (primitive lower upper value values)
  (if (consp values)
      (and
       (not
        (putnam-1981-a5-algebraic-equal-p
         primitive lower upper value (car values)))
       (putnam-1981-a5-distinct-from-p
        primitive lower upper value (cdr values)))
    (equal values nil)))

(defun putnam-1981-a5-pairwise-distinct-p
    (primitive lower upper values)
  (if (consp values)
      (and
       (putnam-1981-a5-distinct-from-p
        primitive lower upper (car values) (cdr values))
       (putnam-1981-a5-pairwise-distinct-p
        primitive lower upper (cdr values)))
    (equal values nil)))

(defun putnam-1981-a5-linear-factor (root)
  (list (putnam-1981-a5-rp-negate root)
        (list 1)))

(defun putnam-1981-a5-linear-product
    (roots multiplicities)
  (if (consp roots)
      (putnam-1981-a5-polynomial-multiply
       (putnam-1981-a5-polynomial-power
        (putnam-1981-a5-linear-factor (car roots))
        (car multiplicities))
       (putnam-1981-a5-linear-product
        (cdr roots) (cdr multiplicities)))
    (list (list 1))))

(defun putnam-1981-a5-quadratic-descriptor-p
    (quadratic)
  (and
   (true-listp quadratic)
   (equal (len quadratic) 2)
   (putnam-1981-a5-rp-p (car quadratic))
   (putnam-1981-a5-rp-p (cadr quadratic))))

(defun putnam-1981-a5-negative-discriminant-p
    (primitive lower upper quadratic)
  (let* ((b (car quadratic))
         (c (cadr quadratic))
         (discriminant
          (putnam-1981-a5-rp-subtract
           (putnam-1981-a5-rp-multiply b b)
           (putnam-1981-a5-rp-scale 4 c))))
    (< (putnam-1981-a5-algebraic-sign
        primitive lower upper discriminant)
       0)))

(defun putnam-1981-a5-quadratic-list-p
    (primitive lower upper quadratics)
  (if (consp quadratics)
      (and
       (putnam-1981-a5-quadratic-descriptor-p
        (car quadratics))
       (putnam-1981-a5-negative-discriminant-p
        primitive lower upper (car quadratics))
       (putnam-1981-a5-quadratic-list-p
        primitive lower upper (cdr quadratics)))
    (equal quadratics nil)))

(defun putnam-1981-a5-quadratic-factor (quadratic)
  (list (cadr quadratic)
        (car quadratic)
        (list 1)))

(defun putnam-1981-a5-quadratic-product
    (quadratics multiplicities)
  (if (consp quadratics)
      (putnam-1981-a5-polynomial-multiply
       (putnam-1981-a5-polynomial-power
        (putnam-1981-a5-quadratic-factor
         (car quadratics))
        (car multiplicities))
       (putnam-1981-a5-quadratic-product
        (cdr quadratics) (cdr multiplicities)))
    (list (list 1))))

(defun putnam-1981-a5-factorization-polynomial
    (scalar roots root-multiplicities
            quadratics quadratic-multiplicities)
  (putnam-1981-a5-polynomial-scale
   scalar
   (putnam-1981-a5-polynomial-multiply
    (putnam-1981-a5-linear-product
     roots root-multiplicities)
    (putnam-1981-a5-quadratic-product
     quadratics quadratic-multiplicities))))

(defun putnam-1981-a5-valid-factorization-p
    (primitive lower upper polynomial scalar
               roots root-multiplicities
               quadratics quadratic-multiplicities)
  (and
   (putnam-1981-a5-rp-p scalar)
   (not
    (putnam-1981-a5-algebraic-zero-p
     primitive lower upper scalar))
   (putnam-1981-a5-algebraic-list-p roots)
   (putnam-1981-a5-positive-nat-list-p
    root-multiplicities)
   (equal (len roots) (len root-multiplicities))
   (putnam-1981-a5-pairwise-distinct-p
    primitive lower upper roots)
   (putnam-1981-a5-quadratic-list-p
    primitive lower upper quadratics)
   (putnam-1981-a5-positive-nat-list-p
    quadratic-multiplicities)
   (equal
    (len quadratics)
    (len quadratic-multiplicities))
   (putnam-1981-a5-polynomial-equal-at-alpha-p
    primitive
    lower
    upper
    polynomial
    (putnam-1981-a5-factorization-polynomial
     scalar roots root-multiplicities
     quadratics quadratic-multiplicities))))

(defun putnam-1981-a5-roots-greater-than-one
    (primitive lower upper roots)
  (if (consp roots)
      (+ (if (< 0
                (putnam-1981-a5-algebraic-sign
                 primitive
                 lower
                 upper
                 (putnam-1981-a5-rp-subtract
                  (car roots) (list 1))))
             1
           0)
         (putnam-1981-a5-roots-greater-than-one
          primitive lower upper (cdr roots)))
    0))

(defun putnam-1981-a5-counterexample-p
    (primitive lower upper coefficients
               p-scalar p-roots p-root-multiplicities
               p-quadratics p-quadratic-multiplicities
               q-scalar q-roots q-root-multiplicities
               q-quadratics q-quadratic-multiplicities)
  (let* ((polynomial
          (putnam-1981-a5-polynomial-normalize
           primitive lower upper coefficients))
         (q-polynomial
          (putnam-1981-a5-polynomial-normalize
           primitive lower upper
           (putnam-1981-a5-q-polynomial polynomial)))
         (n
          (putnam-1981-a5-roots-greater-than-one
           primitive lower upper p-roots)))
    (and
     (putnam-1981-a5-algebraic-list-p coefficients)
     (putnam-1981-a5-valid-factorization-p
      primitive lower upper polynomial
      p-scalar p-roots p-root-multiplicities
      p-quadratics p-quadratic-multiplicities)
     (putnam-1981-a5-valid-factorization-p
      primitive lower upper q-polynomial
      q-scalar q-roots q-root-multiplicities
      q-quadratics q-quadratic-multiplicities)
     (< (len q-roots) (- (* 2 n) 1)))))

(defun putnambench-putnam-1981-a5-statement
    (primitive lower upper coefficients
               p-scalar p-roots p-root-multiplicities
               p-quadratics p-quadratic-multiplicities
               q-scalar q-roots q-root-multiplicities
               q-quadratics q-quadratic-multiplicities)
  (implies
   (putnam-1981-a5-primitive-p primitive lower upper)
   (not
    (putnam-1981-a5-counterexample-p
     primitive lower upper coefficients
     p-scalar p-roots p-root-multiplicities
     p-quadratics p-quadratic-multiplicities
     q-scalar q-roots q-root-multiplicities
     q-quadratics q-quadratic-multiplicities))))

(value-triple :itpeval-statement-checked)
:q
