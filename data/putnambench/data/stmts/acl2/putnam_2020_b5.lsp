;; Statement-only formalization of PutnamBench corpus artifact putnam_2020_b5:
;; four complex numbers of unit norm, each different from one, make
;; 3 - z1 - z2 - z3 - z4 + z1*z2*z3*z4 nonzero. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; In real and imaginary coordinates the hypotheses and conclusion are
;; first-order polynomial formulas over the reals. Real closed fields have
;; the same first-order theory, so a real counterexample exists exactly when
;; one exists over the real algebraic numbers.
;;
;; Every finite tuple of real algebraic numbers lies in Q(alpha) for a single
;; real algebraic alpha. A rational polynomial and rational isolating interval
;; encode alpha, and rational polynomials in alpha encode all eight
;; coordinates. The Sturm-Tarski queries below decide equality at alpha
;; exactly. Thus the final universally closed predicate covers all four
;; arbitrary complex inputs without restricting them to complex rationals.

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-2020-b5-rp-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (putnam-2020-b5-rp-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-2020-b5-rp-normalize (polynomial)
  (if (consp polynomial)
      (if (equal (car polynomial) 0)
          (putnam-2020-b5-rp-normalize (cdr polynomial))
        polynomial)
    nil))

(defun putnam-2020-b5-rp-neg (polynomial)
  (if (consp polynomial)
      (cons (- (car polynomial))
            (putnam-2020-b5-rp-neg (cdr polynomial)))
    nil))

(defun putnam-2020-b5-rp-add-raw (left right)
  (declare (xargs :measure (+ (acl2-count left) (acl2-count right))))
  (cond
   ((endp left) right)
   ((endp right) left)
   ((< (len left) (len right))
    (cons (car right)
          (putnam-2020-b5-rp-add-raw left (cdr right))))
   ((< (len right) (len left))
    (cons (car left)
          (putnam-2020-b5-rp-add-raw (cdr left) right)))
   (t
    (cons (+ (car left) (car right))
          (putnam-2020-b5-rp-add-raw
           (cdr left) (cdr right))))))

(defun putnam-2020-b5-rp-add (left right)
  (putnam-2020-b5-rp-normalize
   (putnam-2020-b5-rp-add-raw left right)))

(defun putnam-2020-b5-rp-sub (left right)
  (putnam-2020-b5-rp-add
   left (putnam-2020-b5-rp-neg right)))

(defun putnam-2020-b5-rp-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-2020-b5-rp-scale scalar (cdr polynomial)))
    nil))

(defun putnam-2020-b5-zeroes (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0 (putnam-2020-b5-zeroes (- count 1)))))

(defun putnam-2020-b5-rp-scale-shift (scalar polynomial shift)
  (append (putnam-2020-b5-rp-scale scalar polynomial)
          (putnam-2020-b5-zeroes shift)))

(defun putnam-2020-b5-rp-mul-raw (left right)
  (if (consp left)
      (putnam-2020-b5-rp-add
       (putnam-2020-b5-rp-scale-shift
        (car left) right (len (cdr left)))
       (putnam-2020-b5-rp-mul-raw (cdr left) right))
    nil))

(defun putnam-2020-b5-rp-mul (left right)
  (putnam-2020-b5-rp-normalize
   (putnam-2020-b5-rp-mul-raw left right)))

(defun putnam-2020-b5-rp-eval-aux
    (polynomial value accumulator)
  (if (consp polynomial)
      (putnam-2020-b5-rp-eval-aux
       (cdr polynomial)
       value
       (+ (* accumulator value) (car polynomial)))
    accumulator))

(defun putnam-2020-b5-rp-eval (polynomial value)
  (putnam-2020-b5-rp-eval-aux polynomial value 0))

(defun putnam-2020-b5-rp-derivative-aux
    (polynomial degree)
  (if (consp polynomial)
      (if (zp degree)
          nil
        (cons (* degree (car polynomial))
              (putnam-2020-b5-rp-derivative-aux
               (cdr polynomial) (- degree 1))))
    nil))

(defun putnam-2020-b5-rp-derivative (polynomial)
  (let ((polynomial
         (putnam-2020-b5-rp-normalize polynomial)))
    (putnam-2020-b5-rp-normalize
     (putnam-2020-b5-rp-derivative-aux
      polynomial (nfix (- (len polynomial) 1))))))

(defun putnam-2020-b5-rp-rem-fuel
    (dividend divisor fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((dividend
         (putnam-2020-b5-rp-normalize dividend))
        (divisor
         (putnam-2020-b5-rp-normalize divisor)))
    (if (or (zp fuel)
            (endp divisor)
            (< (len dividend) (len divisor)))
        dividend
      (putnam-2020-b5-rp-rem-fuel
       (putnam-2020-b5-rp-sub
        dividend
        (putnam-2020-b5-rp-scale-shift
         (/ (car dividend) (car divisor))
         divisor
         (- (len dividend) (len divisor))))
       divisor
       (- fuel 1)))))

(defun putnam-2020-b5-rp-rem (dividend divisor)
  (putnam-2020-b5-rp-rem-fuel
   dividend
   divisor
   (+ 1 (len (putnam-2020-b5-rp-normalize dividend)))))

(defun putnam-2020-b5-rp-sturm-tail
    (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current (putnam-2020-b5-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-2020-b5-rp-sturm-tail
        current
        (putnam-2020-b5-rp-neg
         (putnam-2020-b5-rp-rem previous current))
        (- fuel 1))))))

(defun putnam-2020-b5-rp-sturm-sequence
    (polynomial second)
  (let ((polynomial
         (putnam-2020-b5-rp-normalize polynomial))
        (second
         (putnam-2020-b5-rp-normalize second)))
    (if (endp polynomial)
        nil
      (cons
       polynomial
       (if (endp second)
           nil
         (cons
          second
          (putnam-2020-b5-rp-sturm-tail
           polynomial
           second
           (+ 1 (len polynomial) (len second)))))))))

(defun putnam-2020-b5-rational-sign (value)
  (cond ((< value 0) -1)
        ((< 0 value) 1)
        (t 0)))

(defun putnam-2020-b5-rp-variations-aux
    (polynomials value previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-2020-b5-rational-sign
              (putnam-2020-b5-rp-eval
               (car polynomials) value))))
        (if (equal sign 0)
            (putnam-2020-b5-rp-variations-aux
             (cdr polynomials) value previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-2020-b5-rp-variations-aux
              (cdr polynomials) value sign))))
    0))

(defun putnam-2020-b5-rp-variations
    (polynomials value)
  (putnam-2020-b5-rp-variations-aux
   polynomials value 0))

(defun putnam-2020-b5-rp-cauchy-index
    (polynomial second lower upper)
  (let ((sequence
         (putnam-2020-b5-rp-sturm-sequence
          polynomial second)))
    (- (putnam-2020-b5-rp-variations sequence lower)
       (putnam-2020-b5-rp-variations sequence upper))))

(defun putnam-2020-b5-rp-root-count
    (polynomial lower upper)
  (putnam-2020-b5-rp-cauchy-index
   polynomial
   (putnam-2020-b5-rp-derivative polynomial)
   lower
   upper))

(defun putnam-2020-b5-primitive-p
    (primitive lower upper)
  (and
   (putnam-2020-b5-rp-p primitive)
   (consp (putnam-2020-b5-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not
    (equal
     (putnam-2020-b5-rp-eval primitive lower)
     0))
   (not
    (equal
     (putnam-2020-b5-rp-eval primitive upper)
     0))
   (equal
    (putnam-2020-b5-rp-root-count
     primitive lower upper)
    1)
   (not
    (equal
     (putnam-2020-b5-rp-cauchy-index
      primitive
      (putnam-2020-b5-rp-mul
       (putnam-2020-b5-rp-derivative primitive)
       (putnam-2020-b5-rp-derivative primitive))
      lower
      upper)
     0))))

;; For the isolated simple root alpha, this Sturm-Tarski query is the sign of
;; polynomial(alpha).
(defun putnam-2020-b5-alg-sign
    (primitive lower upper polynomial)
  (putnam-2020-b5-rp-cauchy-index
   primitive
   (putnam-2020-b5-rp-mul
    (putnam-2020-b5-rp-derivative primitive)
    polynomial)
   lower
   upper))

(defun putnam-2020-b5-alg-zero-p
    (primitive lower upper polynomial)
  (equal
   (putnam-2020-b5-alg-sign
    primitive lower upper polynomial)
   0))

;; A complex algebraic expression is a pair of rational polynomials giving
;; its real and imaginary parts at alpha.

(defun putnam-2020-b5-cx-real (value)
  (car value))

(defun putnam-2020-b5-cx-imag (value)
  (cadr value))

(defun putnam-2020-b5-cx-constant (value)
  (list (list value) nil))

(defun putnam-2020-b5-cx-add (left right)
  (list
   (putnam-2020-b5-rp-add
    (putnam-2020-b5-cx-real left)
    (putnam-2020-b5-cx-real right))
   (putnam-2020-b5-rp-add
    (putnam-2020-b5-cx-imag left)
    (putnam-2020-b5-cx-imag right))))

(defun putnam-2020-b5-cx-neg (value)
  (list
   (putnam-2020-b5-rp-neg
    (putnam-2020-b5-cx-real value))
   (putnam-2020-b5-rp-neg
    (putnam-2020-b5-cx-imag value))))

(defun putnam-2020-b5-cx-sub (left right)
  (putnam-2020-b5-cx-add
   left (putnam-2020-b5-cx-neg right)))

(defun putnam-2020-b5-cx-mul (left right)
  (list
   (putnam-2020-b5-rp-sub
    (putnam-2020-b5-rp-mul
     (putnam-2020-b5-cx-real left)
     (putnam-2020-b5-cx-real right))
    (putnam-2020-b5-rp-mul
     (putnam-2020-b5-cx-imag left)
     (putnam-2020-b5-cx-imag right)))
   (putnam-2020-b5-rp-add
    (putnam-2020-b5-rp-mul
     (putnam-2020-b5-cx-real left)
     (putnam-2020-b5-cx-imag right))
    (putnam-2020-b5-rp-mul
     (putnam-2020-b5-cx-imag left)
     (putnam-2020-b5-cx-real right)))))

(defun putnam-2020-b5-unit-circle-polynomial (x y)
  (putnam-2020-b5-rp-sub
   (putnam-2020-b5-rp-add
    (putnam-2020-b5-rp-mul x x)
    (putnam-2020-b5-rp-mul y y))
   (list 1)))

(defun putnam-2020-b5-complex-one-p
    (primitive lower upper x y)
  (and
   (putnam-2020-b5-alg-zero-p
    primitive lower upper
    (putnam-2020-b5-rp-sub x (list 1)))
   (putnam-2020-b5-alg-zero-p
    primitive lower upper y)))

(defun putnam-2020-b5-expression
    (x1 y1 x2 y2 x3 y3 x4 y4)
  (let* ((z1 (list x1 y1))
         (z2 (list x2 y2))
         (z3 (list x3 y3))
         (z4 (list x4 y4))
         (sum-part
          (putnam-2020-b5-cx-sub
           (putnam-2020-b5-cx-sub
            (putnam-2020-b5-cx-sub
             (putnam-2020-b5-cx-sub
              (putnam-2020-b5-cx-constant 3)
              z1)
             z2)
            z3)
           z4))
         (product
          (putnam-2020-b5-cx-mul
           (putnam-2020-b5-cx-mul z1 z2)
           (putnam-2020-b5-cx-mul z3 z4))))
    (putnam-2020-b5-cx-add sum-part product)))

(defun putnambench-putnam-2020-b5-statement
    (primitive lower upper x1 y1 x2 y2 x3 y3 x4 y4)
  (let ((expression
         (putnam-2020-b5-expression
          x1 y1 x2 y2 x3 y3 x4 y4)))
    (implies
     (and
      (putnam-2020-b5-primitive-p primitive lower upper)
      (putnam-2020-b5-rp-p x1)
      (putnam-2020-b5-rp-p y1)
      (putnam-2020-b5-rp-p x2)
      (putnam-2020-b5-rp-p y2)
      (putnam-2020-b5-rp-p x3)
      (putnam-2020-b5-rp-p y3)
      (putnam-2020-b5-rp-p x4)
      (putnam-2020-b5-rp-p y4)
      (putnam-2020-b5-alg-zero-p
       primitive lower upper
       (putnam-2020-b5-unit-circle-polynomial x1 y1))
      (putnam-2020-b5-alg-zero-p
       primitive lower upper
       (putnam-2020-b5-unit-circle-polynomial x2 y2))
      (putnam-2020-b5-alg-zero-p
       primitive lower upper
       (putnam-2020-b5-unit-circle-polynomial x3 y3))
      (putnam-2020-b5-alg-zero-p
       primitive lower upper
       (putnam-2020-b5-unit-circle-polynomial x4 y4))
      (not
       (putnam-2020-b5-complex-one-p
        primitive lower upper x1 y1))
      (not
       (putnam-2020-b5-complex-one-p
        primitive lower upper x2 y2))
      (not
       (putnam-2020-b5-complex-one-p
        primitive lower upper x3 y3))
      (not
       (putnam-2020-b5-complex-one-p
        primitive lower upper x4 y4)))
     (not
      (and
       (putnam-2020-b5-alg-zero-p
        primitive lower upper
        (putnam-2020-b5-cx-real expression))
       (putnam-2020-b5-alg-zero-p
        primitive lower upper
        (putnam-2020-b5-cx-imag expression)))))))

(value-triple :itpeval-statement-checked)
:q
