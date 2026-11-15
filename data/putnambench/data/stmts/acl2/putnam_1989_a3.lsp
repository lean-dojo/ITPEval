;; Statement-only formalization of PutnamBench corpus artifact putnam_1989_a3:
;; every complex root of 11*z^10 + 10*i*z^9 + 10*i*z - 11 has modulus 1.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Writing z=x+i*y turns the hypothesis into two integer-polynomial
;; equalities and the conclusion into x^2+y^2=1. Thus a counterexample is a
;; first-order formula over real closed fields, so a real counterexample
;; exists if and only if one exists over the real algebraic numbers.
;;
;; Every pair of real algebraic numbers lies in Q(alpha) for one real
;; algebraic alpha. A rational polynomial and rational isolating interval
;; encode alpha, while rational polynomials in alpha encode x and y. The
;; Sturm-Tarski queries below decide equality at alpha exactly. Consequently,
;; universal closure of the final predicate covers every complex z without
;; narrowing the source domain to ACL2's complex rationals.

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-1989-a3-rp-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (putnam-1989-a3-rp-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-1989-a3-rp-normalize (polynomial)
  (if (consp polynomial)
      (if (equal (car polynomial) 0)
          (putnam-1989-a3-rp-normalize (cdr polynomial))
        polynomial)
    nil))

(defun putnam-1989-a3-rp-neg (polynomial)
  (if (consp polynomial)
      (cons (- (car polynomial))
            (putnam-1989-a3-rp-neg (cdr polynomial)))
    nil))

(defun putnam-1989-a3-rp-add-raw (left right)
  (declare (xargs :measure (+ (acl2-count left) (acl2-count right))))
  (cond
   ((endp left) right)
   ((endp right) left)
   ((< (len left) (len right))
    (cons (car right)
          (putnam-1989-a3-rp-add-raw left (cdr right))))
   ((< (len right) (len left))
    (cons (car left)
          (putnam-1989-a3-rp-add-raw (cdr left) right)))
   (t
    (cons (+ (car left) (car right))
          (putnam-1989-a3-rp-add-raw
           (cdr left) (cdr right))))))

(defun putnam-1989-a3-rp-add (left right)
  (putnam-1989-a3-rp-normalize
   (putnam-1989-a3-rp-add-raw left right)))

(defun putnam-1989-a3-rp-sub (left right)
  (putnam-1989-a3-rp-add
   left (putnam-1989-a3-rp-neg right)))

(defun putnam-1989-a3-rp-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-1989-a3-rp-scale scalar (cdr polynomial)))
    nil))

(defun putnam-1989-a3-zeroes (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0 (putnam-1989-a3-zeroes (- count 1)))))

(defun putnam-1989-a3-rp-scale-shift (scalar polynomial shift)
  (append (putnam-1989-a3-rp-scale scalar polynomial)
          (putnam-1989-a3-zeroes shift)))

(defun putnam-1989-a3-rp-mul-raw (left right)
  (if (consp left)
      (putnam-1989-a3-rp-add
       (putnam-1989-a3-rp-scale-shift
        (car left) right (len (cdr left)))
       (putnam-1989-a3-rp-mul-raw (cdr left) right))
    nil))

(defun putnam-1989-a3-rp-mul (left right)
  (putnam-1989-a3-rp-normalize
   (putnam-1989-a3-rp-mul-raw left right)))

(defun putnam-1989-a3-rp-eval-aux
    (polynomial value accumulator)
  (if (consp polynomial)
      (putnam-1989-a3-rp-eval-aux
       (cdr polynomial)
       value
       (+ (* accumulator value) (car polynomial)))
    accumulator))

(defun putnam-1989-a3-rp-eval (polynomial value)
  (putnam-1989-a3-rp-eval-aux polynomial value 0))

(defun putnam-1989-a3-rp-derivative-aux
    (polynomial degree)
  (if (consp polynomial)
      (if (zp degree)
          nil
        (cons (* degree (car polynomial))
              (putnam-1989-a3-rp-derivative-aux
               (cdr polynomial) (- degree 1))))
    nil))

(defun putnam-1989-a3-rp-derivative (polynomial)
  (let ((polynomial
         (putnam-1989-a3-rp-normalize polynomial)))
    (putnam-1989-a3-rp-normalize
     (putnam-1989-a3-rp-derivative-aux
      polynomial (nfix (- (len polynomial) 1))))))

(defun putnam-1989-a3-rp-rem-fuel
    (dividend divisor fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((dividend
         (putnam-1989-a3-rp-normalize dividend))
        (divisor
         (putnam-1989-a3-rp-normalize divisor)))
    (if (or (zp fuel)
            (endp divisor)
            (< (len dividend) (len divisor)))
        dividend
      (putnam-1989-a3-rp-rem-fuel
       (putnam-1989-a3-rp-sub
        dividend
        (putnam-1989-a3-rp-scale-shift
         (/ (car dividend) (car divisor))
         divisor
         (- (len dividend) (len divisor))))
       divisor
       (- fuel 1)))))

(defun putnam-1989-a3-rp-rem (dividend divisor)
  (putnam-1989-a3-rp-rem-fuel
   dividend
   divisor
   (+ 1 (len (putnam-1989-a3-rp-normalize dividend)))))

(defun putnam-1989-a3-rp-sturm-tail
    (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current (putnam-1989-a3-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-1989-a3-rp-sturm-tail
        current
        (putnam-1989-a3-rp-neg
         (putnam-1989-a3-rp-rem previous current))
        (- fuel 1))))))

(defun putnam-1989-a3-rp-sturm-sequence
    (polynomial second)
  (let ((polynomial
         (putnam-1989-a3-rp-normalize polynomial))
        (second
         (putnam-1989-a3-rp-normalize second)))
    (if (endp polynomial)
        nil
      (cons
       polynomial
       (if (endp second)
           nil
         (cons
          second
          (putnam-1989-a3-rp-sturm-tail
           polynomial
           second
           (+ 1 (len polynomial) (len second)))))))))

(defun putnam-1989-a3-rational-sign (value)
  (cond ((< value 0) -1)
        ((< 0 value) 1)
        (t 0)))

(defun putnam-1989-a3-rp-variations-aux
    (polynomials value previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-1989-a3-rational-sign
              (putnam-1989-a3-rp-eval
               (car polynomials) value))))
        (if (equal sign 0)
            (putnam-1989-a3-rp-variations-aux
             (cdr polynomials) value previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-1989-a3-rp-variations-aux
              (cdr polynomials) value sign))))
    0))

(defun putnam-1989-a3-rp-variations
    (polynomials value)
  (putnam-1989-a3-rp-variations-aux
   polynomials value 0))

(defun putnam-1989-a3-rp-cauchy-index
    (polynomial second lower upper)
  (let ((sequence
         (putnam-1989-a3-rp-sturm-sequence
          polynomial second)))
    (- (putnam-1989-a3-rp-variations sequence lower)
       (putnam-1989-a3-rp-variations sequence upper))))

(defun putnam-1989-a3-rp-root-count
    (polynomial lower upper)
  (putnam-1989-a3-rp-cauchy-index
   polynomial
   (putnam-1989-a3-rp-derivative polynomial)
   lower
   upper))

(defun putnam-1989-a3-primitive-p
    (primitive lower upper)
  (and
   (putnam-1989-a3-rp-p primitive)
   (consp (putnam-1989-a3-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not
    (equal
     (putnam-1989-a3-rp-eval primitive lower)
     0))
   (not
    (equal
     (putnam-1989-a3-rp-eval primitive upper)
     0))
   (equal
    (putnam-1989-a3-rp-root-count
     primitive lower upper)
    1)
   (not
    (equal
     (putnam-1989-a3-rp-cauchy-index
      primitive
      (putnam-1989-a3-rp-mul
       (putnam-1989-a3-rp-derivative primitive)
       (putnam-1989-a3-rp-derivative primitive))
      lower
      upper)
     0))))

;; For the isolated simple root alpha, this Sturm-Tarski query is
;; sign(polynomial(alpha)).
(defun putnam-1989-a3-alg-sign
    (primitive lower upper polynomial)
  (putnam-1989-a3-rp-cauchy-index
   primitive
   (putnam-1989-a3-rp-mul
    (putnam-1989-a3-rp-derivative primitive)
    polynomial)
   lower
   upper))

(defun putnam-1989-a3-alg-zero-p
    (primitive lower upper polynomial)
  (equal
   (putnam-1989-a3-alg-sign
    primitive lower upper polynomial)
   0))

;; A complex algebraic expression is a pair of rational polynomials giving
;; its real and imaginary parts at alpha.

(defun putnam-1989-a3-cx-real (value)
  (car value))

(defun putnam-1989-a3-cx-imag (value)
  (cadr value))

(defun putnam-1989-a3-cx-add (left right)
  (list
   (putnam-1989-a3-rp-add
    (putnam-1989-a3-cx-real left)
    (putnam-1989-a3-cx-real right))
   (putnam-1989-a3-rp-add
    (putnam-1989-a3-cx-imag left)
    (putnam-1989-a3-cx-imag right))))

(defun putnam-1989-a3-cx-neg (value)
  (list
   (putnam-1989-a3-rp-neg
    (putnam-1989-a3-cx-real value))
   (putnam-1989-a3-rp-neg
    (putnam-1989-a3-cx-imag value))))

(defun putnam-1989-a3-cx-sub (left right)
  (putnam-1989-a3-cx-add
   left (putnam-1989-a3-cx-neg right)))

(defun putnam-1989-a3-cx-scale (scalar value)
  (list
   (putnam-1989-a3-rp-scale
    scalar (putnam-1989-a3-cx-real value))
   (putnam-1989-a3-rp-scale
    scalar (putnam-1989-a3-cx-imag value))))

(defun putnam-1989-a3-cx-mul (left right)
  (list
   (putnam-1989-a3-rp-sub
    (putnam-1989-a3-rp-mul
     (putnam-1989-a3-cx-real left)
     (putnam-1989-a3-cx-real right))
    (putnam-1989-a3-rp-mul
     (putnam-1989-a3-cx-imag left)
     (putnam-1989-a3-cx-imag right)))
   (putnam-1989-a3-rp-add
    (putnam-1989-a3-rp-mul
     (putnam-1989-a3-cx-real left)
     (putnam-1989-a3-cx-imag right))
    (putnam-1989-a3-rp-mul
     (putnam-1989-a3-cx-imag left)
     (putnam-1989-a3-cx-real right)))))

(defun putnam-1989-a3-cx-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (list (list 1) nil)
    (putnam-1989-a3-cx-mul
     value
     (putnam-1989-a3-cx-pow value (- exponent 1)))))

(defun putnam-1989-a3-polynomial-value (x y)
  (let* ((z (list x y))
         (imaginary-unit (list nil (list 1))))
    (putnam-1989-a3-cx-sub
     (putnam-1989-a3-cx-add
      (putnam-1989-a3-cx-scale
       11 (putnam-1989-a3-cx-pow z 10))
      (putnam-1989-a3-cx-add
       (putnam-1989-a3-cx-scale
        10
        (putnam-1989-a3-cx-mul
         imaginary-unit
         (putnam-1989-a3-cx-pow z 9)))
       (putnam-1989-a3-cx-scale
        10
        (putnam-1989-a3-cx-mul imaginary-unit z))))
     (list (list 11) nil))))

(defun putnam-1989-a3-unit-circle-polynomial (x y)
  (putnam-1989-a3-rp-sub
   (putnam-1989-a3-rp-add
    (putnam-1989-a3-rp-mul x x)
    (putnam-1989-a3-rp-mul y y))
   (list 1)))

(defun putnambench-putnam-1989-a3-statement
    (primitive lower upper x y)
  (let ((polynomial-value
         (putnam-1989-a3-polynomial-value x y)))
    (implies
     (and
      (putnam-1989-a3-primitive-p primitive lower upper)
      (putnam-1989-a3-rp-p x)
      (putnam-1989-a3-rp-p y)
      (putnam-1989-a3-alg-zero-p
       primitive lower upper
       (putnam-1989-a3-cx-real polynomial-value))
      (putnam-1989-a3-alg-zero-p
       primitive lower upper
       (putnam-1989-a3-cx-imag polynomial-value)))
     (putnam-1989-a3-alg-zero-p
      primitive lower upper
      (putnam-1989-a3-unit-circle-polynomial x y)))))

(value-triple :itpeval-statement-checked)
:q
