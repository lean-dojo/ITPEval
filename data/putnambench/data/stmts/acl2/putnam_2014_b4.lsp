;; Statement-only formalization of PutnamBench corpus artifact putnam_2014_b4:
;; for every positive integer n, every complex root of the polynomial whose
;; coefficient of z^k is 2^(k*(n-k)) is real. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source polynomial is uniquely determined by n, so its coefficient
;; condition is represented definitionally by the finite sum below. Writing
;; z=x+i*y turns the root condition into two integer-polynomial equalities
;; and the conclusion into y=0. Thus a counterexample is a first-order
;; formula over real closed fields, so a real counterexample exists if and
;; only if one exists over the real algebraic numbers.
;;
;; Every pair of real algebraic numbers lies in Q(alpha) for one real
;; algebraic alpha. A rational polynomial and rational isolating interval
;; encode alpha, while rational polynomials in alpha encode x and y. The
;; Sturm-Tarski queries below decide equality at alpha exactly. Consequently,
;; universal closure of the final predicate covers every complex z without
;; narrowing the source domain to ACL2's complex rationals.

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-2014-b4-rp-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (putnam-2014-b4-rp-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-2014-b4-rp-normalize (polynomial)
  (if (consp polynomial)
      (if (equal (car polynomial) 0)
          (putnam-2014-b4-rp-normalize (cdr polynomial))
        polynomial)
    nil))

(defun putnam-2014-b4-rp-neg (polynomial)
  (if (consp polynomial)
      (cons (- (car polynomial))
            (putnam-2014-b4-rp-neg (cdr polynomial)))
    nil))

(defun putnam-2014-b4-rp-add-raw (left right)
  (declare (xargs :measure (+ (acl2-count left) (acl2-count right))))
  (cond
   ((endp left) right)
   ((endp right) left)
   ((< (len left) (len right))
    (cons (car right)
          (putnam-2014-b4-rp-add-raw left (cdr right))))
   ((< (len right) (len left))
    (cons (car left)
          (putnam-2014-b4-rp-add-raw (cdr left) right)))
   (t
    (cons (+ (car left) (car right))
          (putnam-2014-b4-rp-add-raw
           (cdr left) (cdr right))))))

(defun putnam-2014-b4-rp-add (left right)
  (putnam-2014-b4-rp-normalize
   (putnam-2014-b4-rp-add-raw left right)))

(defun putnam-2014-b4-rp-sub (left right)
  (putnam-2014-b4-rp-add
   left (putnam-2014-b4-rp-neg right)))

(defun putnam-2014-b4-rp-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-2014-b4-rp-scale scalar (cdr polynomial)))
    nil))

(defun putnam-2014-b4-zeroes (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0 (putnam-2014-b4-zeroes (- count 1)))))

(defun putnam-2014-b4-rp-scale-shift (scalar polynomial shift)
  (append (putnam-2014-b4-rp-scale scalar polynomial)
          (putnam-2014-b4-zeroes shift)))

(defun putnam-2014-b4-rp-mul-raw (left right)
  (if (consp left)
      (putnam-2014-b4-rp-add
       (putnam-2014-b4-rp-scale-shift
        (car left) right (len (cdr left)))
       (putnam-2014-b4-rp-mul-raw (cdr left) right))
    nil))

(defun putnam-2014-b4-rp-mul (left right)
  (putnam-2014-b4-rp-normalize
   (putnam-2014-b4-rp-mul-raw left right)))

(defun putnam-2014-b4-rp-eval-aux
    (polynomial value accumulator)
  (if (consp polynomial)
      (putnam-2014-b4-rp-eval-aux
       (cdr polynomial)
       value
       (+ (* accumulator value) (car polynomial)))
    accumulator))

(defun putnam-2014-b4-rp-eval (polynomial value)
  (putnam-2014-b4-rp-eval-aux polynomial value 0))

(defun putnam-2014-b4-rp-derivative-aux
    (polynomial degree)
  (if (consp polynomial)
      (if (zp degree)
          nil
        (cons (* degree (car polynomial))
              (putnam-2014-b4-rp-derivative-aux
               (cdr polynomial) (- degree 1))))
    nil))

(defun putnam-2014-b4-rp-derivative (polynomial)
  (let ((polynomial
         (putnam-2014-b4-rp-normalize polynomial)))
    (putnam-2014-b4-rp-normalize
     (putnam-2014-b4-rp-derivative-aux
      polynomial (nfix (- (len polynomial) 1))))))

(defun putnam-2014-b4-rp-rem-fuel
    (dividend divisor fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((dividend
         (putnam-2014-b4-rp-normalize dividend))
        (divisor
         (putnam-2014-b4-rp-normalize divisor)))
    (if (or (zp fuel)
            (endp divisor)
            (< (len dividend) (len divisor)))
        dividend
      (putnam-2014-b4-rp-rem-fuel
       (putnam-2014-b4-rp-sub
        dividend
        (putnam-2014-b4-rp-scale-shift
         (/ (car dividend) (car divisor))
         divisor
         (- (len dividend) (len divisor))))
       divisor
       (- fuel 1)))))

(defun putnam-2014-b4-rp-rem (dividend divisor)
  (putnam-2014-b4-rp-rem-fuel
   dividend
   divisor
   (+ 1 (len (putnam-2014-b4-rp-normalize dividend)))))

(defun putnam-2014-b4-rp-sturm-tail
    (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current (putnam-2014-b4-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-2014-b4-rp-sturm-tail
        current
        (putnam-2014-b4-rp-neg
         (putnam-2014-b4-rp-rem previous current))
        (- fuel 1))))))

(defun putnam-2014-b4-rp-sturm-sequence
    (polynomial second)
  (let ((polynomial
         (putnam-2014-b4-rp-normalize polynomial))
        (second
         (putnam-2014-b4-rp-normalize second)))
    (if (endp polynomial)
        nil
      (cons
       polynomial
       (if (endp second)
           nil
         (cons
          second
          (putnam-2014-b4-rp-sturm-tail
           polynomial
           second
           (+ 1 (len polynomial) (len second)))))))))

(defun putnam-2014-b4-rational-sign (value)
  (cond ((< value 0) -1)
        ((< 0 value) 1)
        (t 0)))

(defun putnam-2014-b4-rp-variations-aux
    (polynomials value previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-2014-b4-rational-sign
              (putnam-2014-b4-rp-eval
               (car polynomials) value))))
        (if (equal sign 0)
            (putnam-2014-b4-rp-variations-aux
             (cdr polynomials) value previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-2014-b4-rp-variations-aux
              (cdr polynomials) value sign))))
    0))

(defun putnam-2014-b4-rp-variations
    (polynomials value)
  (putnam-2014-b4-rp-variations-aux
   polynomials value 0))

(defun putnam-2014-b4-rp-cauchy-index
    (polynomial second lower upper)
  (let ((sequence
         (putnam-2014-b4-rp-sturm-sequence
          polynomial second)))
    (- (putnam-2014-b4-rp-variations sequence lower)
       (putnam-2014-b4-rp-variations sequence upper))))

(defun putnam-2014-b4-rp-root-count
    (polynomial lower upper)
  (putnam-2014-b4-rp-cauchy-index
   polynomial
   (putnam-2014-b4-rp-derivative polynomial)
   lower
   upper))

(defun putnam-2014-b4-primitive-p
    (primitive lower upper)
  (and
   (putnam-2014-b4-rp-p primitive)
   (consp (putnam-2014-b4-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not
    (equal
     (putnam-2014-b4-rp-eval primitive lower)
     0))
   (not
    (equal
     (putnam-2014-b4-rp-eval primitive upper)
     0))
   (equal
    (putnam-2014-b4-rp-root-count
     primitive lower upper)
    1)
   (not
    (equal
     (putnam-2014-b4-rp-cauchy-index
      primitive
      (putnam-2014-b4-rp-mul
       (putnam-2014-b4-rp-derivative primitive)
       (putnam-2014-b4-rp-derivative primitive))
      lower
      upper)
     0))))

;; For the isolated simple root alpha, this Sturm-Tarski query is
;; sign(polynomial(alpha)).
(defun putnam-2014-b4-alg-sign
    (primitive lower upper polynomial)
  (putnam-2014-b4-rp-cauchy-index
   primitive
   (putnam-2014-b4-rp-mul
    (putnam-2014-b4-rp-derivative primitive)
    polynomial)
   lower
   upper))

(defun putnam-2014-b4-alg-zero-p
    (primitive lower upper polynomial)
  (equal
   (putnam-2014-b4-alg-sign
    primitive lower upper polynomial)
   0))

;; A complex algebraic expression is a pair of rational polynomials giving
;; its real and imaginary parts at alpha.

(defun putnam-2014-b4-cx-real (value)
  (car value))

(defun putnam-2014-b4-cx-imag (value)
  (cadr value))

(defun putnam-2014-b4-cx-add (left right)
  (list
   (putnam-2014-b4-rp-add
    (putnam-2014-b4-cx-real left)
    (putnam-2014-b4-cx-real right))
   (putnam-2014-b4-rp-add
    (putnam-2014-b4-cx-imag left)
    (putnam-2014-b4-cx-imag right))))

(defun putnam-2014-b4-cx-neg (value)
  (list
   (putnam-2014-b4-rp-neg
    (putnam-2014-b4-cx-real value))
   (putnam-2014-b4-rp-neg
    (putnam-2014-b4-cx-imag value))))

(defun putnam-2014-b4-cx-sub (left right)
  (putnam-2014-b4-cx-add
   left (putnam-2014-b4-cx-neg right)))

(defun putnam-2014-b4-cx-scale (scalar value)
  (list
   (putnam-2014-b4-rp-scale
    scalar (putnam-2014-b4-cx-real value))
   (putnam-2014-b4-rp-scale
    scalar (putnam-2014-b4-cx-imag value))))

(defun putnam-2014-b4-cx-mul (left right)
  (list
   (putnam-2014-b4-rp-sub
    (putnam-2014-b4-rp-mul
     (putnam-2014-b4-cx-real left)
     (putnam-2014-b4-cx-real right))
    (putnam-2014-b4-rp-mul
     (putnam-2014-b4-cx-imag left)
     (putnam-2014-b4-cx-imag right)))
   (putnam-2014-b4-rp-add
    (putnam-2014-b4-rp-mul
     (putnam-2014-b4-cx-real left)
     (putnam-2014-b4-cx-imag right))
    (putnam-2014-b4-rp-mul
     (putnam-2014-b4-cx-imag left)
     (putnam-2014-b4-cx-real right)))))

(defun putnam-2014-b4-cx-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (list (list 1) nil)
    (putnam-2014-b4-cx-mul
     value
     (putnam-2014-b4-cx-pow value (- exponent 1)))))

(defun putnam-2014-b4-polynomial-value-aux
    (z n k remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (list nil nil)
    (putnam-2014-b4-cx-add
     (putnam-2014-b4-cx-scale
      (expt 2 (* k (- n k)))
      (putnam-2014-b4-cx-pow z k))
     (putnam-2014-b4-polynomial-value-aux
      z n (+ k 1) (- remaining 1)))))

(defun putnam-2014-b4-polynomial-value (x y n)
  (putnam-2014-b4-polynomial-value-aux
   (list x y) n 0 (+ n 1)))

(defun putnambench-putnam-2014-b4-statement
    (n primitive lower upper x y)
  (let ((polynomial-value
         (putnam-2014-b4-polynomial-value x y n)))
    (implies
     (and
      (posp n)
      (putnam-2014-b4-primitive-p primitive lower upper)
      (putnam-2014-b4-rp-p x)
      (putnam-2014-b4-rp-p y)
      (putnam-2014-b4-alg-zero-p
       primitive lower upper
       (putnam-2014-b4-cx-real polynomial-value))
      (putnam-2014-b4-alg-zero-p
       primitive lower upper
       (putnam-2014-b4-cx-imag polynomial-value)))
     (putnam-2014-b4-alg-zero-p
      primitive lower upper y))))

(value-triple :itpeval-statement-checked)
:q
