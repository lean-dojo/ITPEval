;; Statement-only formalization of PutnamBench corpus artifact putnam_2018_b2:
;; for every positive integer n, the polynomial
;; n + (n-1)z + ... + z^(n-1) has no zero in the closed complex unit disk.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Writing z=x+i*y makes the disk condition and both components of the
;; polynomial value integer-polynomial sign conditions. For each fixed n, a
;; counterexample is therefore a first-order formula over real closed fields,
;; so a complex counterexample exists exactly when one exists with real
;; algebraic x and y.
;;
;; Every pair of real algebraic numbers lies in Q(alpha) for one real
;; algebraic alpha. A rational polynomial with a rational isolating interval
;; encodes alpha, and rational polynomials in alpha encode x and y. The
;; Sturm-Tarski queries below decide signs at alpha exactly. Thus universal
;; closure of the final predicate is bidirectionally equivalent to the source
;; quantification over all complex z; it does not restrict z to complex
;; rationals or to a finite carrier. The source's auxiliary f is eliminated
;; by substituting its defining polynomial equality.

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-2018-b2-rp-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (putnam-2018-b2-rp-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-2018-b2-rp-normalize (polynomial)
  (if (consp polynomial)
      (if (equal (car polynomial) 0)
          (putnam-2018-b2-rp-normalize (cdr polynomial))
        polynomial)
    nil))

(defun putnam-2018-b2-rp-neg (polynomial)
  (if (consp polynomial)
      (cons (- (car polynomial))
            (putnam-2018-b2-rp-neg (cdr polynomial)))
    nil))

(defun putnam-2018-b2-rp-add-raw (left right)
  (declare (xargs :measure (+ (acl2-count left) (acl2-count right))))
  (cond
   ((endp left) right)
   ((endp right) left)
   ((< (len left) (len right))
    (cons (car right)
          (putnam-2018-b2-rp-add-raw left (cdr right))))
   ((< (len right) (len left))
    (cons (car left)
          (putnam-2018-b2-rp-add-raw (cdr left) right)))
   (t
    (cons (+ (car left) (car right))
          (putnam-2018-b2-rp-add-raw
           (cdr left) (cdr right))))))

(defun putnam-2018-b2-rp-add (left right)
  (putnam-2018-b2-rp-normalize
   (putnam-2018-b2-rp-add-raw left right)))

(defun putnam-2018-b2-rp-sub (left right)
  (putnam-2018-b2-rp-add
   left (putnam-2018-b2-rp-neg right)))

(defun putnam-2018-b2-rp-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-2018-b2-rp-scale scalar (cdr polynomial)))
    nil))

(defun putnam-2018-b2-zeroes (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0 (putnam-2018-b2-zeroes (- count 1)))))

(defun putnam-2018-b2-rp-scale-shift (scalar polynomial shift)
  (append (putnam-2018-b2-rp-scale scalar polynomial)
          (putnam-2018-b2-zeroes shift)))

(defun putnam-2018-b2-rp-mul-raw (left right)
  (if (consp left)
      (putnam-2018-b2-rp-add
       (putnam-2018-b2-rp-scale-shift
        (car left) right (len (cdr left)))
       (putnam-2018-b2-rp-mul-raw (cdr left) right))
    nil))

(defun putnam-2018-b2-rp-mul (left right)
  (putnam-2018-b2-rp-normalize
   (putnam-2018-b2-rp-mul-raw left right)))

(defun putnam-2018-b2-rp-eval-aux
    (polynomial value accumulator)
  (if (consp polynomial)
      (putnam-2018-b2-rp-eval-aux
       (cdr polynomial)
       value
       (+ (* accumulator value) (car polynomial)))
    accumulator))

(defun putnam-2018-b2-rp-eval (polynomial value)
  (putnam-2018-b2-rp-eval-aux polynomial value 0))

(defun putnam-2018-b2-rp-derivative-aux
    (polynomial degree)
  (if (consp polynomial)
      (if (zp degree)
          nil
        (cons (* degree (car polynomial))
              (putnam-2018-b2-rp-derivative-aux
               (cdr polynomial) (- degree 1))))
    nil))

(defun putnam-2018-b2-rp-derivative (polynomial)
  (let ((polynomial
         (putnam-2018-b2-rp-normalize polynomial)))
    (putnam-2018-b2-rp-normalize
     (putnam-2018-b2-rp-derivative-aux
      polynomial (nfix (- (len polynomial) 1))))))

(defun putnam-2018-b2-rp-rem-fuel
    (dividend divisor fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((dividend
         (putnam-2018-b2-rp-normalize dividend))
        (divisor
         (putnam-2018-b2-rp-normalize divisor)))
    (if (or (zp fuel)
            (endp divisor)
            (< (len dividend) (len divisor)))
        dividend
      (putnam-2018-b2-rp-rem-fuel
       (putnam-2018-b2-rp-sub
        dividend
        (putnam-2018-b2-rp-scale-shift
         (/ (car dividend) (car divisor))
         divisor
         (- (len dividend) (len divisor))))
       divisor
       (- fuel 1)))))

(defun putnam-2018-b2-rp-rem (dividend divisor)
  (putnam-2018-b2-rp-rem-fuel
   dividend
   divisor
   (+ 1 (len (putnam-2018-b2-rp-normalize dividend)))))

(defun putnam-2018-b2-rp-sturm-tail
    (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current (putnam-2018-b2-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-2018-b2-rp-sturm-tail
        current
        (putnam-2018-b2-rp-neg
         (putnam-2018-b2-rp-rem previous current))
        (- fuel 1))))))

(defun putnam-2018-b2-rp-sturm-sequence
    (polynomial second)
  (let ((polynomial
         (putnam-2018-b2-rp-normalize polynomial))
        (second
         (putnam-2018-b2-rp-normalize second)))
    (if (endp polynomial)
        nil
      (cons
       polynomial
       (if (endp second)
           nil
         (cons
          second
          (putnam-2018-b2-rp-sturm-tail
           polynomial
           second
           (+ 1 (len polynomial) (len second)))))))))

(defun putnam-2018-b2-rational-sign (value)
  (cond ((< value 0) -1)
        ((< 0 value) 1)
        (t 0)))

(defun putnam-2018-b2-rp-variations-aux
    (polynomials value previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-2018-b2-rational-sign
              (putnam-2018-b2-rp-eval
               (car polynomials) value))))
        (if (equal sign 0)
            (putnam-2018-b2-rp-variations-aux
             (cdr polynomials) value previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-2018-b2-rp-variations-aux
              (cdr polynomials) value sign))))
    0))

(defun putnam-2018-b2-rp-variations
    (polynomials value)
  (putnam-2018-b2-rp-variations-aux
   polynomials value 0))

(defun putnam-2018-b2-rp-cauchy-index
    (polynomial second lower upper)
  (let ((sequence
         (putnam-2018-b2-rp-sturm-sequence
          polynomial second)))
    (- (putnam-2018-b2-rp-variations sequence lower)
       (putnam-2018-b2-rp-variations sequence upper))))

(defun putnam-2018-b2-rp-root-count
    (polynomial lower upper)
  (putnam-2018-b2-rp-cauchy-index
   polynomial
   (putnam-2018-b2-rp-derivative polynomial)
   lower
   upper))

(defun putnam-2018-b2-primitive-p
    (primitive lower upper)
  (and
   (putnam-2018-b2-rp-p primitive)
   (consp (putnam-2018-b2-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not
    (equal
     (putnam-2018-b2-rp-eval primitive lower)
     0))
   (not
    (equal
     (putnam-2018-b2-rp-eval primitive upper)
     0))
   (equal
    (putnam-2018-b2-rp-root-count
     primitive lower upper)
    1)
   (not
    (equal
     (putnam-2018-b2-rp-cauchy-index
      primitive
      (putnam-2018-b2-rp-mul
       (putnam-2018-b2-rp-derivative primitive)
       (putnam-2018-b2-rp-derivative primitive))
      lower
      upper)
     0))))

;; For the isolated simple root alpha, this query is sign(P(alpha)).
(defun putnam-2018-b2-alg-sign
    (primitive lower upper polynomial)
  (putnam-2018-b2-rp-cauchy-index
   primitive
   (putnam-2018-b2-rp-mul
    (putnam-2018-b2-rp-derivative primitive)
    polynomial)
   lower
   upper))

(defun putnam-2018-b2-alg-zero-p
    (primitive lower upper polynomial)
  (equal
   (putnam-2018-b2-alg-sign
    primitive lower upper polynomial)
   0))

(defun putnam-2018-b2-alg-nonpositive-p
    (primitive lower upper polynomial)
  (<=
   (putnam-2018-b2-alg-sign
    primitive lower upper polynomial)
   0))

;; A complex algebraic expression is a pair of rational polynomials giving
;; its real and imaginary parts at alpha.

(defun putnam-2018-b2-cx-real (value)
  (car value))

(defun putnam-2018-b2-cx-imag (value)
  (cadr value))

(defun putnam-2018-b2-cx-add (left right)
  (list
   (putnam-2018-b2-rp-add
    (putnam-2018-b2-cx-real left)
    (putnam-2018-b2-cx-real right))
   (putnam-2018-b2-rp-add
    (putnam-2018-b2-cx-imag left)
    (putnam-2018-b2-cx-imag right))))

(defun putnam-2018-b2-cx-scale (scalar value)
  (list
   (putnam-2018-b2-rp-scale
    scalar (putnam-2018-b2-cx-real value))
   (putnam-2018-b2-rp-scale
    scalar (putnam-2018-b2-cx-imag value))))

(defun putnam-2018-b2-cx-mul (left right)
  (list
   (putnam-2018-b2-rp-sub
    (putnam-2018-b2-rp-mul
     (putnam-2018-b2-cx-real left)
     (putnam-2018-b2-cx-real right))
    (putnam-2018-b2-rp-mul
     (putnam-2018-b2-cx-imag left)
     (putnam-2018-b2-cx-imag right)))
   (putnam-2018-b2-rp-add
    (putnam-2018-b2-rp-mul
     (putnam-2018-b2-cx-real left)
     (putnam-2018-b2-cx-imag right))
    (putnam-2018-b2-rp-mul
     (putnam-2018-b2-cx-imag left)
     (putnam-2018-b2-cx-real right)))))

(defun putnam-2018-b2-polynomial-value-aux
    (z remaining power accumulator)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      accumulator
    (putnam-2018-b2-polynomial-value-aux
     z
     (- remaining 1)
     (putnam-2018-b2-cx-mul power z)
     (putnam-2018-b2-cx-add
      accumulator
      (putnam-2018-b2-cx-scale remaining power)))))

(defun putnam-2018-b2-polynomial-value (n x y)
  (putnam-2018-b2-polynomial-value-aux
   (list x y)
   n
   (list (list 1) nil)
   (list nil nil)))

(defun putnam-2018-b2-unit-disk-polynomial (x y)
  (putnam-2018-b2-rp-sub
   (putnam-2018-b2-rp-add
    (putnam-2018-b2-rp-mul x x)
    (putnam-2018-b2-rp-mul y y))
   (list 1)))

(defun putnambench-putnam-2018-b2-statement
    (n primitive lower upper x y)
  (let ((polynomial-value
         (putnam-2018-b2-polynomial-value n x y)))
    (implies
     (and
      (natp n)
      (< 0 n)
      (putnam-2018-b2-primitive-p primitive lower upper)
      (putnam-2018-b2-rp-p x)
      (putnam-2018-b2-rp-p y)
      (putnam-2018-b2-alg-nonpositive-p
       primitive lower upper
       (putnam-2018-b2-unit-disk-polynomial x y)))
     (not
      (and
       (putnam-2018-b2-alg-zero-p
        primitive lower upper
        (putnam-2018-b2-cx-real polynomial-value))
       (putnam-2018-b2-alg-zero-p
        primitive lower upper
        (putnam-2018-b2-cx-imag polynomial-value)))))))

(value-triple :itpeval-statement-checked)
:q
