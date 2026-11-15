;; Statement-only formalization of PutnamBench corpus artifact putnam_1997_a6:
;; the recurrence at the greatest real zero of its (n+1)-st term has values
;; choose(n-1,k-1) for 1 <= k <= n. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; For fixed positive natural N, every recurrence term is a rational
;; polynomial in the real parameter c. The source sequence is uniquely
;; determined by x_0=0, x_1=1, and the recurrence, so these polynomials are a
;; definitional encoding of the arbitrary source function x.
;;
;; Every zero of the (N+1)-st polynomial is real algebraic. PRIMITIVE and the
;; rational interval (LOWER,UPPER) represent its isolated algebraic value
;; alpha. Sturm-Tarski queries decide polynomial signs at alpha exactly, while
;; Sturm root counts and a strict Cauchy bound state that alpha is the greatest
;; real zero. Thus this representation ranges over the source's real maximum,
;; not merely ACL2's executable rationals.

;; Rational polynomials use descending coefficient order.

(defun putnam-1997-a6-rp-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (putnam-1997-a6-rp-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-1997-a6-rp-normalize (polynomial)
  (if (consp polynomial)
      (if (equal (car polynomial) 0)
          (putnam-1997-a6-rp-normalize (cdr polynomial))
        polynomial)
    nil))

(defun putnam-1997-a6-rp-neg (polynomial)
  (if (consp polynomial)
      (cons (- (car polynomial))
            (putnam-1997-a6-rp-neg (cdr polynomial)))
    nil))

(defun putnam-1997-a6-rp-add-raw (left right)
  (declare
   (xargs :measure (+ (acl2-count left) (acl2-count right))))
  (cond
   ((endp left) right)
   ((endp right) left)
   ((< (len left) (len right))
    (cons (car right)
          (putnam-1997-a6-rp-add-raw left (cdr right))))
   ((< (len right) (len left))
    (cons (car left)
          (putnam-1997-a6-rp-add-raw (cdr left) right)))
   (t
    (cons (+ (car left) (car right))
          (putnam-1997-a6-rp-add-raw
           (cdr left) (cdr right))))))

(defun putnam-1997-a6-rp-add (left right)
  (putnam-1997-a6-rp-normalize
   (putnam-1997-a6-rp-add-raw left right)))

(defun putnam-1997-a6-rp-sub (left right)
  (putnam-1997-a6-rp-add
   left (putnam-1997-a6-rp-neg right)))

(defun putnam-1997-a6-rp-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-1997-a6-rp-scale scalar (cdr polynomial)))
    nil))

(defun putnam-1997-a6-zeroes (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0 (putnam-1997-a6-zeroes (- count 1)))))

(defun putnam-1997-a6-rp-scale-shift
    (scalar polynomial shift)
  (append
   (putnam-1997-a6-rp-scale scalar polynomial)
   (putnam-1997-a6-zeroes shift)))

(defun putnam-1997-a6-rp-mul-raw (left right)
  (if (consp left)
      (putnam-1997-a6-rp-add
       (putnam-1997-a6-rp-scale-shift
        (car left) right (len (cdr left)))
       (putnam-1997-a6-rp-mul-raw (cdr left) right))
    nil))

(defun putnam-1997-a6-rp-mul (left right)
  (putnam-1997-a6-rp-normalize
   (putnam-1997-a6-rp-mul-raw left right)))

(defun putnam-1997-a6-rp-eval-aux
    (polynomial value accumulator)
  (if (consp polynomial)
      (putnam-1997-a6-rp-eval-aux
       (cdr polynomial)
       value
       (+ (* accumulator value) (car polynomial)))
    accumulator))

(defun putnam-1997-a6-rp-eval (polynomial value)
  (putnam-1997-a6-rp-eval-aux polynomial value 0))

(defun putnam-1997-a6-rp-derivative-aux
    (polynomial degree)
  (if (consp polynomial)
      (if (zp degree)
          nil
        (cons
         (* degree (car polynomial))
         (putnam-1997-a6-rp-derivative-aux
          (cdr polynomial) (- degree 1))))
    nil))

(defun putnam-1997-a6-rp-derivative (polynomial)
  (let ((polynomial
         (putnam-1997-a6-rp-normalize polynomial)))
    (putnam-1997-a6-rp-normalize
     (putnam-1997-a6-rp-derivative-aux
      polynomial
      (nfix (- (len polynomial) 1))))))

(defun putnam-1997-a6-rp-rem-fuel
    (dividend divisor fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((dividend
         (putnam-1997-a6-rp-normalize dividend))
        (divisor
         (putnam-1997-a6-rp-normalize divisor)))
    (if (or (zp fuel)
            (endp divisor)
            (< (len dividend) (len divisor)))
        dividend
      (putnam-1997-a6-rp-rem-fuel
       (putnam-1997-a6-rp-sub
        dividend
        (putnam-1997-a6-rp-scale-shift
         (/ (car dividend) (car divisor))
         divisor
         (- (len dividend) (len divisor))))
       divisor
       (- fuel 1)))))

(defun putnam-1997-a6-rp-rem (dividend divisor)
  (putnam-1997-a6-rp-rem-fuel
   dividend
   divisor
   (+ 1 (len (putnam-1997-a6-rp-normalize dividend)))))

(defun putnam-1997-a6-rp-sturm-tail
    (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current
         (putnam-1997-a6-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-1997-a6-rp-sturm-tail
        current
        (putnam-1997-a6-rp-neg
         (putnam-1997-a6-rp-rem previous current))
        (- fuel 1))))))

(defun putnam-1997-a6-rp-sturm-sequence
    (polynomial second)
  (let ((polynomial
         (putnam-1997-a6-rp-normalize polynomial))
        (second
         (putnam-1997-a6-rp-normalize second)))
    (if (endp polynomial)
        nil
      (cons
       polynomial
       (if (endp second)
           nil
         (cons
          second
          (putnam-1997-a6-rp-sturm-tail
           polynomial
           second
           (+ 1 (len polynomial) (len second)))))))))

(defun putnam-1997-a6-rational-sign (value)
  (cond ((< value 0) -1)
        ((< 0 value) 1)
        (t 0)))

(defun putnam-1997-a6-rp-variations-aux
    (polynomials value previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-1997-a6-rational-sign
              (putnam-1997-a6-rp-eval
               (car polynomials) value))))
        (if (equal sign 0)
            (putnam-1997-a6-rp-variations-aux
             (cdr polynomials) value previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-1997-a6-rp-variations-aux
              (cdr polynomials) value sign))))
    0))

(defun putnam-1997-a6-rp-variations
    (polynomials value)
  (putnam-1997-a6-rp-variations-aux
   polynomials value 0))

(defun putnam-1997-a6-rp-cauchy-index
    (polynomial second lower upper)
  (let ((sequence
         (putnam-1997-a6-rp-sturm-sequence
          polynomial second)))
    (- (putnam-1997-a6-rp-variations sequence lower)
       (putnam-1997-a6-rp-variations sequence upper))))

(defun putnam-1997-a6-rp-root-count
    (polynomial lower upper)
  (putnam-1997-a6-rp-cauchy-index
   polynomial
   (putnam-1997-a6-rp-derivative polynomial)
   lower
   upper))

(defun putnam-1997-a6-primitive-p
    (primitive lower upper)
  (and
   (putnam-1997-a6-rp-p primitive)
   (consp (putnam-1997-a6-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not
    (equal
     (putnam-1997-a6-rp-eval primitive lower)
     0))
   (not
    (equal
     (putnam-1997-a6-rp-eval primitive upper)
     0))
   (equal
    (putnam-1997-a6-rp-root-count
     primitive lower upper)
    1)
   (not
    (equal
     (putnam-1997-a6-rp-cauchy-index
      primitive
      (putnam-1997-a6-rp-mul
       (putnam-1997-a6-rp-derivative primitive)
       (putnam-1997-a6-rp-derivative primitive))
      lower
      upper)
     0))))

;; For the isolated simple root alpha, this Sturm-Tarski query is the sign of
;; POLYNOMIAL(alpha).
(defun putnam-1997-a6-alg-sign
    (primitive lower upper polynomial)
  (putnam-1997-a6-rp-cauchy-index
   primitive
   (putnam-1997-a6-rp-mul
    (putnam-1997-a6-rp-derivative primitive)
    polynomial)
   lower
   upper))

(defun putnam-1997-a6-alg-zero-p
    (primitive lower upper polynomial)
  (equal
   (putnam-1997-a6-alg-sign
    primitive lower upper polynomial)
   0))

(defun putnam-1997-a6-rp-max-ratio
    (coefficients leading maximum)
  (if (consp coefficients)
      (let ((ratio (abs (/ (car coefficients) leading))))
        (putnam-1997-a6-rp-max-ratio
         (cdr coefficients)
         leading
         (if (< maximum ratio) ratio maximum)))
    maximum))

;; Every real zero of a nonconstant nonzero polynomial lies strictly between
;; the negative and positive values of this Cauchy bound.
(defun putnam-1997-a6-rp-root-bound (polynomial)
  (let ((polynomial
         (putnam-1997-a6-rp-normalize polynomial)))
    (if (or (endp polynomial) (endp (cdr polynomial)))
        1
      (+ 1
         (putnam-1997-a6-rp-max-ratio
          (cdr polynomial) (car polynomial) 0)))))

(defun putnam-1997-a6-recurrence-polynomial (n index)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      nil
    (cond
     ((equal index 0) nil)
     ((equal index 1) (list 1))
     (t
      (let ((k (- index 2)))
        (putnam-1997-a6-rp-scale
         (/ 1 (+ k 1))
         (putnam-1997-a6-rp-sub
          (putnam-1997-a6-rp-scale-shift
           1
           (putnam-1997-a6-recurrence-polynomial
            n (- index 1))
           1)
          (putnam-1997-a6-rp-scale
           (- n k)
           (putnam-1997-a6-recurrence-polynomial
            n (- index 2))))))))))

(defun putnam-1997-a6-binomial (n k)
  (declare (xargs :measure (nfix n)))
  (cond
   ((or (not (natp n))
        (not (natp k))
        (< n k))
    0)
   ((equal k 0) 1)
   ((equal n 0) 0)
   (t
    (+ (putnam-1997-a6-binomial (- n 1) k)
       (putnam-1997-a6-binomial (- n 1) (- k 1))))))

(defun putnam-1997-a6-greatest-root-p
    (n primitive lower upper)
  (let* ((polynomial
          (putnam-1997-a6-recurrence-polynomial
           n (+ n 1)))
         (bound
          (putnam-1997-a6-rp-root-bound polynomial)))
    (and
     (putnam-1997-a6-primitive-p primitive lower upper)
     (putnam-1997-a6-alg-zero-p
      primitive lower upper polynomial)
     (not
      (equal
       (putnam-1997-a6-rp-eval polynomial lower)
       0))
     (not
      (equal
       (putnam-1997-a6-rp-eval polynomial upper)
       0))
     (equal
      (putnam-1997-a6-rp-root-count
       polynomial lower upper)
      1)
     (< upper bound)
     (not
      (equal
       (putnam-1997-a6-rp-eval polynomial bound)
       0))
     (equal
      (putnam-1997-a6-rp-root-count
       polynomial upper bound)
      0))))

(defun putnambench-putnam-1997-a6-statement
    (n k primitive lower upper)
  (implies
   (and
    (posp n)
    (natp k)
    (<= 1 k)
    (<= k n)
    (putnam-1997-a6-greatest-root-p
     n primitive lower upper))
   (putnam-1997-a6-alg-zero-p
    primitive
    lower
    upper
    (putnam-1997-a6-rp-sub
     (putnam-1997-a6-recurrence-polynomial n k)
     (list
      (putnam-1997-a6-binomial
       (- n 1) (- k 1)))))))

(value-triple :itpeval-statement-checked)
:q
