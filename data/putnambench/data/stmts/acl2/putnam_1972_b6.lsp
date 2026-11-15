;; Statement-only formalization of PutnamBench corpus artifact putnam_1972_b6:
;; a polynomial with constant term one and strictly increasing positive
;; integer exponents has no complex zero of modulus less than
;; (sqrt(5)-1)/2. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A zero of the source integer polynomial is algebraic. Its real and
;; imaginary parts can therefore be represented in one real number field
;; Q(alpha), using rational polynomials in a real algebraic generator alpha.
;; Conversely, every code below denotes an actual algebraic complex number.
;; Thus quantifying over these codes preserves every possible zero rather
;; than restricting the source's complex domain.
;;
;; Rational polynomials in alpha use descending coefficient order. A
;; rational polynomial and rational isolating interval define alpha, while
;; Sturm-Tarski queries decide signs at alpha exactly.

(defun putnam-1972-b6-rp-p (p)
  (if (consp p)
      (and (rationalp (car p))
           (putnam-1972-b6-rp-p (cdr p)))
    (equal p nil)))

(defun putnam-1972-b6-rp-normalize (p)
  (if (consp p)
      (if (equal (car p) 0)
          (putnam-1972-b6-rp-normalize (cdr p))
        p)
    nil))

(defun putnam-1972-b6-rp-negate (p)
  (if (consp p)
      (cons (- (car p))
            (putnam-1972-b6-rp-negate (cdr p)))
    nil))

(defun putnam-1972-b6-rp-add-raw (p q)
  (declare (xargs :measure (+ (acl2-count p) (acl2-count q))))
  (cond
   ((endp p) q)
   ((endp q) p)
   ((< (len p) (len q))
    (cons (car q)
          (putnam-1972-b6-rp-add-raw p (cdr q))))
   ((< (len q) (len p))
    (cons (car p)
          (putnam-1972-b6-rp-add-raw (cdr p) q)))
   (t
    (cons (+ (car p) (car q))
          (putnam-1972-b6-rp-add-raw (cdr p) (cdr q))))))

(defun putnam-1972-b6-rp-add (p q)
  (putnam-1972-b6-rp-normalize
   (putnam-1972-b6-rp-add-raw p q)))

(defun putnam-1972-b6-rp-subtract (p q)
  (putnam-1972-b6-rp-add
   p (putnam-1972-b6-rp-negate q)))

(defun putnam-1972-b6-rp-scale (coefficient p)
  (if (consp p)
      (cons (* coefficient (car p))
            (putnam-1972-b6-rp-scale coefficient (cdr p)))
    nil))

(defun putnam-1972-b6-zeroes (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (putnam-1972-b6-zeroes (- n 1)))))

(defun putnam-1972-b6-rp-scale-shift (coefficient p shift)
  (append
   (putnam-1972-b6-rp-scale coefficient p)
   (putnam-1972-b6-zeroes shift)))

(defun putnam-1972-b6-rp-multiply-raw (p q)
  (if (consp p)
      (putnam-1972-b6-rp-add
       (putnam-1972-b6-rp-scale-shift
        (car p) q (len (cdr p)))
       (putnam-1972-b6-rp-multiply-raw (cdr p) q))
    nil))

(defun putnam-1972-b6-rp-multiply (p q)
  (putnam-1972-b6-rp-normalize
   (putnam-1972-b6-rp-multiply-raw p q)))

(defun putnam-1972-b6-rp-square (p)
  (putnam-1972-b6-rp-multiply p p))

(defun putnam-1972-b6-rp-eval-aux (p x accumulator)
  (if (consp p)
      (putnam-1972-b6-rp-eval-aux
       (cdr p) x (+ (* accumulator x) (car p)))
    accumulator))

(defun putnam-1972-b6-rp-eval (p x)
  (putnam-1972-b6-rp-eval-aux p x 0))

(defun putnam-1972-b6-rp-derivative-aux (p degree)
  (if (consp p)
      (if (zp degree)
          nil
        (cons (* degree (car p))
              (putnam-1972-b6-rp-derivative-aux
               (cdr p) (- degree 1))))
    nil))

(defun putnam-1972-b6-rp-derivative (p)
  (let ((normalized (putnam-1972-b6-rp-normalize p)))
    (putnam-1972-b6-rp-normalize
     (putnam-1972-b6-rp-derivative-aux
      normalized
      (nfix (- (len normalized) 1))))))

(defun putnam-1972-b6-rp-remainder-fuel (p q fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((p (putnam-1972-b6-rp-normalize p))
        (q (putnam-1972-b6-rp-normalize q)))
    (if (or (zp fuel)
            (endp q)
            (< (len p) (len q)))
        p
      (putnam-1972-b6-rp-remainder-fuel
       (putnam-1972-b6-rp-subtract
        p
        (putnam-1972-b6-rp-scale-shift
         (/ (car p) (car q))
         q
         (- (len p) (len q))))
       q
       (- fuel 1)))))

(defun putnam-1972-b6-rp-remainder (p q)
  (putnam-1972-b6-rp-remainder-fuel
   p q (+ 1 (len (putnam-1972-b6-rp-normalize p)))))

(defun putnam-1972-b6-rp-sturm-tail (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current (putnam-1972-b6-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-1972-b6-rp-sturm-tail
        current
        (putnam-1972-b6-rp-negate
         (putnam-1972-b6-rp-remainder previous current))
        (- fuel 1))))))

(defun putnam-1972-b6-rp-sturm-sequence (p q)
  (let ((p (putnam-1972-b6-rp-normalize p))
        (q (putnam-1972-b6-rp-normalize q)))
    (if (endp p)
        nil
      (cons
       p
       (if (endp q)
           nil
         (cons
          q
          (putnam-1972-b6-rp-sturm-tail
           p q (+ 1 (len p) (len q)))))))))

(defun putnam-1972-b6-rational-sign (x)
  (cond ((< x 0) -1)
        ((< 0 x) 1)
        (t 0)))

(defun putnam-1972-b6-rp-variations-aux
    (polynomials x previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-1972-b6-rational-sign
              (putnam-1972-b6-rp-eval
               (car polynomials) x))))
        (if (equal sign 0)
            (putnam-1972-b6-rp-variations-aux
             (cdr polynomials) x previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-1972-b6-rp-variations-aux
              (cdr polynomials) x sign))))
    0))

(defun putnam-1972-b6-rp-variations (polynomials x)
  (putnam-1972-b6-rp-variations-aux polynomials x 0))

(defun putnam-1972-b6-rp-cauchy-index (p q lower upper)
  (let ((sequence
         (putnam-1972-b6-rp-sturm-sequence p q)))
    (- (putnam-1972-b6-rp-variations sequence lower)
       (putnam-1972-b6-rp-variations sequence upper))))

(defun putnam-1972-b6-rp-root-count (p lower upper)
  (putnam-1972-b6-rp-cauchy-index
   p (putnam-1972-b6-rp-derivative p) lower upper))

(defun putnam-1972-b6-primitive-p (primitive lower upper)
  (and
   (putnam-1972-b6-rp-p primitive)
   (consp (putnam-1972-b6-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not (equal
         (putnam-1972-b6-rp-eval primitive lower) 0))
   (not (equal
         (putnam-1972-b6-rp-eval primitive upper) 0))
   (equal
    (putnam-1972-b6-rp-root-count primitive lower upper)
    1)
   (not
    (equal
     (putnam-1972-b6-rp-cauchy-index
      primitive
      (putnam-1972-b6-rp-multiply
       (putnam-1972-b6-rp-derivative primitive)
       (putnam-1972-b6-rp-derivative primitive))
      lower
      upper)
     0))))

;; For the single isolated simple root alpha, this Sturm-Tarski query is the
;; sign of VALUE(alpha).
(defun putnam-1972-b6-algebraic-sign
    (primitive lower upper value)
  (putnam-1972-b6-rp-cauchy-index
   primitive
   (putnam-1972-b6-rp-multiply
    (putnam-1972-b6-rp-derivative primitive)
    value)
   lower
   upper))

(defun putnam-1972-b6-zero-at-alpha-p
    (primitive lower upper value)
  (equal
   (putnam-1972-b6-algebraic-sign
    primitive lower upper value)
   0))

;; A pair stores the real and imaginary parts as polynomials in alpha.
(defun putnam-1972-b6-complex (real-part imaginary-part)
  (cons real-part imaginary-part))

(defun putnam-1972-b6-complex-real (z)
  (car z))

(defun putnam-1972-b6-complex-imaginary (z)
  (cdr z))

(defun putnam-1972-b6-complex-rational (q)
  (putnam-1972-b6-complex (list q) nil))

(defun putnam-1972-b6-complex-add (left right)
  (putnam-1972-b6-complex
   (putnam-1972-b6-rp-add
    (putnam-1972-b6-complex-real left)
    (putnam-1972-b6-complex-real right))
   (putnam-1972-b6-rp-add
    (putnam-1972-b6-complex-imaginary left)
    (putnam-1972-b6-complex-imaginary right))))

(defun putnam-1972-b6-complex-multiply (left right)
  (putnam-1972-b6-complex
   (putnam-1972-b6-rp-subtract
    (putnam-1972-b6-rp-multiply
     (putnam-1972-b6-complex-real left)
     (putnam-1972-b6-complex-real right))
    (putnam-1972-b6-rp-multiply
     (putnam-1972-b6-complex-imaginary left)
     (putnam-1972-b6-complex-imaginary right)))
   (putnam-1972-b6-rp-add
    (putnam-1972-b6-rp-multiply
     (putnam-1972-b6-complex-real left)
     (putnam-1972-b6-complex-imaginary right))
    (putnam-1972-b6-rp-multiply
     (putnam-1972-b6-complex-imaginary left)
     (putnam-1972-b6-complex-real right)))))

(defun putnam-1972-b6-complex-power (z exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (putnam-1972-b6-complex-rational 1)
    (putnam-1972-b6-complex-multiply
     z
     (putnam-1972-b6-complex-power z (- exponent 1)))))

(defun putnam-1972-b6-polynomial-value (z exponents)
  (if (consp exponents)
      (putnam-1972-b6-complex-add
       (putnam-1972-b6-complex-power z (car exponents))
       (putnam-1972-b6-polynomial-value z (cdr exponents)))
    (putnam-1972-b6-complex-rational 1)))

(defun putnam-1972-b6-increasing-positive-exponents-p (exponents)
  (if (consp exponents)
      (and
       (posp (car exponents))
       (or
        (endp (cdr exponents))
        (and
         (< (car exponents) (cadr exponents))
         (putnam-1972-b6-increasing-positive-exponents-p
          (cdr exponents)))))
    (equal exponents nil)))

(defun putnam-1972-b6-complex-zero-at-alpha-p
    (primitive lower upper z)
  (and
   (putnam-1972-b6-zero-at-alpha-p
    primitive lower upper
    (putnam-1972-b6-complex-real z))
   (putnam-1972-b6-zero-at-alpha-p
    primitive lower upper
    (putnam-1972-b6-complex-imaginary z))))

(defun putnam-1972-b6-modulus-squared (z)
  (putnam-1972-b6-rp-add
   (putnam-1972-b6-rp-square
    (putnam-1972-b6-complex-real z))
   (putnam-1972-b6-rp-square
    (putnam-1972-b6-complex-imaginary z))))

;; With q = |z|^2 >= 0,
;;
;;   |z| < (sqrt(5)-1)/2
;;
;; is equivalent to 3-2q > 0 and (3-2q)^2 > 5. This removes both square
;; roots without changing the strict disk.
(defun putnam-1972-b6-inside-disk-p
    (primitive lower upper z)
  (let* ((q (putnam-1972-b6-modulus-squared z))
         (three-minus-two-q
          (putnam-1972-b6-rp-subtract
           (list 3)
           (putnam-1972-b6-rp-scale 2 q)))
         (square-minus-five
          (putnam-1972-b6-rp-subtract
           (putnam-1972-b6-rp-square three-minus-two-q)
           (list 5))))
    (and
     (equal
      (putnam-1972-b6-algebraic-sign
       primitive lower upper three-minus-two-q)
      1)
     (equal
      (putnam-1972-b6-algebraic-sign
       primitive lower upper square-minus-five)
      1))))

(defun putnambench-putnam-1972-b6-statement
    (primitive lower upper exponents z-real z-imaginary)
  (let ((z (putnam-1972-b6-complex z-real z-imaginary)))
    (implies
     (and
      (putnam-1972-b6-primitive-p primitive lower upper)
      (true-listp exponents)
      (consp exponents)
      (putnam-1972-b6-increasing-positive-exponents-p exponents)
      (putnam-1972-b6-rp-p z-real)
      (putnam-1972-b6-rp-p z-imaginary)
      (putnam-1972-b6-inside-disk-p
       primitive lower upper z))
     (not
      (putnam-1972-b6-complex-zero-at-alpha-p
       primitive lower upper
       (putnam-1972-b6-polynomial-value z exponents))))))

(value-triple :itpeval-statement-checked)
:q
