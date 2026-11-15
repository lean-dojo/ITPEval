;; Statement-only formalization of PutnamBench corpus artifact putnam_2003_b1:
;; nonexistence of four real univariate polynomials whose two separated
;; products sum identically to 1 + x*y + x^2*y^2. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Since the supplied solution is False, the source biconditional is the
;; universal assertion that no four real polynomials satisfy the identity.
;; A failure of that assertion is a finite system of polynomial equations
;; over the reals, so it has a real solution iff it has a real-algebraic
;; solution. Every finite tuple of real algebraic coefficients lies in
;; Q(alpha) for one real algebraic alpha. Rational polynomials in alpha, with
;; alpha specified by a rational isolating interval, therefore preserve the
;; arbitrary real domain rather than restricting coefficients to rationals.
;;
;; Source polynomials are arbitrary finite coefficient lists in ascending
;; degree order. Coefficientwise comparison is equivalent to identity for all
;; real x and y, and the list lengths remain unbounded.

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-2003-b1-rp-p (p)
  (if (consp p)
      (and (rationalp (car p))
           (putnam-2003-b1-rp-p (cdr p)))
    (equal p nil)))

(defun putnam-2003-b1-rp-normalize (p)
  (if (consp p)
      (if (equal (car p) 0)
          (putnam-2003-b1-rp-normalize (cdr p))
        p)
    nil))

(defun putnam-2003-b1-rp-neg (p)
  (if (consp p)
      (cons (- (car p))
            (putnam-2003-b1-rp-neg (cdr p)))
    nil))

(defun putnam-2003-b1-rp-add-raw (p q)
  (declare (xargs :measure (+ (acl2-count p) (acl2-count q))))
  (cond
   ((endp p) q)
   ((endp q) p)
   ((< (len p) (len q))
    (cons (car q)
          (putnam-2003-b1-rp-add-raw p (cdr q))))
   ((< (len q) (len p))
    (cons (car p)
          (putnam-2003-b1-rp-add-raw (cdr p) q)))
   (t
    (cons (+ (car p) (car q))
          (putnam-2003-b1-rp-add-raw (cdr p) (cdr q))))))

(defun putnam-2003-b1-rp-add (p q)
  (putnam-2003-b1-rp-normalize
   (putnam-2003-b1-rp-add-raw p q)))

(defun putnam-2003-b1-rp-sub (p q)
  (putnam-2003-b1-rp-add
   p (putnam-2003-b1-rp-neg q)))

(defun putnam-2003-b1-rp-scale (coefficient p)
  (if (consp p)
      (cons (* coefficient (car p))
            (putnam-2003-b1-rp-scale coefficient (cdr p)))
    nil))

(defun putnam-2003-b1-zeroes (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (putnam-2003-b1-zeroes (- n 1)))))

(defun putnam-2003-b1-rp-scale-shift (coefficient p shift)
  (append
   (putnam-2003-b1-rp-scale coefficient p)
   (putnam-2003-b1-zeroes shift)))

(defun putnam-2003-b1-rp-mul-raw (p q)
  (if (consp p)
      (putnam-2003-b1-rp-add
       (putnam-2003-b1-rp-scale-shift
        (car p) q (len (cdr p)))
       (putnam-2003-b1-rp-mul-raw (cdr p) q))
    nil))

(defun putnam-2003-b1-rp-mul (p q)
  (putnam-2003-b1-rp-normalize
   (putnam-2003-b1-rp-mul-raw p q)))

(defun putnam-2003-b1-rp-eval-aux (p x accumulator)
  (if (consp p)
      (putnam-2003-b1-rp-eval-aux
       (cdr p) x (+ (* accumulator x) (car p)))
    accumulator))

(defun putnam-2003-b1-rp-eval (p x)
  (putnam-2003-b1-rp-eval-aux p x 0))

(defun putnam-2003-b1-rp-derivative-aux (p degree)
  (if (consp p)
      (if (zp degree)
          nil
        (cons (* degree (car p))
              (putnam-2003-b1-rp-derivative-aux
               (cdr p) (- degree 1))))
    nil))

(defun putnam-2003-b1-rp-derivative (p)
  (let ((p (putnam-2003-b1-rp-normalize p)))
    (putnam-2003-b1-rp-normalize
     (putnam-2003-b1-rp-derivative-aux
      p (nfix (- (len p) 1))))))

(defun putnam-2003-b1-rp-rem-fuel (p q fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((p (putnam-2003-b1-rp-normalize p))
        (q (putnam-2003-b1-rp-normalize q)))
    (if (or (zp fuel)
            (endp q)
            (< (len p) (len q)))
        p
      (putnam-2003-b1-rp-rem-fuel
       (putnam-2003-b1-rp-sub
        p
        (putnam-2003-b1-rp-scale-shift
         (/ (car p) (car q))
         q
         (- (len p) (len q))))
       q
       (- fuel 1)))))

(defun putnam-2003-b1-rp-rem (p q)
  (putnam-2003-b1-rp-rem-fuel
   p q (+ 1 (len (putnam-2003-b1-rp-normalize p)))))

(defun putnam-2003-b1-rp-sturm-tail (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current (putnam-2003-b1-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-2003-b1-rp-sturm-tail
        current
        (putnam-2003-b1-rp-neg
         (putnam-2003-b1-rp-rem previous current))
        (- fuel 1))))))

(defun putnam-2003-b1-rp-sturm-sequence (p q)
  (let ((p (putnam-2003-b1-rp-normalize p))
        (q (putnam-2003-b1-rp-normalize q)))
    (if (endp p)
        nil
      (cons
       p
       (if (endp q)
           nil
         (cons
          q
          (putnam-2003-b1-rp-sturm-tail
           p q (+ 1 (len p) (len q)))))))))

(defun putnam-2003-b1-rational-sign (x)
  (cond ((< x 0) -1)
        ((< 0 x) 1)
        (t 0)))

(defun putnam-2003-b1-rp-variations-aux
    (polynomials x previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-2003-b1-rational-sign
              (putnam-2003-b1-rp-eval
               (car polynomials) x))))
        (if (equal sign 0)
            (putnam-2003-b1-rp-variations-aux
             (cdr polynomials) x previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-2003-b1-rp-variations-aux
              (cdr polynomials) x sign))))
    0))

(defun putnam-2003-b1-rp-variations (polynomials x)
  (putnam-2003-b1-rp-variations-aux polynomials x 0))

(defun putnam-2003-b1-rp-cauchy-index (p q lower upper)
  (let ((sequence
         (putnam-2003-b1-rp-sturm-sequence p q)))
    (- (putnam-2003-b1-rp-variations sequence lower)
       (putnam-2003-b1-rp-variations sequence upper))))

(defun putnam-2003-b1-rp-root-count (p lower upper)
  (putnam-2003-b1-rp-cauchy-index
   p (putnam-2003-b1-rp-derivative p) lower upper))

(defun putnam-2003-b1-primitive-p (primitive lower upper)
  (and
   (putnam-2003-b1-rp-p primitive)
   (consp (putnam-2003-b1-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not (equal
         (putnam-2003-b1-rp-eval primitive lower) 0))
   (not (equal
         (putnam-2003-b1-rp-eval primitive upper) 0))
   (equal
    (putnam-2003-b1-rp-root-count primitive lower upper)
    1)
   (not
    (equal
     (putnam-2003-b1-rp-cauchy-index
      primitive
      (putnam-2003-b1-rp-mul
       (putnam-2003-b1-rp-derivative primitive)
       (putnam-2003-b1-rp-derivative primitive))
      lower
      upper)
     0))))

;; For the isolated simple root alpha, this query is sign(value(alpha)).
(defun putnam-2003-b1-algebraic-sign
    (primitive lower upper value)
  (putnam-2003-b1-rp-cauchy-index
   primitive
   (putnam-2003-b1-rp-mul
    (putnam-2003-b1-rp-derivative primitive)
    value)
   lower
   upper))

(defun putnam-2003-b1-algebraic-equal-p
    (primitive lower upper left right)
  (equal
   (putnam-2003-b1-algebraic-sign
    primitive lower upper
    (putnam-2003-b1-rp-sub left right))
   0))

(defun putnam-2003-b1-algebraic-polynomial-p (coefficients)
  (if (consp coefficients)
      (and
       (putnam-2003-b1-rp-p (car coefficients))
       (putnam-2003-b1-algebraic-polynomial-p
        (cdr coefficients)))
    (equal coefficients nil)))

(defun putnam-2003-b1-target-coefficient (x-degree y-degree)
  (if (and
       (equal x-degree y-degree)
       (< x-degree 3))
      (list 1)
    nil))

(defun putnam-2003-b1-coefficient-equal-p
    (primitive lower upper a b c d x-degree y-degree)
  (putnam-2003-b1-algebraic-equal-p
   primitive lower upper
   (putnam-2003-b1-rp-add
    (putnam-2003-b1-rp-mul
     (nth x-degree a)
     (nth y-degree c))
    (putnam-2003-b1-rp-mul
     (nth x-degree b)
     (nth y-degree d)))
   (putnam-2003-b1-target-coefficient
    x-degree y-degree)))

(defun putnam-2003-b1-row-identity-p
    (primitive lower upper a b c d x-degree y-degree)
  (declare (xargs :measure (nfix y-degree)))
  (and
   (putnam-2003-b1-coefficient-equal-p
    primitive lower upper a b c d x-degree y-degree)
   (if (zp y-degree)
       t
     (putnam-2003-b1-row-identity-p
      primitive lower upper a b c d
      x-degree (- y-degree 1)))))

(defun putnam-2003-b1-coefficient-identity-aux-p
    (primitive lower upper a b c d x-degree y-degree)
  (declare (xargs :measure (nfix x-degree)))
  (and
   (putnam-2003-b1-row-identity-p
    primitive lower upper a b c d x-degree y-degree)
   (if (zp x-degree)
       t
     (putnam-2003-b1-coefficient-identity-aux-p
      primitive lower upper a b c d
      (- x-degree 1) y-degree))))

(defun putnam-2003-b1-max2 (left right)
  (if (< left right) right left))

(defun putnam-2003-b1-coefficient-identity-p (primitive lower upper a b c d)
  (let* ((x-count
          (putnam-2003-b1-max2
           3
           (putnam-2003-b1-max2 (len a) (len b))))
         (y-count
          (putnam-2003-b1-max2
           3
           (putnam-2003-b1-max2 (len c) (len d)))))
    (putnam-2003-b1-coefficient-identity-aux-p
     primitive lower upper a b c d
     (- x-count 1) (- y-count 1))))

(defun putnambench-putnam-2003-b1-statement
    (primitive lower upper a b c d)
  (implies
   (and
    (putnam-2003-b1-primitive-p primitive lower upper)
    (putnam-2003-b1-algebraic-polynomial-p a)
    (putnam-2003-b1-algebraic-polynomial-p b)
    (putnam-2003-b1-algebraic-polynomial-p c)
    (putnam-2003-b1-algebraic-polynomial-p d))
   (not
    (putnam-2003-b1-coefficient-identity-p
     primitive lower upper a b c d))))

(value-triple :itpeval-statement-checked)
:q
