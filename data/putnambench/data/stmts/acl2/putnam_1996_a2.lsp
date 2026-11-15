;; Statement-only formalization of PutnamBench corpus artifact putnam_1996_a2:
;; the midpoint locus for points chosen on two circles of radii 1 and 3 is
;; the closed annulus of radii 1 and 2 about the midpoint of their centers.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Put d=O2-O1, w=2*M-O1-O2, u=X-O1, and v=Y-O2. Then the source statement is
;;
;;   |d|^2=100 implies
;;   ((exists u,v, |u|^2=1 and |v|^2=9 and w=u+v)
;;      iff 4 <= |w|^2 <= 16).
;;
;; The defun-sk predicate below retains the source's existential circle
;; witnesses. Its new primitive element beta may generate a finite algebraic
;; extension of Q(alpha), so witnesses such as square roots need not already
;; be polynomials in the input primitive alpha. A polynomial alpha-code(beta)
;; is required to be the unique input root in its isolating interval, and the
;; original coordinates are transported by polynomial composition. Thus the
;; circle witnesses are internal rather than additional statement parameters.
;;
;; Every finite tuple of real algebraic numbers lies in Q(alpha). A rational
;; polynomial and isolating interval represent alpha, and rational polynomials
;; in alpha represent all coordinates under discussion. Sturm-Tarski queries
;; decide their signs exactly. Each clause is first-order over real closed
;; fields with rational coefficients, so a real counterexample exists exactly
;; when a real-algebraic one exists. Thus the universal closure below covers
;; arbitrary real-plane points without narrowing the domain to ACL2's rationals.

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-1996-a2-rp-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (putnam-1996-a2-rp-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-1996-a2-rp-normalize (polynomial)
  (if (consp polynomial)
      (if (equal (car polynomial) 0)
          (putnam-1996-a2-rp-normalize (cdr polynomial))
        polynomial)
    nil))

(defun putnam-1996-a2-rp-neg (polynomial)
  (if (consp polynomial)
      (cons (- (car polynomial))
            (putnam-1996-a2-rp-neg (cdr polynomial)))
    nil))

(defun putnam-1996-a2-rp-add-raw (left right)
  (declare
   (xargs :measure (+ (acl2-count left) (acl2-count right))))
  (cond
   ((endp left) right)
   ((endp right) left)
   ((< (len left) (len right))
    (cons (car right)
          (putnam-1996-a2-rp-add-raw left (cdr right))))
   ((< (len right) (len left))
    (cons (car left)
          (putnam-1996-a2-rp-add-raw (cdr left) right)))
   (t
    (cons (+ (car left) (car right))
          (putnam-1996-a2-rp-add-raw
           (cdr left) (cdr right))))))

(defun putnam-1996-a2-rp-add (left right)
  (putnam-1996-a2-rp-normalize
   (putnam-1996-a2-rp-add-raw left right)))

(defun putnam-1996-a2-rp-sub (left right)
  (putnam-1996-a2-rp-add
   left (putnam-1996-a2-rp-neg right)))

(defun putnam-1996-a2-rp-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-1996-a2-rp-scale scalar (cdr polynomial)))
    nil))

(defun putnam-1996-a2-zeroes (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0 (putnam-1996-a2-zeroes (- count 1)))))

(defun putnam-1996-a2-rp-scale-shift
    (scalar polynomial shift)
  (append
   (putnam-1996-a2-rp-scale scalar polynomial)
   (putnam-1996-a2-zeroes shift)))

(defun putnam-1996-a2-rp-mul-raw (left right)
  (if (consp left)
      (putnam-1996-a2-rp-add
       (putnam-1996-a2-rp-scale-shift
        (car left) right (len (cdr left)))
       (putnam-1996-a2-rp-mul-raw (cdr left) right))
    nil))

(defun putnam-1996-a2-rp-mul (left right)
  (putnam-1996-a2-rp-normalize
   (putnam-1996-a2-rp-mul-raw left right)))

(defun putnam-1996-a2-rp-square (polynomial)
  (putnam-1996-a2-rp-mul polynomial polynomial))

(defun putnam-1996-a2-rp-compose-aux
    (outer inner accumulator)
  (if (consp outer)
      (putnam-1996-a2-rp-compose-aux
       (cdr outer)
       inner
       (putnam-1996-a2-rp-add
        (putnam-1996-a2-rp-mul accumulator inner)
        (list (car outer))))
    accumulator))

(defun putnam-1996-a2-rp-compose (outer inner)
  (putnam-1996-a2-rp-compose-aux outer inner nil))

(defun putnam-1996-a2-rp-eval-aux
    (polynomial value accumulator)
  (if (consp polynomial)
      (putnam-1996-a2-rp-eval-aux
       (cdr polynomial)
       value
       (+ (* accumulator value) (car polynomial)))
    accumulator))

(defun putnam-1996-a2-rp-eval (polynomial value)
  (putnam-1996-a2-rp-eval-aux polynomial value 0))

(defun putnam-1996-a2-rp-derivative-aux
    (polynomial degree)
  (if (consp polynomial)
      (if (zp degree)
          nil
        (cons
         (* degree (car polynomial))
         (putnam-1996-a2-rp-derivative-aux
          (cdr polynomial) (- degree 1))))
    nil))

(defun putnam-1996-a2-rp-derivative (polynomial)
  (let ((polynomial
         (putnam-1996-a2-rp-normalize polynomial)))
    (putnam-1996-a2-rp-normalize
     (putnam-1996-a2-rp-derivative-aux
      polynomial
      (nfix (- (len polynomial) 1))))))

(defun putnam-1996-a2-rp-rem-fuel
    (dividend divisor fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((dividend
         (putnam-1996-a2-rp-normalize dividend))
        (divisor
         (putnam-1996-a2-rp-normalize divisor)))
    (if (or (zp fuel)
            (endp divisor)
            (< (len dividend) (len divisor)))
        dividend
      (putnam-1996-a2-rp-rem-fuel
       (putnam-1996-a2-rp-sub
        dividend
        (putnam-1996-a2-rp-scale-shift
         (/ (car dividend) (car divisor))
         divisor
         (- (len dividend) (len divisor))))
       divisor
       (- fuel 1)))))

(defun putnam-1996-a2-rp-rem (dividend divisor)
  (putnam-1996-a2-rp-rem-fuel
   dividend
   divisor
   (+ 1 (len (putnam-1996-a2-rp-normalize dividend)))))

(defun putnam-1996-a2-rp-sturm-tail
    (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current
         (putnam-1996-a2-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-1996-a2-rp-sturm-tail
        current
        (putnam-1996-a2-rp-neg
         (putnam-1996-a2-rp-rem previous current))
        (- fuel 1))))))

(defun putnam-1996-a2-rp-sturm-sequence
    (polynomial second)
  (let ((polynomial
         (putnam-1996-a2-rp-normalize polynomial))
        (second
         (putnam-1996-a2-rp-normalize second)))
    (if (endp polynomial)
        nil
      (cons
       polynomial
       (if (endp second)
           nil
         (cons
          second
          (putnam-1996-a2-rp-sturm-tail
           polynomial
           second
           (+ 1 (len polynomial) (len second)))))))))

(defun putnam-1996-a2-rational-sign (value)
  (cond ((< value 0) -1)
        ((< 0 value) 1)
        (t 0)))

(defun putnam-1996-a2-rp-variations-aux
    (polynomials value previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-1996-a2-rational-sign
              (putnam-1996-a2-rp-eval
               (car polynomials) value))))
        (if (equal sign 0)
            (putnam-1996-a2-rp-variations-aux
             (cdr polynomials) value previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-1996-a2-rp-variations-aux
              (cdr polynomials) value sign))))
    0))

(defun putnam-1996-a2-rp-variations
    (polynomials value)
  (putnam-1996-a2-rp-variations-aux
   polynomials value 0))

(defun putnam-1996-a2-rp-cauchy-index
    (polynomial second lower upper)
  (let ((sequence
         (putnam-1996-a2-rp-sturm-sequence
          polynomial second)))
    (- (putnam-1996-a2-rp-variations sequence lower)
       (putnam-1996-a2-rp-variations sequence upper))))

(defun putnam-1996-a2-rp-root-count
    (polynomial lower upper)
  (putnam-1996-a2-rp-cauchy-index
   polynomial
   (putnam-1996-a2-rp-derivative polynomial)
   lower
   upper))

(defun putnam-1996-a2-primitive-p
    (primitive lower upper)
  (and
   (putnam-1996-a2-rp-p primitive)
   (consp (putnam-1996-a2-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not
    (equal
     (putnam-1996-a2-rp-eval primitive lower)
     0))
   (not
    (equal
     (putnam-1996-a2-rp-eval primitive upper)
     0))
   (equal
    (putnam-1996-a2-rp-root-count
     primitive lower upper)
    1)
   (not
    (equal
     (putnam-1996-a2-rp-cauchy-index
      primitive
      (putnam-1996-a2-rp-mul
       (putnam-1996-a2-rp-derivative primitive)
       (putnam-1996-a2-rp-derivative primitive))
      lower
      upper)
     0))))

;; For the isolated simple root alpha, this Sturm-Tarski query is the sign of
;; polynomial(alpha).
(defun putnam-1996-a2-alg-sign
    (primitive lower upper polynomial)
  (putnam-1996-a2-rp-cauchy-index
   primitive
   (putnam-1996-a2-rp-mul
    (putnam-1996-a2-rp-derivative primitive)
    polynomial)
   lower
   upper))

(defun putnam-1996-a2-alg-zero-p
    (primitive lower upper polynomial)
  (equal
   (putnam-1996-a2-alg-sign
    primitive lower upper polynomial)
   0))

(defun putnam-1996-a2-alg-nonnegative-p
    (primitive lower upper polynomial)
  (<= 0
      (putnam-1996-a2-alg-sign
       primitive lower upper polynomial)))

(defun putnam-1996-a2-alg-positive-p
    (primitive lower upper polynomial)
  (< 0
     (putnam-1996-a2-alg-sign
      primitive lower upper polynomial)))

(defun putnam-1996-a2-norm-squared (x y)
  (putnam-1996-a2-rp-add
   (putnam-1996-a2-rp-square x)
   (putnam-1996-a2-rp-square y)))

(defun putnam-1996-a2-equal-at-alpha-p
    (primitive lower upper left right)
  (putnam-1996-a2-alg-zero-p
   primitive lower upper
   (putnam-1996-a2-rp-sub left right)))

(defun-sk putnam-1996-a2-midpoint-witness-exists-p
    (primitive lower upper wx wy)
  (exists
   (extension-primitive extension-lower extension-upper
                        alpha-code ux uy vx vy)
   (and
    (putnam-1996-a2-primitive-p primitive lower upper)
    (putnam-1996-a2-rp-p wx)
    (putnam-1996-a2-rp-p wy)
    (putnam-1996-a2-primitive-p
     extension-primitive extension-lower extension-upper)
    (putnam-1996-a2-rp-p alpha-code)
    (putnam-1996-a2-rp-p ux)
    (putnam-1996-a2-rp-p uy)
    (putnam-1996-a2-rp-p vx)
    (putnam-1996-a2-rp-p vy)
    (putnam-1996-a2-alg-zero-p
     extension-primitive extension-lower extension-upper
     (putnam-1996-a2-rp-compose primitive alpha-code))
    (putnam-1996-a2-alg-positive-p
     extension-primitive extension-lower extension-upper
     (putnam-1996-a2-rp-sub alpha-code (list lower)))
    (putnam-1996-a2-alg-positive-p
     extension-primitive extension-lower extension-upper
     (putnam-1996-a2-rp-sub (list upper) alpha-code))
    (putnam-1996-a2-equal-at-alpha-p
     extension-primitive extension-lower extension-upper
     (putnam-1996-a2-norm-squared ux uy)
     (list 1))
    (putnam-1996-a2-equal-at-alpha-p
     extension-primitive extension-lower extension-upper
     (putnam-1996-a2-norm-squared vx vy)
     (list 9))
    (putnam-1996-a2-equal-at-alpha-p
     extension-primitive extension-lower extension-upper
     (putnam-1996-a2-rp-compose wx alpha-code)
     (putnam-1996-a2-rp-add ux vx))
    (putnam-1996-a2-equal-at-alpha-p
     extension-primitive extension-lower extension-upper
     (putnam-1996-a2-rp-compose wy alpha-code)
     (putnam-1996-a2-rp-add uy vy)))))

(defun putnambench-putnam-1996-a2-statement
    (primitive lower upper dx dy wx wy)
  (implies
   (and
    (putnam-1996-a2-primitive-p primitive lower upper)
    (putnam-1996-a2-rp-p dx)
    (putnam-1996-a2-rp-p dy)
    (putnam-1996-a2-rp-p wx)
    (putnam-1996-a2-rp-p wy))
   (let* ((center-distance-squared
           (putnam-1996-a2-norm-squared dx dy))
          (q
           (putnam-1996-a2-norm-squared wx wy))
          (annulus-p
           (and
            (putnam-1996-a2-alg-nonnegative-p
             primitive lower upper
             (putnam-1996-a2-rp-sub q (list 4)))
            (putnam-1996-a2-alg-nonnegative-p
             primitive lower upper
             (putnam-1996-a2-rp-sub (list 16) q))))
          (center-distance-p
           (putnam-1996-a2-equal-at-alpha-p
            primitive lower upper
            center-distance-squared
            (list 100))))
     (implies
      center-distance-p
      (iff
       (putnam-1996-a2-midpoint-witness-exists-p
        primitive lower upper wx wy)
       annulus-p)))))

(value-triple :itpeval-statement-checked)
:q
