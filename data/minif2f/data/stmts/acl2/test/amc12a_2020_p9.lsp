;; Statement-only formalization of miniF2F corpus artifact amc12a_2020_p9:
;; the real solution set in [0, 2*pi] of tan(2*x) = cos(x/2) has cardinality
;; five, encoded exactly by Sturm and Sturm-Tarski root counts after a
;; bijective trigonometric-to-semialgebraic reduction. This file contains no
;; proof.

(in-package "ACL2")

;; Put t = x/2, c = cos(t), and u = c^2.  Since t ranges over [0,pi],
;; c ranges bijectively over [-1,1].  The solution c = 0 contributes one x.
;; For c != 0, the equation is equivalent to
;;
;;   4*sqrt(1-u)*(2*u-1) = 8*u^2-8*u+1.
;;
;; Thus the other solutions correspond exactly to roots u in (0,1) of P
;; for which Q is positive, where
;;
;;   P(u) = 64*u^4-64*u^3-48*u^2+64*u-15,
;;   Q(u) = (2*u-1)*(8*u^2-8*u+1).
;;
;; The sign condition removes precisely the extraneous roots introduced by
;; squaring.  Each qualifying u gives the two values c = +/-sqrt(u), hence
;; two values of x.

(defun amc12a-2020-p9-p ()
  (list -15 64 -48 -64 64))

(defun amc12a-2020-p9-q ()
  (list -1 10 -24 16))

;; Polynomials are coefficient lists in ascending degree order.
(defun amc12a-2020-p9-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (amc12a-2020-p9-poly-normalize
              (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun amc12a-2020-p9-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (amc12a-2020-p9-poly-add
               (cdr left) (cdr right)))
      left))
   (t right)))

(defun amc12a-2020-p9-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (amc12a-2020-p9-poly-scale
             scalar (cdr polynomial)))
    nil))

(defun amc12a-2020-p9-poly-negate (polynomial)
  (amc12a-2020-p9-poly-scale -1 polynomial))

(defun amc12a-2020-p9-poly-subtract (left right)
  (amc12a-2020-p9-poly-normalize
   (amc12a-2020-p9-poly-add
    left
    (amc12a-2020-p9-poly-negate right))))

(defun amc12a-2020-p9-poly-multiply (left right)
  (if (consp left)
      (amc12a-2020-p9-poly-normalize
       (amc12a-2020-p9-poly-add
        (amc12a-2020-p9-poly-scale (car left) right)
        (cons 0
              (amc12a-2020-p9-poly-multiply
               (cdr left) right))))
    nil))

(defun amc12a-2020-p9-poly-derivative-aux
    (coefficients degree)
  (if (consp coefficients)
      (cons (* degree (car coefficients))
            (amc12a-2020-p9-poly-derivative-aux
             (cdr coefficients) (+ degree 1)))
    nil))

(defun amc12a-2020-p9-poly-derivative (polynomial)
  (if (consp polynomial)
      (amc12a-2020-p9-poly-normalize
       (amc12a-2020-p9-poly-derivative-aux
        (cdr polynomial) 1))
    nil))

(defun amc12a-2020-p9-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (amc12a-2020-p9-zero-list (- count 1)))))

(defun amc12a-2020-p9-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append (amc12a-2020-p9-zero-list degree)
            (list coefficient))))

(defun amc12a-2020-p9-poly-degree (polynomial)
  (let ((normalized
         (amc12a-2020-p9-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun amc12a-2020-p9-poly-leading-coefficient (polynomial)
  (let ((normalized
         (amc12a-2020-p9-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (amc12a-2020-p9-poly-degree normalized)
             normalized)
      0)))

;; The step bound is larger than the number of degree-lowering divisions
;; needed for these exact rational polynomials.
(defun amc12a-2020-p9-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons (amc12a-2020-p9-poly-normalize quotient)
            (amc12a-2020-p9-poly-normalize remainder))
    (let* ((normalized-remainder
            (amc12a-2020-p9-poly-normalize remainder))
           (normalized-divisor
            (amc12a-2020-p9-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (amc12a-2020-p9-poly-degree
                  normalized-remainder)
                 (amc12a-2020-p9-poly-degree
                  normalized-divisor)))
          (cons (amc12a-2020-p9-poly-normalize quotient)
                normalized-remainder)
        (let* ((degree-difference
                (- (amc12a-2020-p9-poly-degree
                    normalized-remainder)
                   (amc12a-2020-p9-poly-degree
                    normalized-divisor)))
               (coefficient
                (/ (amc12a-2020-p9-poly-leading-coefficient
                    normalized-remainder)
                   (amc12a-2020-p9-poly-leading-coefficient
                    normalized-divisor)))
               (term
                (amc12a-2020-p9-poly-monomial
                 coefficient degree-difference)))
          (amc12a-2020-p9-poly-divmod-steps
           (amc12a-2020-p9-poly-subtract
            normalized-remainder
            (amc12a-2020-p9-poly-multiply
             term normalized-divisor))
           normalized-divisor
           (amc12a-2020-p9-poly-add quotient term)
           (- steps 1)))))))

(defun amc12a-2020-p9-poly-divmod (dividend divisor)
  (amc12a-2020-p9-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1
      (len (amc12a-2020-p9-poly-normalize dividend)))))

(defun amc12a-2020-p9-poly-remainder (dividend divisor)
  (cdr (amc12a-2020-p9-poly-divmod dividend divisor)))

(defun amc12a-2020-p9-sturm-tail
    (previous current steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-current
         (amc12a-2020-p9-poly-normalize current)))
    (if (or (zp steps)
            (not (consp normalized-current)))
        nil
      (cons
       normalized-current
       (amc12a-2020-p9-sturm-tail
        normalized-current
        (amc12a-2020-p9-poly-negate
         (amc12a-2020-p9-poly-remainder
          previous normalized-current))
        (- steps 1))))))

(defun amc12a-2020-p9-sturm-chain (first second)
  (let ((normalized-first
         (amc12a-2020-p9-poly-normalize first)))
    (if (consp normalized-first)
        (cons
         normalized-first
         (amc12a-2020-p9-sturm-tail
          normalized-first
          second
          (+ 1 (len normalized-first))))
      nil)))

(defun amc12a-2020-p9-poly-evaluate (polynomial value)
  (if (consp polynomial)
      (+ (car polynomial)
         (* value
            (amc12a-2020-p9-poly-evaluate
             (cdr polynomial) value)))
    0))

(defun amc12a-2020-p9-chain-values-at (chain value)
  (if (consp chain)
      (cons
       (amc12a-2020-p9-poly-evaluate
        (car chain) value)
       (amc12a-2020-p9-chain-values-at
        (cdr chain) value))
    nil))

(defun amc12a-2020-p9-sign (value)
  (cond ((< value 0) -1)
        ((< 0 value) 1)
        (t 0)))

(defun amc12a-2020-p9-sign-variations-aux (values previous-sign)
  (if (consp values)
      (let ((current-sign
             (amc12a-2020-p9-sign (car values))))
        (cond
         ((equal current-sign 0)
          (amc12a-2020-p9-sign-variations-aux
           (cdr values) previous-sign))
         ((equal previous-sign 0)
          (amc12a-2020-p9-sign-variations-aux
           (cdr values) current-sign))
         (t
          (+ (if (equal current-sign previous-sign) 0 1)
             (amc12a-2020-p9-sign-variations-aux
              (cdr values) current-sign)))))
    0))

(defun amc12a-2020-p9-sign-variations (values)
  (amc12a-2020-p9-sign-variations-aux values 0))

;; P(0) and P(1) are nonzero, so this variation difference counts all real
;; roots of P in the open unit interval, without replacing them by rationals.
(defun amc12a-2020-p9-unit-root-count ()
  (let* ((p (amc12a-2020-p9-p))
         (chain
          (amc12a-2020-p9-sturm-chain
           p
           (amc12a-2020-p9-poly-derivative p))))
    (- (amc12a-2020-p9-sign-variations
        (amc12a-2020-p9-chain-values-at chain 0))
       (amc12a-2020-p9-sign-variations
        (amc12a-2020-p9-chain-values-at chain 1)))))

(defun amc12a-2020-p9-unit-sign-query ()
  (let* ((p (amc12a-2020-p9-p))
         (p-prime (amc12a-2020-p9-poly-derivative p))
         (p-prime-times-q
          (amc12a-2020-p9-poly-multiply
           p-prime
           (amc12a-2020-p9-q)))
         (reduced-query-polynomial
          (amc12a-2020-p9-poly-remainder
           p-prime-times-q p))
         (chain
          (amc12a-2020-p9-sturm-chain
           p reduced-query-polynomial)))
    (- (amc12a-2020-p9-sign-variations
        (amc12a-2020-p9-chain-values-at chain 0))
       (amc12a-2020-p9-sign-variations
        (amc12a-2020-p9-chain-values-at chain 1)))))

;; Because Q is nonzero at every root of P, (root-count + sign-query)/2 is
;; exactly the number of roots at which Q is positive.
(defun amc12a-2020-p9-positive-q-root-count ()
  (/ (+ (amc12a-2020-p9-unit-root-count)
        (amc12a-2020-p9-unit-sign-query))
     2))

(defun amc12a-2020-p9-solution-count ()
  (+ 1
     (* 2
        (amc12a-2020-p9-positive-q-root-count))))

(defun amc12a-2020-p9-statement ()
  (equal (amc12a-2020-p9-solution-count) 5))

(value-triple :itpeval-statement-checked)
:q
