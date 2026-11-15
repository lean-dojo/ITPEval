;; Statement-only formalization of miniF2F corpus artifact aime_1997_p11:
;; the floor of 100 times the ratio of the cosine and sine sums at the
;; integer degree angles from 1 through 44 is 241. This file contains no
;; proof.
;;
;; Let z = exp(i*pi/180), a primitive 360th root of unity. Then
;;
;;   2*cos(n degrees)   = z^n + z^(-n),
;;   2*i*sin(n degrees) = z^n - z^(-n).
;;
;; Thus x = sum(cos(n degrees))/sum(sin(n degrees)) is equivalent to
;;
;;   x * sum(z^n - z^(-n))
;;     = z^90 * sum(z^n + z^(-n)).
;;
;; The sine denominator is nonzero because every summand for 1 <= n <= 44
;; is positive. Polynomial equality at z is encoded exactly by divisibility
;; by Phi_360. The ratio is cot(22.5 degrees) = 1 + sqrt(2), so every real x
;; satisfying the source hypothesis lies in Q(sqrt(2)). Conversely, each
;; represented pair denotes a real number. Restricting the ACL2 parameter to
;; this exact field therefore removes no satisfying source case. The floor
;; conclusion is represented by its exact adjacent-integer order bounds in
;; Q(sqrt(2)).

(in-package "ACL2")

;; Elements a + b*sqrt(2) are represented by dotted pairs (a . b).
(defun aime-1997-p11-qsqrt2-p (x)
  (and (consp x)
       (rationalp (car x))
       (rationalp (cdr x))))

(defun aime-1997-p11-qsqrt2-constant (value)
  (cons value 0))

(defun aime-1997-p11-qsqrt2-subtract (left right)
  (cons (- (car left) (car right))
        (- (cdr left) (cdr right))))

(defun aime-1997-p11-qsqrt2-scale (scalar x)
  (cons (* scalar (car x))
        (* scalar (cdr x))))

;; Exact positivity for a + b*sqrt(2), using rational comparisons only.
(defun aime-1997-p11-qsqrt2-positive-p (x)
  (let ((a (car x))
        (b (cdr x)))
    (cond
     ((equal b 0)
      (< 0 a))
     ((< 0 b)
      (or (<= 0 a)
          (< (* a a) (* 2 b b))))
     (t
      (and (< 0 a)
           (< (* 2 b b) (* a a)))))))

(defun aime-1997-p11-qsqrt2-less-p (left right)
  (aime-1997-p11-qsqrt2-positive-p
   (aime-1997-p11-qsqrt2-subtract right left)))

(defun aime-1997-p11-qsqrt2-less-equal-p (left right)
  (or (equal left right)
      (aime-1997-p11-qsqrt2-less-p left right)))

(defun aime-1997-p11-floor-witness-p (x floor-x)
  (and
   (integerp floor-x)
   (aime-1997-p11-qsqrt2-less-equal-p
    (aime-1997-p11-qsqrt2-constant floor-x)
    x)
   (aime-1997-p11-qsqrt2-less-p
    x
    (aime-1997-p11-qsqrt2-constant (+ floor-x 1)))))

;; Polynomials use ascending rational coefficient lists.
(defun aime-1997-p11-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (aime-1997-p11-poly-normalize
              (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun aime-1997-p11-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (aime-1997-p11-poly-add
               (cdr left) (cdr right)))
      left))
   (t right)))

(defun aime-1997-p11-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (aime-1997-p11-poly-scale
             scalar (cdr polynomial)))
    nil))

(defun aime-1997-p11-poly-negate (polynomial)
  (aime-1997-p11-poly-scale -1 polynomial))

(defun aime-1997-p11-poly-subtract (left right)
  (aime-1997-p11-poly-normalize
   (aime-1997-p11-poly-add
    left
    (aime-1997-p11-poly-negate right))))

(defun aime-1997-p11-poly-multiply (left right)
  (if (consp left)
      (aime-1997-p11-poly-normalize
       (aime-1997-p11-poly-add
        (aime-1997-p11-poly-scale (car left) right)
        (cons 0
              (aime-1997-p11-poly-multiply
               (cdr left) right))))
    nil))

(defun aime-1997-p11-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (aime-1997-p11-zero-list (- count 1)))))

(defun aime-1997-p11-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append
     (aime-1997-p11-zero-list degree)
     (list coefficient))))

(defun aime-1997-p11-poly-degree (polynomial)
  (let ((normalized
         (aime-1997-p11-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun aime-1997-p11-poly-leading-coefficient (polynomial)
  (let ((normalized
         (aime-1997-p11-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (aime-1997-p11-poly-degree normalized)
             normalized)
      0)))

(defun aime-1997-p11-poly-remainder-steps
    (remainder divisor steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (aime-1997-p11-poly-normalize remainder)
    (let* ((normalized-remainder
            (aime-1997-p11-poly-normalize remainder))
           (normalized-divisor
            (aime-1997-p11-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (aime-1997-p11-poly-degree
                  normalized-remainder)
                 (aime-1997-p11-poly-degree
                  normalized-divisor)))
          normalized-remainder
        (let* ((degree-difference
                (- (aime-1997-p11-poly-degree
                    normalized-remainder)
                   (aime-1997-p11-poly-degree
                    normalized-divisor)))
               (coefficient
                (/ (aime-1997-p11-poly-leading-coefficient
                    normalized-remainder)
                   (aime-1997-p11-poly-leading-coefficient
                    normalized-divisor))))
          (aime-1997-p11-poly-remainder-steps
           (aime-1997-p11-poly-subtract
            normalized-remainder
            (aime-1997-p11-poly-scale
             coefficient
             (aime-1997-p11-poly-multiply
              (aime-1997-p11-poly-monomial
               1 degree-difference)
              normalized-divisor)))
           normalized-divisor
           (- steps 1)))))))

(defun aime-1997-p11-poly-remainder (dividend divisor)
  (aime-1997-p11-poly-remainder-steps
   dividend
   divisor
   (+ 1 (len (aime-1997-p11-poly-normalize dividend)))))

;; Phi_360(X) = X^96 + X^84 - X^60 - X^48 - X^36 + X^12 + 1.
(defun aime-1997-p11-cyclotomic-polynomial ()
  (aime-1997-p11-poly-add
   (aime-1997-p11-poly-monomial 1 96)
   (aime-1997-p11-poly-add
    (aime-1997-p11-poly-monomial 1 84)
    (aime-1997-p11-poly-add
     (aime-1997-p11-poly-monomial -1 60)
     (aime-1997-p11-poly-add
      (aime-1997-p11-poly-monomial -1 48)
      (aime-1997-p11-poly-add
       (aime-1997-p11-poly-monomial -1 36)
       (aime-1997-p11-poly-add
        (aime-1997-p11-poly-monomial 1 12)
        (list 1))))))))

;; Embed a + b*sqrt(2) using sqrt(2) = z^45 + z^315.
(defun aime-1997-p11-embed-qsqrt2 (x)
  (aime-1997-p11-poly-add
   (list (car x))
   (aime-1997-p11-poly-add
    (aime-1997-p11-poly-monomial (cdr x) 45)
    (aime-1997-p11-poly-monomial (cdr x) 315))))

(defun aime-1997-p11-cosine-double-sum (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (aime-1997-p11-poly-add
     (aime-1997-p11-cosine-double-sum (- n 1))
     (aime-1997-p11-poly-add
      (aime-1997-p11-poly-monomial 1 n)
      (aime-1997-p11-poly-monomial 1 (- 360 n))))))

(defun aime-1997-p11-sine-double-i-sum (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (aime-1997-p11-poly-add
     (aime-1997-p11-sine-double-i-sum (- n 1))
     (aime-1997-p11-poly-subtract
      (aime-1997-p11-poly-monomial 1 n)
      (aime-1997-p11-poly-monomial 1 (- 360 n))))))

(defun aime-1997-p11-ratio-equation-polynomial (x)
  (aime-1997-p11-poly-subtract
   (aime-1997-p11-poly-multiply
    (aime-1997-p11-embed-qsqrt2 x)
    (aime-1997-p11-sine-double-i-sum 44))
   (aime-1997-p11-poly-multiply
    (aime-1997-p11-poly-monomial 1 90)
    (aime-1997-p11-cosine-double-sum 44))))

(defun aime-1997-p11-ratio-equation-p (x)
  (equal
   (aime-1997-p11-poly-remainder
    (aime-1997-p11-ratio-equation-polynomial x)
    (aime-1997-p11-cyclotomic-polynomial))
   nil))

(defun aime-1997-p11-statement (x)
  (implies
   (and
    (aime-1997-p11-qsqrt2-p x)
    (aime-1997-p11-ratio-equation-p x))
   (aime-1997-p11-floor-witness-p
    (aime-1997-p11-qsqrt2-scale 100 x)
    241)))

(value-triple :itpeval-statement-checked)
:q
