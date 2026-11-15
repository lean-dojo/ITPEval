;; Statement-only formalization of miniF2F corpus artifact aime_1999_p11:
;; for a positive reduced rational angle m/n below 90 degrees, if
;; sin(5 degrees) + sin(10 degrees) + ... + sin(175 degrees) equals
;; tan((m/n) degrees), then m + n = 177. The trigonometric equality is
;; encoded exactly by divisibility by the cyclotomic polynomial for a
;; primitive (360*n)-th root of unity. This file contains no proof.

(in-package "ACL2")

;; Polynomials are coefficient lists in ascending degree order.
(defun aime-1999-p11-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (aime-1999-p11-poly-normalize (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun aime-1999-p11-poly-add (left right)
  (cond ((consp left)
         (if (consp right)
             (cons (+ (car left) (car right))
                   (aime-1999-p11-poly-add
                    (cdr left) (cdr right)))
           left))
        (t right)))

(defun aime-1999-p11-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (aime-1999-p11-poly-scale
             scalar (cdr polynomial)))
    nil))

(defun aime-1999-p11-poly-negate (polynomial)
  (aime-1999-p11-poly-scale -1 polynomial))

(defun aime-1999-p11-poly-subtract (left right)
  (aime-1999-p11-poly-normalize
   (aime-1999-p11-poly-add
    left
    (aime-1999-p11-poly-negate right))))

(defun aime-1999-p11-poly-multiply (left right)
  (if (consp left)
      (aime-1999-p11-poly-normalize
       (aime-1999-p11-poly-add
        (aime-1999-p11-poly-scale (car left) right)
        (cons 0
              (aime-1999-p11-poly-multiply
               (cdr left) right))))
    nil))

(defun aime-1999-p11-zero-list (count)
  (if (zp count)
      nil
    (cons 0
          (aime-1999-p11-zero-list (- count 1)))))

(defun aime-1999-p11-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append (aime-1999-p11-zero-list degree)
            (list coefficient))))

(defun aime-1999-p11-poly-degree (polynomial)
  (let ((normalized
         (aime-1999-p11-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun aime-1999-p11-poly-leading-coefficient (polynomial)
  (let ((normalized
         (aime-1999-p11-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (aime-1999-p11-poly-degree normalized)
             normalized)
      0)))

;; A bounded long division is total in ACL2. The bound exceeds the number of
;; degree-lowering steps needed for a nonzero divisor.
(defun aime-1999-p11-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons (aime-1999-p11-poly-normalize quotient)
            (aime-1999-p11-poly-normalize remainder))
    (let* ((normalized-remainder
            (aime-1999-p11-poly-normalize remainder))
           (normalized-divisor
            (aime-1999-p11-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (aime-1999-p11-poly-degree
                  normalized-remainder)
                 (aime-1999-p11-poly-degree
                  normalized-divisor)))
          (cons (aime-1999-p11-poly-normalize quotient)
                normalized-remainder)
        (let* ((degree-difference
                (- (aime-1999-p11-poly-degree
                    normalized-remainder)
                   (aime-1999-p11-poly-degree
                    normalized-divisor)))
               (coefficient
                (/ (aime-1999-p11-poly-leading-coefficient
                    normalized-remainder)
                   (aime-1999-p11-poly-leading-coefficient
                    normalized-divisor)))
               (term
                (aime-1999-p11-poly-monomial
                 coefficient degree-difference)))
          (aime-1999-p11-poly-divmod-steps
           (aime-1999-p11-poly-subtract
            normalized-remainder
            (aime-1999-p11-poly-multiply
             term normalized-divisor))
           normalized-divisor
           (aime-1999-p11-poly-add quotient term)
           (- steps 1)))))))

(defun aime-1999-p11-poly-divmod (dividend divisor)
  (aime-1999-p11-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1
      (len (aime-1999-p11-poly-normalize dividend)))))

(defun aime-1999-p11-poly-quotient (dividend divisor)
  (car (aime-1999-p11-poly-divmod dividend divisor)))

(defun aime-1999-p11-poly-remainder (dividend divisor)
  (cdr (aime-1999-p11-poly-divmod dividend divisor)))

(defun aime-1999-p11-x-to-n-minus-one (n)
  (aime-1999-p11-poly-add
   (list -1)
   (aime-1999-p11-poly-monomial 1 n)))

;; The preceding list contains Phi_1 through Phi_(n-1).
(defun aime-1999-p11-proper-divisor-product
    (n divisor preceding)
  (if (zp divisor)
      (list 1)
    (let ((remaining
           (aime-1999-p11-proper-divisor-product
            n (- divisor 1) preceding)))
      (if (equal (mod n divisor) 0)
          (aime-1999-p11-poly-multiply
           (nth (- divisor 1) preceding)
           remaining)
        remaining))))

;; Phi_n = (x^n - 1) / product_(d|n, d<n) Phi_d.
(defun aime-1999-p11-cyclotomic-list (n)
  (if (zp n)
      nil
    (let* ((preceding
            (aime-1999-p11-cyclotomic-list (- n 1)))
           (proper-divisor-product
            (aime-1999-p11-proper-divisor-product
             n (- n 1) preceding))
           (phi-n
            (aime-1999-p11-poly-quotient
             (aime-1999-p11-x-to-n-minus-one n)
             proper-divisor-product)))
      (append preceding
              (list
               (aime-1999-p11-poly-normalize phi-n))))))

(defun aime-1999-p11-cyclotomic-polynomial (n)
  (if (zp n)
      nil
    (nth (- n 1)
         (aime-1999-p11-cyclotomic-list n))))

;; With z a primitive (360*n)-th root of unity,
;; 2*i*sin(5*k degrees) = z^(5*k*n) - z^(-5*k*n).
(defun aime-1999-p11-sine-difference-sum
    (k denominator root-order)
  (if (zp k)
      nil
    (let ((exponent (* 5 k denominator)))
      (aime-1999-p11-poly-add
       (aime-1999-p11-sine-difference-sum
        (- k 1) denominator root-order)
       (aime-1999-p11-poly-subtract
        (aime-1999-p11-poly-monomial 1 exponent)
        (aime-1999-p11-poly-monomial
         1 (- root-order exponent)))))))

;; Cross-multiplying sum(sin(5*k degrees)) = tan((m/n) degrees)
;; gives A(z)*(z^m + z^(-m)) = 2*(z^m - z^(-m)).
(defun aime-1999-p11-trig-equation-polynomial
    (numerator denominator)
  (let* ((root-order (* 360 denominator))
         (sine-sum
          (aime-1999-p11-sine-difference-sum
           35 denominator root-order))
         (cosine-factor
          (aime-1999-p11-poly-add
           (aime-1999-p11-poly-monomial 1 numerator)
           (aime-1999-p11-poly-monomial
            1 (- root-order numerator))))
         (tangent-sine-factor
          (aime-1999-p11-poly-subtract
           (aime-1999-p11-poly-monomial 1 numerator)
           (aime-1999-p11-poly-monomial
            1 (- root-order numerator)))))
    (aime-1999-p11-poly-subtract
     (aime-1999-p11-poly-multiply
      sine-sum cosine-factor)
     (aime-1999-p11-poly-scale
      2 tangent-sine-factor))))

(defun aime-1999-p11-trig-equation-p
    (numerator denominator)
  (let ((root-order (* 360 denominator)))
    (equal
     (aime-1999-p11-poly-remainder
      (aime-1999-p11-trig-equation-polynomial
       numerator denominator)
      (aime-1999-p11-cyclotomic-polynomial root-order))
     nil)))

(defun aime-1999-p11-statement (angle)
  (let ((m (numerator angle))
        (n (denominator angle)))
    (implies
     (and (rationalp angle)
          (< 0 angle)
          (< angle 90)
          (aime-1999-p11-trig-equation-p m n))
     (equal (+ m n) 177))))

(value-triple :itpeval-statement-checked)
:q
