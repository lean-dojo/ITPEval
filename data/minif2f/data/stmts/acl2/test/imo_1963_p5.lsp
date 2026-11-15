;; Statement-only formalization of miniF2F corpus artifact imo_1963_p5:
;; cos(pi/7) - cos(2*pi/7) + cos(3*pi/7) equals 1/2. The real
;; trigonometric identity is encoded exactly using the minimal polynomial of
;; exp(i*pi/7). This file contains no proof.

(in-package "ACL2")

;; Let z = exp(i*pi/7), a primitive 14th root of unity. Since
;; 2*cos(k*pi/7) = z^k + z^(-k), the source identity is equivalent to
;;
;;   z^13 - z^12 + z^11 + z^3 - z^2 + z - 1 = 0.
;;
;; The minimal polynomial of z over the rationals is
;;
;;   Phi_14(x) = x^6 - x^5 + x^4 - x^3 + x^2 - x + 1.
;;
;; Thus the displayed equality is equivalent to exact divisibility of the
;; first polynomial by Phi_14. Polynomials below use ascending coefficients.

(defun imo-1963-p5-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (imo-1963-p5-poly-normalize
              (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun imo-1963-p5-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (imo-1963-p5-poly-add
               (cdr left) (cdr right)))
      left))
   (t right)))

(defun imo-1963-p5-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (imo-1963-p5-poly-scale
             scalar (cdr polynomial)))
    nil))

(defun imo-1963-p5-poly-negate (polynomial)
  (imo-1963-p5-poly-scale -1 polynomial))

(defun imo-1963-p5-poly-subtract (left right)
  (imo-1963-p5-poly-normalize
   (imo-1963-p5-poly-add
    left
    (imo-1963-p5-poly-negate right))))

(defun imo-1963-p5-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (imo-1963-p5-zero-list (- count 1)))))

(defun imo-1963-p5-poly-shift-scale
    (scalar degree polynomial)
  (append
   (imo-1963-p5-zero-list degree)
   (imo-1963-p5-poly-scale scalar polynomial)))

(defun imo-1963-p5-poly-degree (polynomial)
  (let ((normalized
         (imo-1963-p5-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun imo-1963-p5-poly-leading-coefficient (polynomial)
  (let ((normalized
         (imo-1963-p5-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (imo-1963-p5-poly-degree normalized)
             normalized)
      0)))

(defun imo-1963-p5-poly-remainder-steps
    (remainder divisor steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (imo-1963-p5-poly-normalize remainder)
    (let* ((normalized-remainder
            (imo-1963-p5-poly-normalize remainder))
           (normalized-divisor
            (imo-1963-p5-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (imo-1963-p5-poly-degree
                  normalized-remainder)
                 (imo-1963-p5-poly-degree
                  normalized-divisor)))
          normalized-remainder
        (let* ((degree-difference
                (- (imo-1963-p5-poly-degree
                    normalized-remainder)
                   (imo-1963-p5-poly-degree
                    normalized-divisor)))
               (coefficient
                (/ (imo-1963-p5-poly-leading-coefficient
                    normalized-remainder)
                   (imo-1963-p5-poly-leading-coefficient
                    normalized-divisor))))
          (imo-1963-p5-poly-remainder-steps
           (imo-1963-p5-poly-subtract
            normalized-remainder
            (imo-1963-p5-poly-shift-scale
             coefficient
             degree-difference
             normalized-divisor))
           normalized-divisor
           (- steps 1)))))))

(defun imo-1963-p5-poly-remainder (dividend divisor)
  (imo-1963-p5-poly-remainder-steps
   dividend
   divisor
   (+ 1 (len (imo-1963-p5-poly-normalize dividend)))))

(defun imo-1963-p5-cyclotomic-polynomial ()
  (list 1 -1 1 -1 1 -1 1))

(defun imo-1963-p5-trigonometric-identity-polynomial ()
  (list -1 1 -1 1 0 0 0 0 0 0 0 1 -1 1))

(defun imo-1963-p5-statement ()
  (equal
   (imo-1963-p5-poly-remainder
    (imo-1963-p5-trigonometric-identity-polynomial)
    (imo-1963-p5-cyclotomic-polynomial))
   nil))

(value-triple :itpeval-statement-checked)
:q
