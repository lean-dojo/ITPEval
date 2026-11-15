;; Statement-only formalization of miniF2F corpus artifact amc12a_2021_p22:
;; a monic real cubic with zeros cos(2*pi/7), cos(4*pi/7), and cos(6*pi/7)
;; has coefficient product 1/32. The cosine zero set is encoded by its exact
;; integer polynomial, and the file contains no proof.

(in-package "ACL2")

;; The three displayed cosine values are the three distinct real roots of
;;
;;   G(x) = 8*x^3 + 4*x^2 - 4*x - 1.
;;
;; After substituting the source hypothesis that f is the monic cubic P,
;; equality of its zero set with those roots is equivalent to G dividing 8*P.
;; Both polynomials then have degree three and leading coefficient 8, so they
;; are equal. In particular, every satisfying real coefficient triple is
;; rational; restricting the ACL2 arguments to rationals omits no source case.

;; Polynomials are coefficient lists in ascending degree order.
(defun amc12a-2021-p22-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (amc12a-2021-p22-poly-normalize
              (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun amc12a-2021-p22-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (amc12a-2021-p22-poly-add
               (cdr left) (cdr right)))
      left))
   (t right)))

(defun amc12a-2021-p22-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (amc12a-2021-p22-poly-scale
             scalar (cdr polynomial)))
    nil))

(defun amc12a-2021-p22-poly-negate (polynomial)
  (amc12a-2021-p22-poly-scale -1 polynomial))

(defun amc12a-2021-p22-poly-subtract (left right)
  (amc12a-2021-p22-poly-normalize
   (amc12a-2021-p22-poly-add
    left
    (amc12a-2021-p22-poly-negate right))))

(defun amc12a-2021-p22-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (amc12a-2021-p22-zero-list (- count 1)))))

(defun amc12a-2021-p22-poly-shift-scale
    (scalar degree polynomial)
  (append
   (amc12a-2021-p22-zero-list degree)
   (amc12a-2021-p22-poly-scale scalar polynomial)))

(defun amc12a-2021-p22-poly-degree (polynomial)
  (let ((normalized
         (amc12a-2021-p22-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun amc12a-2021-p22-poly-leading-coefficient (polynomial)
  (let ((normalized
         (amc12a-2021-p22-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (amc12a-2021-p22-poly-degree normalized)
             normalized)
      0)))

(defun amc12a-2021-p22-poly-remainder-steps
    (remainder divisor steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (amc12a-2021-p22-poly-normalize remainder)
    (let* ((normalized-remainder
            (amc12a-2021-p22-poly-normalize remainder))
           (normalized-divisor
            (amc12a-2021-p22-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (amc12a-2021-p22-poly-degree
                  normalized-remainder)
                 (amc12a-2021-p22-poly-degree
                  normalized-divisor)))
          normalized-remainder
        (let* ((degree-difference
                (- (amc12a-2021-p22-poly-degree
                    normalized-remainder)
                   (amc12a-2021-p22-poly-degree
                    normalized-divisor)))
               (coefficient
                (/ (amc12a-2021-p22-poly-leading-coefficient
                    normalized-remainder)
                   (amc12a-2021-p22-poly-leading-coefficient
                    normalized-divisor))))
          (amc12a-2021-p22-poly-remainder-steps
           (amc12a-2021-p22-poly-subtract
            normalized-remainder
            (amc12a-2021-p22-poly-shift-scale
             coefficient
             degree-difference
             normalized-divisor))
           normalized-divisor
           (- steps 1)))))))

(defun amc12a-2021-p22-poly-remainder (dividend divisor)
  (amc12a-2021-p22-poly-remainder-steps
   dividend
   divisor
   (+ 1 (len (amc12a-2021-p22-poly-normalize dividend)))))

(defun amc12a-2021-p22-cosine-root-polynomial ()
  (list -1 -4 4 8))

(defun amc12a-2021-p22-scaled-cubic (a b c)
  (list (* 8 c) (* 8 b) (* 8 a) 8))

(defun amc12a-2021-p22-same-zero-set-p (a b c)
  (and
   (rationalp a)
   (rationalp b)
   (rationalp c)
   (equal
    (amc12a-2021-p22-poly-remainder
     (amc12a-2021-p22-scaled-cubic a b c)
     (amc12a-2021-p22-cosine-root-polynomial))
    nil)))

(defun amc12a-2021-p22-statement (a b c)
  (implies
   (amc12a-2021-p22-same-zero-set-p a b c)
   (equal (* a b c) (/ 1 32))))

(value-triple :itpeval-statement-checked)
:q
