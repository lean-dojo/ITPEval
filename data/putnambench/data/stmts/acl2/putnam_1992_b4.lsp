;; Statement-only formalization of PutnamBench corpus artifact putnam_1992_b4:
;; the smallest numerator degree after differentiating p(x)/(x^3-x) 1992
;; times, over all admissible real polynomials p, is 3984. This file contains
;; no proof.

(in-package "ACL2")

;; Formal polynomials are coefficient lists in ascending degree order.
;;
;; Put q=x^3-x. For every source polynomial p of degree below 1992, division
;; gives p=h*q+r with deg(h)<1989 and deg(r)<3. The 1992nd derivative of h
;; vanishes, so the source optimization depends exactly on r=a+b*x+c*x^2.
;; Coprimeness with q is equivalent to r being nonzero at -1, 0, and 1.
;;
;; If N_k/q^(k+1) is the kth derivative of r/q away from those three roots,
;; then
;;
;;   N_(k+1) = N_k' * q - (k+1) * N_k * q'.
;;
;; A pair f,g represents the derivative exactly when
;;
;;              f * q^1993 = N_1992 * g.
;;
;; This polynomial identity is equivalent to equality of the rational
;; functions on their common natural domain.
;;
;; The final predicate is universally closed over rational a, b, and c.
;; This is equivalent to the closed real statement, rather than a rational
;; specialization. A failure of the lower bound or root nonvanishing consists
;; of homogeneous rational linear equations in (a,b,c), together with the
;; three rational linear inequations expressing admissibility. Any real point
;; in such a rational linear subspace can be replaced by a rational point
;; avoiding those three hyperplanes. Conversely, every rational failure is a
;; real failure.

(defun putnam-1992-b4-polynomial-p (polynomial)
  (if (consp polynomial)
      (and
       (rationalp (car polynomial))
       (putnam-1992-b4-polynomial-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-1992-b4-polynomial-normalize (polynomial)
  (if (consp polynomial)
      (let ((tail
             (putnam-1992-b4-polynomial-normalize
              (cdr polynomial))))
        (if (and (endp tail)
                 (equal (car polynomial) 0))
            nil
          (cons (car polynomial) tail)))
    nil))

(defun putnam-1992-b4-polynomial-add-raw (left right)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons (+ (car left) (car right))
          (putnam-1992-b4-polynomial-add-raw
           (cdr left) (cdr right))))))

(defun putnam-1992-b4-polynomial-add (left right)
  (putnam-1992-b4-polynomial-normalize
   (putnam-1992-b4-polynomial-add-raw left right)))

(defun putnam-1992-b4-polynomial-negate (polynomial)
  (if (consp polynomial)
      (cons (- (car polynomial))
            (putnam-1992-b4-polynomial-negate
             (cdr polynomial)))
    nil))

(defun putnam-1992-b4-polynomial-subtract (left right)
  (putnam-1992-b4-polynomial-add
   left
   (putnam-1992-b4-polynomial-negate right)))

(defun putnam-1992-b4-polynomial-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-1992-b4-polynomial-scale
             scalar (cdr polynomial)))
    nil))

(defun putnam-1992-b4-polynomial-multiply-raw (left right)
  (if (consp left)
      (putnam-1992-b4-polynomial-add
       (putnam-1992-b4-polynomial-scale (car left) right)
       (cons
        0
        (putnam-1992-b4-polynomial-multiply-raw
         (cdr left) right)))
    nil))

(defun putnam-1992-b4-polynomial-multiply (left right)
  (putnam-1992-b4-polynomial-normalize
   (putnam-1992-b4-polynomial-multiply-raw left right)))

(defun putnam-1992-b4-polynomial-power (polynomial exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (list 1)
    (putnam-1992-b4-polynomial-multiply
     polynomial
     (putnam-1992-b4-polynomial-power
      polynomial (- exponent 1)))))

(defun putnam-1992-b4-polynomial-derivative-aux
    (coefficients multiplier)
  (if (consp coefficients)
      (cons
       (* multiplier (car coefficients))
       (putnam-1992-b4-polynomial-derivative-aux
        (cdr coefficients) (+ multiplier 1)))
    nil))

(defun putnam-1992-b4-polynomial-derivative (polynomial)
  (putnam-1992-b4-polynomial-normalize
   (putnam-1992-b4-polynomial-derivative-aux
    (cdr polynomial) 1)))

(defun putnam-1992-b4-polynomial-evaluate (polynomial x)
  (if (consp polynomial)
      (+ (car polynomial)
         (* x
            (putnam-1992-b4-polynomial-evaluate
             (cdr polynomial) x)))
    0))

(defun putnam-1992-b4-polynomial-degree (polynomial)
  (let ((normalized
         (putnam-1992-b4-polynomial-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun putnam-1992-b4-q ()
  (list 0 -1 0 1))

(defun putnam-1992-b4-q-derivative ()
  (list -1 0 3))

(defun putnam-1992-b4-numerator-step
    (numerator denominator-power)
  (putnam-1992-b4-polynomial-subtract
   (putnam-1992-b4-polynomial-multiply
    (putnam-1992-b4-polynomial-derivative numerator)
    (putnam-1992-b4-q))
   (putnam-1992-b4-polynomial-scale
    denominator-power
    (putnam-1992-b4-polynomial-multiply
     numerator
     (putnam-1992-b4-q-derivative)))))

(defun putnam-1992-b4-iterated-numerator
    (numerator remaining denominator-power)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (putnam-1992-b4-polynomial-normalize numerator)
    (putnam-1992-b4-iterated-numerator
     (putnam-1992-b4-numerator-step
      numerator denominator-power)
     (- remaining 1)
     (+ denominator-power 1))))

(defun putnam-1992-b4-root-coprime-p (polynomial)
  (and
   (not
    (equal
     (putnam-1992-b4-polynomial-evaluate polynomial -1)
     0))
   (not
    (equal
     (putnam-1992-b4-polynomial-evaluate polynomial 0)
     0))
   (not
    (equal
     (putnam-1992-b4-polynomial-evaluate polynomial 1)
     0))))

(defun putnam-1992-b4-valid-remainder-p (a b c)
  (and
   (rationalp a)
   (rationalp b)
   (rationalp c)
   (putnam-1992-b4-root-coprime-p (list a b c))))

(defun putnam-1992-b4-representation-p (a b c f g)
  (let* ((numerator
          (putnam-1992-b4-iterated-numerator
           (list a b c) 1992 1))
         (denominator
          (putnam-1992-b4-polynomial-power
           (putnam-1992-b4-q) 1993)))
    (and
     (putnam-1992-b4-polynomial-p f)
     (putnam-1992-b4-polynomial-p g)
     (consp (putnam-1992-b4-polynomial-normalize g))
     (equal
      (putnam-1992-b4-polynomial-multiply f denominator)
      (putnam-1992-b4-polynomial-multiply numerator g)))))

(defun-sk putnam-1992-b4-lower-bound-p (a b c)
  (forall (f g)
    (implies
     (putnam-1992-b4-representation-p a b c f g)
     (<=
      3984
      (putnam-1992-b4-polynomial-degree f)))))

(defun-sk putnam-1992-b4-attainment-exists-p ()
  (exists (a b c f g)
    (and
     (putnam-1992-b4-valid-remainder-p a b c)
     (putnam-1992-b4-representation-p a b c f g)
     (equal
      (putnam-1992-b4-polynomial-degree f)
      3984))))

(defun putnambench-putnam-1992-b4-statement (a b c)
  (and
   (implies
    (putnam-1992-b4-valid-remainder-p a b c)
    (putnam-1992-b4-lower-bound-p a b c))
   (putnam-1992-b4-attainment-exists-p)))

(value-triple :itpeval-statement-checked)
:q
