;; Statement-only formalization of PutnamBench corpus artifact putnam_1970_b2:
;; the two-node Gaussian quadrature identity for every real polynomial of
;; degree at most three on a symmetric interval. This file contains no proof.

(in-package "ACL2")

;; Multivariate polynomials over the rationals represent arbitrary real
;; assignments to T and to the four coefficients of H. A monomial is a sorted
;; list of variable indices, with repetition denoting powers; a polynomial is
;; a canonical sorted list of (monomial . coefficient) pairs.

(defun putnam-1970-b2-monomial-multiply (left right)
  (declare (xargs :measure
                  (+ (acl2-count left) (acl2-count right))))
  (cond ((endp left) right)
        ((endp right) left)
        ((<= (car left) (car right))
         (cons (car left)
               (putnam-1970-b2-monomial-multiply
                (cdr left) right)))
        (t
         (cons (car right)
               (putnam-1970-b2-monomial-multiply
                left (cdr right))))))

(defun putnam-1970-b2-polynomial-insert
    (monomial coefficient polynomial)
  (cond ((equal coefficient 0) polynomial)
        ((endp polynomial)
         (list (cons monomial coefficient)))
        ((equal monomial (caar polynomial))
         (let ((sum (+ coefficient (cdar polynomial))))
           (if (equal sum 0)
               (cdr polynomial)
             (cons (cons monomial sum)
                   (cdr polynomial)))))
        ((lexorder monomial (caar polynomial))
         (cons (cons monomial coefficient) polynomial))
        (t
         (cons (car polynomial)
               (putnam-1970-b2-polynomial-insert
                monomial coefficient (cdr polynomial))))))

(defun putnam-1970-b2-polynomial-add (left right)
  (if (endp left)
      right
    (putnam-1970-b2-polynomial-add
     (cdr left)
     (putnam-1970-b2-polynomial-insert
      (caar left) (cdar left) right))))

(defun putnam-1970-b2-polynomial-negate (polynomial)
  (if (endp polynomial)
      nil
    (cons
     (cons (caar polynomial) (- (cdar polynomial)))
     (putnam-1970-b2-polynomial-negate
      (cdr polynomial)))))

(defun putnam-1970-b2-polynomial-subtract (left right)
  (putnam-1970-b2-polynomial-add
   left
   (putnam-1970-b2-polynomial-negate right)))

(defun putnam-1970-b2-polynomial-scale (scalar polynomial)
  (if (endp polynomial)
      nil
    (cons
     (cons (caar polynomial) (* scalar (cdar polynomial)))
     (putnam-1970-b2-polynomial-scale
      scalar (cdr polynomial)))))

(defun putnam-1970-b2-polynomial-multiply-term
    (monomial coefficient polynomial)
  (if (endp polynomial)
      nil
    (putnam-1970-b2-polynomial-insert
     (putnam-1970-b2-monomial-multiply
      monomial (caar polynomial))
     (* coefficient (cdar polynomial))
     (putnam-1970-b2-polynomial-multiply-term
      monomial coefficient (cdr polynomial)))))

(defun putnam-1970-b2-polynomial-multiply (left right)
  (if (endp left)
      nil
    (putnam-1970-b2-polynomial-add
     (putnam-1970-b2-polynomial-multiply-term
      (caar left) (cdar left) right)
     (putnam-1970-b2-polynomial-multiply
      (cdr left) right))))

(defun putnam-1970-b2-polynomial-power (polynomial exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (list (cons nil 1))
    (putnam-1970-b2-polynomial-multiply
     polynomial
     (putnam-1970-b2-polynomial-power
      polynomial (- exponent 1)))))

(defun putnam-1970-b2-polynomial-variable (index)
  (list (cons (list index) 1)))

;; A pair (P . Q) denotes P + Q*s in the exact quadratic extension with
;; s^2 = 3. Thus T/s is represented exactly as (T/3)*s.

(defun putnam-1970-b2-extension-base (polynomial)
  (cons polynomial nil))

(defun putnam-1970-b2-extension-add (left right)
  (cons
   (putnam-1970-b2-polynomial-add
    (car left) (car right))
   (putnam-1970-b2-polynomial-add
    (cdr left) (cdr right))))

(defun putnam-1970-b2-extension-multiply (left right)
  (cons
   (putnam-1970-b2-polynomial-add
    (putnam-1970-b2-polynomial-multiply
     (car left) (car right))
    (putnam-1970-b2-polynomial-scale
     3
     (putnam-1970-b2-polynomial-multiply
      (cdr left) (cdr right))))
   (putnam-1970-b2-polynomial-add
    (putnam-1970-b2-polynomial-multiply
     (car left) (cdr right))
    (putnam-1970-b2-polynomial-multiply
     (cdr left) (car right)))))

(defun putnam-1970-b2-cubic-eval-extension
    (coefficients point)
  (putnam-1970-b2-extension-add
   (putnam-1970-b2-extension-base (nth 0 coefficients))
   (putnam-1970-b2-extension-multiply
    point
    (putnam-1970-b2-extension-add
     (putnam-1970-b2-extension-base (nth 1 coefficients))
     (putnam-1970-b2-extension-multiply
      point
      (putnam-1970-b2-extension-add
       (putnam-1970-b2-extension-base (nth 2 coefficients))
       (putnam-1970-b2-extension-multiply
        point
        (putnam-1970-b2-extension-base
         (nth 3 coefficients)))))))))

;; For H(x)=a0+a1*x+a2*x^2+a3*x^3, this is its exact antiderivative
;; a0*x+(a1/2)*x^2+(a2/3)*x^3+(a3/4)*x^4.

(defun putnam-1970-b2-antiderivative-value
    (coefficients point)
  (putnam-1970-b2-polynomial-add
   (putnam-1970-b2-polynomial-multiply
    (nth 0 coefficients) point)
   (putnam-1970-b2-polynomial-add
    (putnam-1970-b2-polynomial-scale
     1/2
     (putnam-1970-b2-polynomial-multiply
      (nth 1 coefficients)
      (putnam-1970-b2-polynomial-power point 2)))
    (putnam-1970-b2-polynomial-add
     (putnam-1970-b2-polynomial-scale
      1/3
      (putnam-1970-b2-polynomial-multiply
       (nth 2 coefficients)
       (putnam-1970-b2-polynomial-power point 3)))
     (putnam-1970-b2-polynomial-scale
      1/4
      (putnam-1970-b2-polynomial-multiply
       (nth 3 coefficients)
       (putnam-1970-b2-polynomial-power point 4)))))))

;; Variable 0 is T; variables 1 through 4 are the arbitrary real
;; coefficients a0 through a3. Multiplying the source equality by 2*T gives
;;
;;   T * (H(-T/sqrt(3)) + H(T/sqrt(3)))
;;     = integral_[-T,T] H.
;;
;; This is reversible because the source assumes T > 0. The right side below
;; is the exact antiderivative difference. Equality of these generic formal
;; polynomials is equivalent to the displayed equality under every real
;; coefficient assignment and every positive real T.

(defun putnambench-putnam-1970-b2-statement ()
  (let* ((time (putnam-1970-b2-polynomial-variable 0))
         (negative-time
          (putnam-1970-b2-polynomial-negate time))
         (coefficients
          (list
           (putnam-1970-b2-polynomial-variable 1)
           (putnam-1970-b2-polynomial-variable 2)
           (putnam-1970-b2-polynomial-variable 3)
           (putnam-1970-b2-polynomial-variable 4)))
         (positive-node
          (cons
           nil
           (putnam-1970-b2-polynomial-scale 1/3 time)))
         (negative-node
          (cons
           nil
           (putnam-1970-b2-polynomial-scale -1/3 time)))
         (quadrature-sum
          (putnam-1970-b2-extension-add
           (putnam-1970-b2-cubic-eval-extension
            coefficients negative-node)
           (putnam-1970-b2-cubic-eval-extension
            coefficients positive-node)))
         (cleared-quadrature
          (putnam-1970-b2-extension-multiply
           (putnam-1970-b2-extension-base time)
           quadrature-sum))
         (integral
          (putnam-1970-b2-polynomial-subtract
           (putnam-1970-b2-antiderivative-value
            coefficients time)
           (putnam-1970-b2-antiderivative-value
            coefficients negative-time))))
    (equal
     cleared-quadrature
     (putnam-1970-b2-extension-base integral))))

(value-triple :itpeval-statement-checked)
:q
