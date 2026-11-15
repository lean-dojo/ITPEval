;; Statement-only formalization of PutnamBench corpus artifact putnam_2022_b1:
;; every coefficient of the exponential power series of an integer polynomial
;; with zero constant term and odd linear coefficient is nonzero. This file
;; contains no proof.

(in-package "ACL2")

;; POLYNOMIAL lists the integer coefficients a_0,...,a_d in ascending degree
;; order, with no trailing zero. This is a bijective presentation of the
;; source's integer polynomials under the hypotheses a_0 = 0 and odd a_1.

(defun putnam-2022-b1-integer-list-p (values)
  (if (consp values)
      (and (integerp (car values))
           (putnam-2022-b1-integer-list-p (cdr values)))
    (equal values nil)))

(defun putnam-2022-b1-polynomial-p (polynomial)
  (and
   (true-listp polynomial)
   (<= 2 (len polynomial))
   (putnam-2022-b1-integer-list-p polynomial)
   (not (equal (car (last polynomial)) 0))))

(defun putnam-2022-b1-polynomial-coefficient
    (polynomial degree)
  (if (and (natp degree)
           (< degree (len polynomial)))
      (nth degree polynomial)
    0))

;; If B(x) = sum_n b_n x^n = exp(P(x)), then B' = P' B. Coefficient
;; comparison gives
;;
;;   b_0 = 1,
;;   n b_n = sum_{j=1}^n j a_j b_{n-j}.
;;
;; PREVIOUS contains b_0,...,b_(n-1), and INDEX descends from n to 1.

(defun putnam-2022-b1-recurrence-sum
    (polynomial previous degree index)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      0
    (+ (* index
          (putnam-2022-b1-polynomial-coefficient
           polynomial index)
          (nth (- degree index) previous))
       (putnam-2022-b1-recurrence-sum
        polynomial previous degree (- index 1)))))

(defun putnam-2022-b1-coefficient-prefix-aux
    (polynomial remaining coefficients)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      coefficients
    (let* ((degree (len coefficients))
           (next
            (/ (putnam-2022-b1-recurrence-sum
                polynomial coefficients degree degree)
               degree)))
      (putnam-2022-b1-coefficient-prefix-aux
       polynomial
       (- remaining 1)
       (append coefficients (list next))))))

(defun putnam-2022-b1-exponential-coefficient
    (polynomial degree)
  (if (natp degree)
      (nth degree
           (putnam-2022-b1-coefficient-prefix-aux
            polynomial degree (list 1)))
    0))

;; The recurrence uniquely determines the formal series exp(P), and for every
;; real polynomial P this formal series is the Maclaurin series of the entire
;; function exp(P(x)). Conversely, the source HasSum/convergence hypothesis
;; uniquely forces b to have these coefficients. Since the a_j are integers,
;; the recurrence also proves that every forced real coefficient is rational;
;; ACL2's exact rationals therefore represent those same values rather than a
;; restriction of the source domain. Eliminating b and its defining analytic
;; hypothesis is thus bidirectionally equivalent to the source implication.
;; The free natural DEGREE is the source's universally quantified k.

(defun putnambench-putnam-2022-b1-statement
    (polynomial degree)
  (implies
   (and
    (putnam-2022-b1-polynomial-p polynomial)
    (equal
     (putnam-2022-b1-polynomial-coefficient polynomial 0)
     0)
    (oddp
     (putnam-2022-b1-polynomial-coefficient polynomial 1))
    (natp degree))
   (not
    (equal
     (putnam-2022-b1-exponential-coefficient
      polynomial degree)
     0))))

(value-triple :itpeval-statement-checked)
:q
