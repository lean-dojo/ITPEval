;; Statement-only formalization of PutnamBench corpus artifact
;; putnam_1967_a3: the least positive leading coefficient of an integer
;; quadratic with two distinct real zeros in (0,1) is 5. This file contains
;; no proof.

(in-package "ACL2")

;; Write the polynomial as A*x^2 - B*x + C, with A positive. A positive
;; discriminant gives two distinct real roots. By Vieta's formulas, B > 0
;; and C > 0 make both roots positive. After substituting y = 1-x, the sum
;; and product of the two y-roots are (2*A-B)/A and (A-B+C)/A, so B < 2*A
;; and A-B+C > 0 make both original roots less than one.
;;
;; Conversely, two roots in (0,1) imply every displayed inequality, including
;; C < A because their product is C/A < 1. Thus this integer coefficient
;; predicate is bidirectionally equivalent to the source's real-root condition.
(defun putnam-1967-a3-admissible-coefficients-p (a b c)
  (and (integerp a)
       (integerp b)
       (integerp c)
       (< 0 a)
       (< 0 b)
       (< 0 c)
       (< b (* 2 a))
       (< c a)
       (< 0 (+ a (- b) c))
       (< 0 (- (* b b) (* 4 a c)))))

;; The root conditions force 1 <= B < 2*A and 1 <= C < A. These finite
;; searches therefore preserve the source's internal existential coefficient
;; witnesses rather than restricting their domains.
(defun putnam-1967-a3-some-c-p (a b c)
  (declare (xargs :measure (nfix c)))
  (if (zp c)
      nil
    (or (putnam-1967-a3-admissible-coefficients-p a b c)
        (putnam-1967-a3-some-c-p a b (- c 1)))))

(defun putnam-1967-a3-some-b-p (a b)
  (declare (xargs :measure (nfix b)))
  (if (zp b)
      nil
    (or (putnam-1967-a3-some-c-p a b (- a 1))
        (putnam-1967-a3-some-b-p a (- b 1)))))

(defun putnam-1967-a3-leading-coefficient-p (a)
  (and (integerp a)
       (< 0 a)
       (putnam-1967-a3-some-b-p a (- (* 2 a) 1))))

;; Since admissible leading coefficients are positive integers, membership of
;; 5 together with nonmembership of 1, 2, 3, and 4 is exactly IsLeast at 5.
(defun putnambench-putnam-1967-a3-statement ()
  (and (putnam-1967-a3-leading-coefficient-p 5)
       (not (putnam-1967-a3-leading-coefficient-p 1))
       (not (putnam-1967-a3-leading-coefficient-p 2))
       (not (putnam-1967-a3-leading-coefficient-p 3))
       (not (putnam-1967-a3-leading-coefficient-p 4))))

(value-triple :itpeval-statement-checked)
:q
