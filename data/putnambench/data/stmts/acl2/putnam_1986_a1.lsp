;; Statement-only formalization of PutnamBench corpus artifact putnam_1986_a1:
;; the greatest value of x^3 - 3*x over real x satisfying
;; x^4 + 36 <= 13*x^2 is 18. This file contains no proof.

(in-package "ACL2")

;; Standard ACL2 has exact rational arithmetic rather than a primitive real
;; sort. The constraint factors as
;;
;;   (x^2 - 4)*(x^2 - 9) <= 0,
;;
;; so its real solution set is [-3,-2] union [2,3]. The objective is a
;; polynomial, rational points are dense in both intervals, and the value 18
;; is attained at the rational point x = 3. Consequently the rational
;; greatest-value predicate below and the source real predicate imply each
;; other: restriction gives one direction, while density and continuity give
;; the other without changing the maximum.

(defun putnam-1986-a1-objective (x)
  (- (* x x x)
     (* 3 x)))

(defun putnam-1986-a1-admissible-p (x)
  (and
   (rationalp x)
   (<= (+ (* x x x x) 36)
       (* 13 x x))))

(defun putnambench-putnam-1986-a1-statement (competitor)
  (and
   (putnam-1986-a1-admissible-p 3)
   (equal (putnam-1986-a1-objective 3) 18)
   (implies
    (putnam-1986-a1-admissible-p competitor)
    (<= (putnam-1986-a1-objective competitor)
        18))))

(value-triple :itpeval-statement-checked)
:q
