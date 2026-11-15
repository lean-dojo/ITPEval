;; Statement-only formalization of PutnamBench corpus artifact putnam_2018_a3:
;; the greatest possible value of the sum of cos(3*x_i) for ten real x_i
;; whose cosines sum to zero is 480/49. This file contains no proof.

(in-package "ACL2")

;; Put c_i = cos(x_i). Every c_i in [-1,1] is the cosine of a real x_i, and
;; cos(3*x_i) = 4*c_i^3 - 3*c_i. Thus the source optimization is exactly the
;; polynomial optimization below on
;;
;;   {c in [-1,1]^10 : sum_i c_i = 0}.
;;
;; Standard ACL2 has exact rational arithmetic rather than a primitive real
;; sort. Rational points are dense in this rational polytope. Since the
;; objective is continuous, a strict real violation of the proposed upper
;; bound would have a rational violation, while every rational violation is
;; already a real violation. Hence the universal rational inequality is
;; bidirectionally equivalent to the universal real inequality. The existential
;; rational attainment clause is equivalent to real attainment here because
;; the maximum is attained at the rational tuple with three entries equal to 1
;; and seven entries equal to -3/7.

(defun putnam-2018-a3-triple-cosine (c)
  (- (* 4 c c c)
     (* 3 c)))

(defun putnam-2018-a3-feasible-p
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
  (and
   (rationalp c0)
   (rationalp c1)
   (rationalp c2)
   (rationalp c3)
   (rationalp c4)
   (rationalp c5)
   (rationalp c6)
   (rationalp c7)
   (rationalp c8)
   (rationalp c9)
   (<= -1 c0) (<= c0 1)
   (<= -1 c1) (<= c1 1)
   (<= -1 c2) (<= c2 1)
   (<= -1 c3) (<= c3 1)
   (<= -1 c4) (<= c4 1)
   (<= -1 c5) (<= c5 1)
   (<= -1 c6) (<= c6 1)
   (<= -1 c7) (<= c7 1)
   (<= -1 c8) (<= c8 1)
   (<= -1 c9) (<= c9 1)
   (equal (+ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
          0)))

(defun putnam-2018-a3-objective
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
  (+ (putnam-2018-a3-triple-cosine c0)
     (putnam-2018-a3-triple-cosine c1)
     (putnam-2018-a3-triple-cosine c2)
     (putnam-2018-a3-triple-cosine c3)
     (putnam-2018-a3-triple-cosine c4)
     (putnam-2018-a3-triple-cosine c5)
     (putnam-2018-a3-triple-cosine c6)
     (putnam-2018-a3-triple-cosine c7)
     (putnam-2018-a3-triple-cosine c8)
     (putnam-2018-a3-triple-cosine c9)))

(defun-sk putnam-2018-a3-maximum-attained-p ()
  (exists (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
    (and
     (putnam-2018-a3-feasible-p
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
     (equal
      (putnam-2018-a3-objective
       c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
      (/ 480 49)))))

(defun-sk putnam-2018-a3-upper-bound-p ()
  (forall (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
    (implies
     (putnam-2018-a3-feasible-p
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
     (<=
      (putnam-2018-a3-objective
       c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
      (/ 480 49)))))

(defun putnambench-putnam-2018-a3-statement ()
  (and
   (putnam-2018-a3-maximum-attained-p)
   (putnam-2018-a3-upper-bound-p)))

(value-triple :itpeval-statement-checked)
:q
