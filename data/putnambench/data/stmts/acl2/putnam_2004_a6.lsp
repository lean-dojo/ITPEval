;; Statement-only formalization of PutnamBench corpus artifact putnam_2004_a6:
;; the two squared marginal integrals of a continuous real function on the
;; unit square satisfy the stated integral inequality. This file contains no
;; proof.

(in-package "ACL2")

;; A monomial is the true list (c a b), denoting c*x^a*y^b with rational
;; coefficient c and natural exponents a,b. A polynomial is an arbitrary
;; finite list of such monomials; repeated exponent pairs simply add their
;; coefficients. Thus the root predicate is universally closed over every
;; rational bivariate polynomial, with no degree or term-count bound.
;;
;; This is bidirectionally equivalent to the sources' universal proposition
;; over continuous real functions on [0,1]^2. In the forward direction,
;; rational polynomials are continuous, so they are source instances. In the
;; reverse direction, rational bivariate polynomials are uniformly dense in
;; C([0,1]^2): real polynomials are dense by Stone-Weierstrass, and their
;; finitely many coefficients can be approximated by rationals. Uniform
;; convergence f_n -> f gives uniform convergence of both marginal integrals
;; and of f_n^2 -> f^2 (the sequence is uniformly bounded). Therefore each
;; of the four integral expressions below is continuous in the uniform norm,
;; and the non-strict inequality passes to the limit. Consequently validity
;; for every rational polynomial is equivalent to validity for every
;; continuous source function, rather than a restriction to a finite model.
;;
;; The formulas compute the integrals exactly, using
;; integral_0^1 t^n dt = 1/(n+1). Ordinary recursive ACL2 functions suffice;
;; no quoted lambda, FN-EQUAL, or APPLY$ term is generated. NIL represents
;; the zero function, is a valid polynomial, and makes both sides exactly
;; zero, so the statement domain is inhabited and the implication is
;; non-vacuous.

(defun putnam-2004-a6-monomial-p (term)
  (and (true-listp term)
       (equal (len term) 3)
       (rationalp (nth 0 term))
       (natp (nth 1 term))
       (natp (nth 2 term))))

(defun putnam-2004-a6-polynomial-p (polynomial)
  (if (consp polynomial)
      (and (putnam-2004-a6-monomial-p (car polynomial))
           (putnam-2004-a6-polynomial-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-2004-a6-coefficient (term)
  (nth 0 term))

(defun putnam-2004-a6-x-degree (term)
  (nth 1 term))

(defun putnam-2004-a6-y-degree (term)
  (nth 2 term))

;; Exact contribution of one monomial to the square integral.
(defun putnam-2004-a6-monomial-integral (term)
  (/ (putnam-2004-a6-coefficient term)
     (* (+ 1 (putnam-2004-a6-x-degree term))
        (+ 1 (putnam-2004-a6-y-degree term)))))

(defun putnam-2004-a6-polynomial-integral (polynomial)
  (if (consp polynomial)
      (+ (putnam-2004-a6-monomial-integral (car polynomial))
         (putnam-2004-a6-polynomial-integral (cdr polynomial)))
    0))

;; For monomials c_i*x^a_i*y^b_i and c_j*x^a_j*y^b_j, this is
;;
;;   integral_0^1
;;     (integral_0^1 c_i*x^a_i*y^b_i dx)
;;     (integral_0^1 c_j*x^a_j*y^b_j dx) dy.
(defun putnam-2004-a6-x-marginal-pair (left right)
  (/ (* (putnam-2004-a6-coefficient left)
        (putnam-2004-a6-coefficient right))
     (* (+ 1 (putnam-2004-a6-x-degree left))
        (+ 1 (putnam-2004-a6-x-degree right))
        (+ 1
           (putnam-2004-a6-y-degree left)
           (putnam-2004-a6-y-degree right)))))

;; This is the analogous pair contribution after integrating first in y.
(defun putnam-2004-a6-y-marginal-pair (left right)
  (/ (* (putnam-2004-a6-coefficient left)
        (putnam-2004-a6-coefficient right))
     (* (+ 1 (putnam-2004-a6-y-degree left))
        (+ 1 (putnam-2004-a6-y-degree right))
        (+ 1
           (putnam-2004-a6-x-degree left)
           (putnam-2004-a6-x-degree right)))))

(defun putnam-2004-a6-left-pair (left right)
  (+ (putnam-2004-a6-x-marginal-pair left right)
     (putnam-2004-a6-y-marginal-pair left right)))

(defun putnam-2004-a6-left-pairs-with (left polynomial)
  (if (consp polynomial)
      (+ (putnam-2004-a6-left-pair left (car polynomial))
         (putnam-2004-a6-left-pairs-with left (cdr polynomial)))
    0))

(defun putnam-2004-a6-left-side-sum (remaining polynomial)
  (if (consp remaining)
      (+ (putnam-2004-a6-left-pairs-with
          (car remaining) polynomial)
         (putnam-2004-a6-left-side-sum
          (cdr remaining) polynomial))
    0))

;; Exact contribution of a monomial pair to integral_[0,1]^2 f(x,y)^2.
(defun putnam-2004-a6-square-integral-pair (left right)
  (/ (* (putnam-2004-a6-coefficient left)
        (putnam-2004-a6-coefficient right))
     (* (+ 1
           (putnam-2004-a6-x-degree left)
           (putnam-2004-a6-x-degree right))
        (+ 1
           (putnam-2004-a6-y-degree left)
           (putnam-2004-a6-y-degree right)))))

(defun putnam-2004-a6-square-pairs-with (left polynomial)
  (if (consp polynomial)
      (+ (putnam-2004-a6-square-integral-pair
          left (car polynomial))
         (putnam-2004-a6-square-pairs-with
          left (cdr polynomial)))
    0))

(defun putnam-2004-a6-square-integral-sum
    (remaining polynomial)
  (if (consp remaining)
      (+ (putnam-2004-a6-square-pairs-with
          (car remaining) polynomial)
         (putnam-2004-a6-square-integral-sum
          (cdr remaining) polynomial))
    0))

(defun putnambench-putnam-2004-a6-statement (polynomial)
  (implies
   (putnam-2004-a6-polynomial-p polynomial)
   (let ((integral
          (putnam-2004-a6-polynomial-integral polynomial)))
     (<=
      (putnam-2004-a6-left-side-sum polynomial polynomial)
      (+ (* integral integral)
         (putnam-2004-a6-square-integral-sum
          polynomial polynomial))))))

(value-triple :itpeval-statement-checked)
:q
