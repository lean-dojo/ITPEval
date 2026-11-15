;; Statement-only formalization of PutnamBench corpus artifact putnam_1968_a5:
;; the sharp bound 8 for the derivative at zero of a real quadratic bounded
;; in absolute value by 1 on the unit interval. This file contains no proof.

(in-package "ACL2")

;; For a quadratic a*x^2+b*x+c, the extrema of its absolute value on [0,1]
;; occur at an endpoint or at the unique critical point when that point lies
;; in the interval. Thus this finite predicate is exactly the source's
;; universal interval bound for rational coefficients.
(defun putnam-1968-a5-bounded-quadratic-p (a b c)
  (let ((vertex (/ (- b) (* 2 a))))
    (and (rationalp a)
         (rationalp b)
         (rationalp c)
         (not (equal a 0))
         (<= (abs c) 1)
         (<= (abs (+ a b c)) 1)
         (implies
          (and (<= 0 vertex)
               (<= vertex 1))
          (<= (abs (+ (* a vertex vertex)
                      (* b vertex)
                      c))
              1)))))

;; Restricting the universally quantified coefficient test below to rationals
;; preserves the closed real statement. One direction is specialization. For
;; the converse, a real counterexample with |b| > 8 can be scaled slightly
;; toward zero while still having |b| > 8, making its interval bound strict;
;; sufficiently close rational coefficients then give a rational
;; counterexample and preserve the nonzero leading coefficient.
(defun-sk putnam-1968-a5-universal-upper-bound-p ()
  (forall (a b c)
    (implies
     (putnam-1968-a5-bounded-quadratic-p a b c)
     (<= (abs b) 8))))

;; The source supremum is 8 exactly when 8 is attained and is an upper bound.
;; The quadratic 8*x^2-8*x+1 supplies the internal sharpness witness.
(defun putnambench-putnam-1968-a5-statement ()
  (and
   (putnam-1968-a5-bounded-quadratic-p 8 -8 1)
   (equal (abs -8) 8)
   (putnam-1968-a5-universal-upper-bound-p)))

(value-triple :itpeval-statement-checked)
:q
