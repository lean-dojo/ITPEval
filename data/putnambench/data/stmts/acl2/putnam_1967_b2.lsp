;; Statement-only formalization of PutnamBench artifact putnam_1967_b2:
;; lower bounds for the largest coefficients in two quadratic identities
;; determined by parameters in the real unit interval. This file contains
;; no proof.

(in-package "ACL2")

;; Comparing coefficients makes the two universally quantified real
;; polynomial identities equivalent to the six equations below:
;;
;;   A = p^2,  B = 2*p*(1-p),  C = (1-p)^2,
;;   alpha = p*r,
;;   beta = p*(1-r) + (1-p)*r,
;;   gamma = (1-p)*(1-r).
;;
;; Standard ACL2 has exact rationals rather than a primitive real sort. The
;; rational predicate is nevertheless bidirectionally equivalent to the
;; source universal real statement. Every rational instance is a real
;; instance. Conversely, a real counterexample makes at least one of the two
;; maxima strictly less than 4/9. After the coefficient equations eliminate
;; A, B, C, alpha, beta, and gamma, that strict violation is an open condition
;; on p and r relative to the closed square [0,1]^2. Rational points are dense
;; in that square, so a nearby rational p,r preserves the interval bounds and
;; the same strict violation; defining the six coefficients by the displayed
;; equations gives an exact rational counterexample.
(defun putnambench-putnam-1967-b2-statement
    (p r a b c alpha beta gamma)
  (implies
   (and
    (rationalp p)
    (rationalp r)
    (rationalp a)
    (rationalp b)
    (rationalp c)
    (rationalp alpha)
    (rationalp beta)
    (rationalp gamma)
    (<= 0 p)
    (<= p 1)
    (<= 0 r)
    (<= r 1)
    (equal a (* p p))
    (equal b (* 2 p (- 1 p)))
    (equal c (* (- 1 p) (- 1 p)))
    (equal alpha (* p r))
    (equal beta
           (+ (* p (- 1 r))
              (* (- 1 p) r)))
    (equal gamma (* (- 1 p) (- 1 r))))
   (and
    (or (<= (/ 4 9) a)
        (<= (/ 4 9) b)
        (<= (/ 4 9) c))
    (or (<= (/ 4 9) alpha)
        (<= (/ 4 9) beta)
        (<= (/ 4 9) gamma)))))

(value-triple :itpeval-statement-checked)
:q
