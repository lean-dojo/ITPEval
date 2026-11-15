;; Statement-only formalization of PutnamBench corpus artifact putnam_1977_a3:
;; recovering a real-valued function from its averages at shifts 1 and 4 by
;; an explicit linear combination of the two average functions. This file
;; contains no proof.

(in-package "ACL2")

;; At a fixed real x, the source hypotheses needed for the conclusion are
;; exactly the four averaging equations for f at x-3, x-1, x+1, and x+3,
;; together with the averaging equation for g at x. Substituting them makes
;; the displayed solution formula a linear identity in
;;
;;   h(x-4), h(x-2), h(x), h(x+2), h(x+4).
;;
;; This local form is bidirectionally equivalent to the arbitrary-function
;; statement. A source counterexample supplies a violating local tuple.
;; Conversely, any local tuple satisfying these equations extends to a real
;; function h (take x=0 and assign the five displayed values arbitrarily);
;; defining f(y)=(h(y+1)+h(y-1))/2 and g(y)=(h(y+4)+h(y-4))/2 gives the
;; global source hypotheses and preserves the local violation.
;;
;; Standard ACL2 has exact rationals rather than a primitive real sort. The
;; local equations and conclusion are affine identities with rational
;; coefficients. A real counterexample would persist after rationally
;; approximating the five free h-values and defining the f- and g-values by
;; the equations, while every rational counterexample is already real.
;; Therefore the rational predicate below has exactly the source theorem's
;; counterexamples and does not restrict its mathematical generality.

(defun putnam-1977-a3-solution-value
    (g-at-x
     f-at-x-minus-3
     f-at-x-minus-1
     f-at-x-plus-1
     f-at-x-plus-3)
  (- (+ (- g-at-x f-at-x-minus-3)
        f-at-x-minus-1
        f-at-x-plus-1)
     f-at-x-plus-3))

(defun putnambench-putnam-1977-a3-statement
    (h-at-x-minus-4
     h-at-x-minus-2
     h-at-x
     h-at-x-plus-2
     h-at-x-plus-4
     f-at-x-minus-3
     f-at-x-minus-1
     f-at-x-plus-1
     f-at-x-plus-3
     g-at-x)
  (implies
   (and
    (rationalp h-at-x-minus-4)
    (rationalp h-at-x-minus-2)
    (rationalp h-at-x)
    (rationalp h-at-x-plus-2)
    (rationalp h-at-x-plus-4)
    (rationalp f-at-x-minus-3)
    (rationalp f-at-x-minus-1)
    (rationalp f-at-x-plus-1)
    (rationalp f-at-x-plus-3)
    (rationalp g-at-x)
    (equal f-at-x-minus-3
           (/ (+ h-at-x-minus-2 h-at-x-minus-4) 2))
    (equal f-at-x-minus-1
           (/ (+ h-at-x h-at-x-minus-2) 2))
    (equal f-at-x-plus-1
           (/ (+ h-at-x-plus-2 h-at-x) 2))
    (equal f-at-x-plus-3
           (/ (+ h-at-x-plus-4 h-at-x-plus-2) 2))
    (equal g-at-x
           (/ (+ h-at-x-plus-4 h-at-x-minus-4) 2)))
   (equal
    h-at-x
    (putnam-1977-a3-solution-value
     g-at-x
     f-at-x-minus-3
     f-at-x-minus-1
     f-at-x-plus-1
     f-at-x-plus-3))))

(value-triple :itpeval-statement-checked)
:q
