;; Statement-only formalization of PutnamBench corpus artifact putnam_1987_a3:
;; classification of two positivity implications for twice-differentiable
;; real solutions of a second-order exponential ODE. This file contains no
;; proof.

(in-package "ACL2")

;; For any source solution f, put f(x)=exp(x)*q(x). Since exp(x) is positive,
;;
;;   f'' - 2*f' + f = exp(x)*q'',
;;   f > 0             iff q > 0,
;;   f' > 0            iff q + q' > 0.
;;
;; Thus the source ODE is equivalent to q''=2. Its twice-differentiable real
;; solutions are exactly q(x)=x^2+a*x+b, and every such polynomial gives a
;; source solution. This is a bidirectional normal-form equivalence, not a
;; restriction to polynomial source functions.

(defun putnam-1987-a3-quadratic (a b x)
  (+ (* x x) (* a x) b))

(defun putnam-1987-a3-quadratic-derivative (a x)
  (+ (* 2 x) a))

(defun putnam-1987-a3-first-derivative-factor (a b x)
  (+ (putnam-1987-a3-quadratic a b x)
     (putnam-1987-a3-quadratic-derivative a x)))

(defun putnam-1987-a3-second-derivative-factor (a b x)
  (+ (putnam-1987-a3-quadratic a b x)
     (* 2 (putnam-1987-a3-quadratic-derivative a x))
     2))

(defun putnam-1987-a3-ode-factor (a b x)
  (+ (putnam-1987-a3-second-derivative-factor a b x)
     (* -2
        (putnam-1987-a3-first-derivative-factor a b x))
     (putnam-1987-a3-quadratic a b x)))

;; The first source implication is false. The internal witness
;; f(x)=exp(x)*(x^2+1) satisfies the ODE and is strictly positive, while
;; f'(-1)=0. The pointwise polynomial identities below express all three
;; facts without exposing the existential function witness as a parameter.
(defun putnam-1987-a3-first-counterexample-at-p (x)
  (and
   (equal (putnam-1987-a3-ode-factor 0 1 x) 2)
   (< 0 (putnam-1987-a3-quadratic 0 1 x))
   (equal
    (putnam-1987-a3-first-derivative-factor 0 1 -1)
    0)))

;; A monic real quadratic x^2+linear*x+constant is positive at every real x
;; exactly when its discriminant is negative.
(defun putnam-1987-a3-positive-monic-quadratic-p
    (linear constant)
  (< (* linear linear)
     (* 4 constant)))

;; For q=x^2+a*x+b, the factor q+q' is
;;
;;   x^2+(a+2)*x+(a+b).
;;
;; Its strict positivity therefore says a^2+4 < 4*b, which directly implies
;; a^2 < 4*b, the strict positivity criterion for q. This is exactly the
;; second source implication in the normal form above.
(defun putnam-1987-a3-second-normal-form-p (a b)
  (implies
   (putnam-1987-a3-positive-monic-quadratic-p
    (+ a 2)
    (+ a b))
   (putnam-1987-a3-positive-monic-quadratic-p
    a b)))

;; ACL2's exact ordered field is rational. The counterexample has rational
;; coefficients, and the second clause is the ordered-field implication
;; a^2+4<4*b => a^2<4*b. Hence its universal rational closure and universal
;; real closure are bidirectionally equivalent; no real counterexample can be
;; lost by this exact algebraic presentation.
(defun putnambench-putnam-1987-a3-statement (a b x)
  (implies
   (and (rationalp a)
        (rationalp b)
        (rationalp x))
   (and
    (putnam-1987-a3-first-counterexample-at-p x)
    (putnam-1987-a3-second-normal-form-p a b))))

(value-triple :itpeval-statement-checked)
:q
