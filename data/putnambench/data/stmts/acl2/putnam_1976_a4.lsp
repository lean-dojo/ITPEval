;; Statement-only formalization of PutnamBench corpus artifact putnam_1976_a4:
;; an irreducible integer cubic and a shifted integer cubic force one of two
;; explicit rational functions of a real root to be another root.
;; This file contains no proof.

(in-package "ACL2")

;; Coefficient lists are in ascending degree order.  For
;;
;;   P(X) = X^3 + a*X^2 + b*X - 1,
;;
;; irreducibility over the rationals is equivalent to the absence of a
;; rational root.  The rational-root theorem reduces this, for this monic
;; cubic, to P(1) = a+b and P(-1) = a-b-2 both being nonzero.
(defun putnam-1976-a4-irreducible-p (a b)
  (and (integerp a)
       (integerp b)
       (not (equal (+ a b) 0))
       (not (equal (- (- a b) 2) 0))))

;; If P is irreducible and r is any of its real roots, then P is the minimal
;; polynomial of r.  Hence a polynomial F of degree at most three vanishes at
;; r exactly when its remainder modulo P is zero.  Subtracting the leading
;; coefficient of F times P gives the three remainder coefficients below.
;; This is an exact algebraic encoding of the source real root, not a
;; restriction to rational roots.
(defun putnam-1976-a4-zero-at-p-root-p (polynomial a b)
  (let ((leading (nth 3 polynomial)))
    (and
     (equal (+ (nth 0 polynomial) leading) 0)
     (equal (- (nth 1 polynomial)
               (* leading b))
            0)
     (equal (- (nth 2 polynomial)
               (* leading a))
            0))))

;; Q(X+1), where Q(X) = X^3 + c*X^2 + d*X + 1.
(defun putnam-1976-a4-shifted-q (c d)
  (list (+ (+ c d) 2)
        (+ (+ 3 (* 2 c)) d)
        (+ 3 c)
        1))

;; With t = r+1, this is the coefficient list of
;; t^3 * P(-1/t).  Irreducibility makes t nonzero because P(-1) is nonzero.
(defun putnam-1976-a4-first-candidate-numerator (a b)
  (list (- (- a b) 2)
        (- (- a (* 2 b)) 3)
        (- (- b) 3)
        -1))

;; This is the coefficient list of
;; r^3 * P(-(r+1)/r).  Here r is nonzero because P(0) = -1.
(defun putnam-1976-a4-second-candidate-numerator (a b)
  (list -1
        (- a 3)
        (- (- (* 2 a) b) 3)
        (- (- a b) 2)))

;; The source existential
;;
;;   exists s, P(s)=0 and
;;     (s=-1/(r+1) or s=-(r+1)/r)
;;
;; is equivalent to the disjunction that one of those two displayed values
;; is a root.  The two numerator polynomials above clear only nonzero
;; denominators.  Likewise, Q(r+1)=0 is represented exactly by vanishing of
;; Q(X+1) in the quotient by the minimal polynomial P.
(defun putnambench-putnam-1976-a4-statement (a b c d)
  (implies
   (and (integerp a)
        (integerp b)
        (integerp c)
        (integerp d)
        (putnam-1976-a4-irreducible-p a b)
        (putnam-1976-a4-zero-at-p-root-p
         (putnam-1976-a4-shifted-q c d)
         a b))
   (or
    (putnam-1976-a4-zero-at-p-root-p
     (putnam-1976-a4-first-candidate-numerator a b)
     a b)
    (putnam-1976-a4-zero-at-p-root-p
     (putnam-1976-a4-second-candidate-numerator a b)
     a b))))

(value-triple :itpeval-statement-checked)
:q
