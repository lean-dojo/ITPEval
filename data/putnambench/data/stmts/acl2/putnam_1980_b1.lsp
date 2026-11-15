;; Statement-only formalization of PutnamBench corpus artifact putnam_1980_b1:
;; the real constants c for which (exp(x) + exp(-x))/2 is at most
;; exp(c*x^2) for every real x are exactly those with c >= 1/2. This file
;; contains no proof.

(in-package "ACL2")

;; Standard ACL2 has exact rational arithmetic but no primitive real
;; exponential. The rational Taylor prefixes below converge to exp(y).
(defun putnam-1980-b1-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1980-b1-factorial (- n 1)))))

(defun putnam-1980-b1-exp-prefix (y terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- terms 1)))
      (+ (putnam-1980-b1-exp-prefix y index)
         (/ (expt y index)
            (putnam-1980-b1-factorial index))))))

;; Multiplying the source inequality by exp(K), where
;;
;;   K = 1 + floor(|x| + |c*x^2|),
;;
;; gives
;;
;;   exp(K+x) + exp(K-x) <= 2*exp(K+c*x^2).
;;
;; All three Taylor arguments are nonnegative. Requiring every sufficiently
;; long pair of prefixes to satisfy the inequality up to every positive
;; rational tolerance is exactly the non-strict real inequality after taking
;; limits.
(defun putnam-1980-b1-shift (c x)
  (+ 1
     (floor (+ (abs x)
               (abs (* c x x)))
            1)))

(defun putnam-1980-b1-forward-approximant-p
    (c x epsilon left-terms right-terms)
  (let* ((shift (putnam-1980-b1-shift c x))
         (positive-x (+ shift x))
         (negative-x (- shift x))
         (quadratic (+ shift (* c x x))))
    (< (+ (putnam-1980-b1-exp-prefix
           positive-x left-terms)
          (putnam-1980-b1-exp-prefix
           negative-x left-terms))
       (+ (* 2
             (putnam-1980-b1-exp-prefix
              quadratic right-terms))
          epsilon))))

(defun-sk putnam-1980-b1-forward-tail-p
    (c x epsilon cutoff)
  (forall (left-terms right-terms)
    (implies
     (and
      (natp left-terms)
      (natp right-terms)
      (<= cutoff left-terms)
      (<= cutoff right-terms))
     (putnam-1980-b1-forward-approximant-p
      c x epsilon left-terms right-terms))))

(defun-sk putnam-1980-b1-forward-cutoff-exists-p
    (c x epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (< 0 cutoff)
     (putnam-1980-b1-forward-tail-p
      c x epsilon cutoff))))

(defun putnam-1980-b1-reverse-approximant-p
    (c x margin left-terms right-terms)
  (let* ((shift (putnam-1980-b1-shift c x))
         (positive-x (+ shift x))
         (negative-x (- shift x))
         (quadratic (+ shift (* c x x))))
    (< (+ (* 2
             (putnam-1980-b1-exp-prefix
              quadratic right-terms))
          margin)
       (+ (putnam-1980-b1-exp-prefix
           positive-x left-terms)
          (putnam-1980-b1-exp-prefix
           negative-x left-terms)))))

(defun-sk putnam-1980-b1-reverse-tail-p
    (c x margin cutoff)
  (forall (left-terms right-terms)
    (implies
     (and
      (natp left-terms)
      (natp right-terms)
      (<= cutoff left-terms)
      (<= cutoff right-terms))
     (putnam-1980-b1-reverse-approximant-p
      c x margin left-terms right-terms))))

;; For c < 1/2 the source asks only for some real counterexample. A strict
;; real counterexample persists at a nearby rational x, and a positive
;; rational margin can be placed below its gap. The existential below states
;; exactly that eventual strict prefix separation; it does not prescribe a
;; witness or a Taylor rate.
(defun-sk putnam-1980-b1-counterexample-exists-p (c)
  (exists (x margin cutoff)
    (and
     (rationalp x)
     (rationalp margin)
     (< 0 margin)
     (natp cutoff)
     (< 0 cutoff)
     (putnam-1980-b1-reverse-tail-p
      c x margin cutoff))))

;; Rational c and x suffice without narrowing the theorem. Continuity extends
;; the forward inequality from rational x to real x. Monotonicity in c extends
;; it from rational c >= 1/2 to every real c >= 1/2. If a real c is below
;; 1/2, choose a rational r with c < r < 1/2; a counterexample for r is also
;; one for c. Thus the two clauses below are bidirectionally equivalent to the
;; source characterization over all reals.
(defun putnambench-putnam-1980-b1-statement
    (c x epsilon)
  (and
   (implies
    (and (rationalp c)
         (<= 1/2 c)
         (rationalp x)
         (rationalp epsilon)
         (< 0 epsilon))
    (putnam-1980-b1-forward-cutoff-exists-p
     c x epsilon))
   (implies
    (and (rationalp c)
         (< c 1/2))
    (putnam-1980-b1-counterexample-exists-p c))))

(value-triple :itpeval-statement-checked)
:q
