;; Statement-only formalization of PutnamBench corpus artifact putnam_1980_b5:
;; the parameters for which nonnegative strictly increasing convex continuous
;; functions satisfying a finite-difference inequality are closed under
;; pointwise multiplication. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Write a=f(0), b=f(1/3), c=f(2/3), and d=f(1).  Such values come from a
;; nonnegative strictly increasing convex continuous function on [0,1]
;; exactly when a>=0 and the three successive increments are positive and
;; nondecreasing: piecewise-linear interpolation gives the reverse direction.
;; The final inequality is precisely the defining P(t,f) condition.
(defun putnam-1980-b5-member-data-p (t-param a b c d)
  (and
   (rationalp t-param)
   (rationalp a)
   (rationalp b)
   (rationalp c)
   (rationalp d)
   (<= 0 a)
   (< a b)
   (< b c)
   (< c d)
   (<= (- b a) (- c b))
   (<= (- c b) (- d c))
   (<=
    (* t-param (+ c a (- (* 2 b))))
    (+ d b (- (* 2 c))))))

;; Nonnegativity, strict increase, convexity, and continuity are preserved by
;; the pointwise product of two source members.  Consequently closure under
;; multiplication is equivalent to this remaining P(t,f*g) inequality on
;; their four values.
(defun putnam-1980-b5-product-condition-p
    (t-param f0 f1 f2 f3 g0 g1 g2 g3)
  (<=
   (* t-param
      (+ (* f2 g2)
         (* f0 g0)
         (- (* 2 f1 g1))))
   (+ (* f3 g3)
      (* f1 g1)
      (- (* 2 f2 g2)))))

;; For t>1, let the successive increments of f=g be
;;
;;   1, 1+delta, 1+(t+1)*delta.
;;
;; Then P(t,f) and P(t,g) hold with equality.  The positive delta below is
;; small enough that P(t,f*g) fails, giving an internal counterexample rather
;; than exposing an existential function as a statement parameter.
(defun putnam-1980-b5-counterexample-delta (t-param)
  (if (and (rationalp t-param)
           (< 1 t-param))
      (/ (- t-param 1)
         (* 4
            (+ t-param 1)
            (+ t-param 2)))
    0))

(defun putnam-1980-b5-explicit-counterexample-p (t-param)
  (let* ((delta
          (putnam-1980-b5-counterexample-delta t-param))
         (a 0)
         (b 1)
         (c (+ 2 delta))
         (d (+ 3 (* (+ t-param 2) delta))))
    (and
     (putnam-1980-b5-member-data-p t-param a b c d)
     (not
      (putnam-1980-b5-product-condition-p
       t-param a b c d a b c d)))))

;; This is an exact rational encoding of the closed real statement, not a
;; restriction of its domain.  For rational t, any real counterexample to the
;; finite inequalities can be perturbed within their strict conditions to a
;; rational counterexample, and rational instances are real instances.
;; For a real t<=1, a product violation has a strictly smaller ratio, so a
;; rational parameter between that ratio and t would also be a counterexample.
;; For every real t>1, the explicit formula above is itself a real
;; counterexample.  Thus the universal rational statement below holds iff the
;; source universal real statement holds.
(defun putnambench-putnam-1980-b5-statement
    (t-param f0 f1 f2 f3 g0 g1 g2 g3)
  (implies
   (and
    (rationalp t-param)
    (<= 0 t-param))
   (if (<= t-param 1)
       (implies
        (and
         (putnam-1980-b5-member-data-p
          t-param f0 f1 f2 f3)
         (putnam-1980-b5-member-data-p
          t-param g0 g1 g2 g3))
        (putnam-1980-b5-product-condition-p
         t-param f0 f1 f2 f3 g0 g1 g2 g3))
     (putnam-1980-b5-explicit-counterexample-p
      t-param))))

(value-triple :itpeval-statement-checked)
:q
