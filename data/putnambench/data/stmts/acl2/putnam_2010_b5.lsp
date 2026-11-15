;; Statement-only formalization of PutnamBench corpus artifact putnam_2010_b5:
;; no strictly increasing differentiable real function satisfies
;; f'(x) = f(f(x)) at every real x. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; F-APPROX(x,epsilon) is an arbitrary rational regular-Cauchy name for f(x)
;; at rational x.  The other conservative symbols supply compact continuity,
;; strict-order, and derivative-convergence witnesses.  DEFSTUB leaves all
;; four mappings arbitrary; unlike APPLY$ function objects, it imposes no
;; executability or definability restriction.
;;
;; The DEFUN-SK predicates below give unbounded first-order constraints on
;; these symbols.  A regular name plus compact uniform continuity determines
;; a unique continuous real extension.  Strict increase on rational inputs
;; then extends to all reals.  The final predicate rules out every arbitrary
;; tuple whose difference quotients converge on compact intervals to the
;; nested Cauchy approximation of f(f(x)), which is equivalent to the source
;; existential statement having answer False.

(defstub putnam-2010-b5-f-approx (x epsilon) t)
(defstub putnam-2010-b5-compact-modulus (bound epsilon) t)
(defstub putnam-2010-b5-derivative-modulus (bound epsilon) t)
(defstub putnam-2010-b5-increase-margin (x y) t)

(defun putnam-2010-b5-positive-rational-p (value)
  (and
   (rationalp value)
   (< 0 value)))

(defun putnam-2010-b5-in-bounded-interval-p
    (value bound)
  (and
   (rationalp value)
   (<= (- bound) value)
   (<= value bound)))

(defun-sk putnam-2010-b5-regular-cauchy-data-p ()
  (forall (x epsilon eta)
    (implies
     (and
      (rationalp x)
      (putnam-2010-b5-positive-rational-p epsilon)
      (putnam-2010-b5-positive-rational-p eta))
     (let ((left
            (putnam-2010-b5-f-approx x epsilon))
           (right
            (putnam-2010-b5-f-approx x eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

(defun-sk putnam-2010-b5-compact-continuity-p ()
  (forall (bound x y epsilon)
    (implies
     (and
      (posp bound)
      (putnam-2010-b5-in-bounded-interval-p
       x bound)
      (putnam-2010-b5-in-bounded-interval-p
       y bound)
      (putnam-2010-b5-positive-rational-p epsilon))
     (let* ((delta
             (putnam-2010-b5-compact-modulus
              bound epsilon))
            (left
             (putnam-2010-b5-f-approx
              x (* 1/4 epsilon)))
            (right
             (putnam-2010-b5-f-approx
              y (* 1/4 epsilon))))
       (and
        (putnam-2010-b5-positive-rational-p delta)
        (implies
         (< (abs (- x y)) delta)
         (and
          (rationalp left)
          (rationalp right)
          (<= (abs (- left right))
              epsilon))))))))

(defun-sk putnam-2010-b5-strictly-increasing-p ()
  (forall (x y)
    (implies
     (and
      (rationalp x)
      (rationalp y)
      (< x y))
     (let* ((margin
             (putnam-2010-b5-increase-margin x y))
            (precision (* 1/4 margin))
            (left
             (putnam-2010-b5-f-approx x precision))
            (right
             (putnam-2010-b5-f-approx y precision)))
       (and
        (putnam-2010-b5-positive-rational-p margin)
        (rationalp left)
        (rationalp right)
        (< (+ left margin)
           (- right margin)))))))

(defun-sk putnam-2010-b5-derivative-equation-p ()
  (forall (bound x h epsilon)
    (implies
     (and
      (posp bound)
      (putnam-2010-b5-in-bounded-interval-p
       x bound)
      (rationalp h)
      (not (equal h 0))
      (putnam-2010-b5-positive-rational-p epsilon))
     (let* ((delta
             (putnam-2010-b5-derivative-modulus
              bound epsilon))
            (absolute-h (abs h))
            (quotient-precision
             (* absolute-h (* 1/32 epsilon)))
            (shifted-x (+ x h))
            (shifted-value
             (putnam-2010-b5-f-approx
              shifted-x quotient-precision))
            (value
             (putnam-2010-b5-f-approx
              x quotient-precision))
            (quotient
             (/ (- shifted-value value) h))
            (continuity-tolerance (* 1/32 epsilon))
            (function-coarse
             (putnam-2010-b5-f-approx x 1))
            (composition-bound
             (+ 3 (floor (abs function-coarse) 1)))
            (composition-delta
             (putnam-2010-b5-compact-modulus
              composition-bound
              continuity-tolerance))
            (half-composition-delta
             (* 1/2 composition-delta))
            (inner-tolerance
             (if (< 1/4 half-composition-delta)
                 1/4
               half-composition-delta))
            (inner-value
             (putnam-2010-b5-f-approx
              x inner-tolerance))
            (composition
             (putnam-2010-b5-f-approx
              inner-value
              (* 1/64 epsilon))))
       (and
        (putnam-2010-b5-positive-rational-p delta)
        (implies
         (<= absolute-h delta)
         (and
          (rationalp shifted-value)
          (rationalp value)
          (rationalp quotient)
          (rationalp function-coarse)
          (posp composition-bound)
          (putnam-2010-b5-positive-rational-p
           composition-delta)
          (putnam-2010-b5-positive-rational-p
           inner-tolerance)
          (rationalp inner-value)
          (rationalp composition)
          (<= (abs (- quotient composition))
              epsilon))))))))

(defun putnambench-putnam-2010-b5-statement ()
  (not
   (and
    (putnam-2010-b5-regular-cauchy-data-p)
    (putnam-2010-b5-compact-continuity-p)
    (putnam-2010-b5-strictly-increasing-p)
    (putnam-2010-b5-derivative-equation-p))))

(value-triple :itpeval-statement-checked)
:q
