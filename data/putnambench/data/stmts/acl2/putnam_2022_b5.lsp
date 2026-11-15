;; Statement-only formalization of PutnamBench corpus artifact putnam_2022_b5:
;; the zero value has maximal probability for every finite integer linear
;; combination of independent {-1,0,1}-valued variables exactly when the
;; common probability p lies in [0,1/4]. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; This conservative generic symbol is an arbitrary rational regular Cauchy
;; name for the real parameter p. Regularity and all order assumptions remain
;; explicit below, so the symbol supplies no mathematical premise by itself.
(defstub putnam-2022-b5-p-approx (precision) t)

(defun putnam-2022-b5-positive-rational-p (value)
  (and
   (rationalp value)
   (< 0 value)))

;; At each positive rational precision the stub returns a rational
;; approximation. Pairwise regularity gives a unique real limit, and every
;; classical real admits such a rational regular Cauchy name.
(defun-sk putnam-2022-b5-real-name-p ()
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2022-b5-positive-rational-p epsilon)
      (putnam-2022-b5-positive-rational-p eta))
     (let ((left (putnam-2022-b5-p-approx epsilon))
           (right (putnam-2022-b5-p-approx eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

;; For a regular name q, its limit is at least LOWER exactly when
;; LOWER <= q(epsilon)+epsilon for every positive rational epsilon.
(defun-sk putnam-2022-b5-real-at-least-p (lower)
  (forall (epsilon)
    (implies
     (putnam-2022-b5-positive-rational-p epsilon)
     (let ((value (putnam-2022-b5-p-approx epsilon)))
       (and
        (rationalp lower)
        (rationalp value)
        (<= lower (+ value epsilon)))))))

;; Dually, the limit is at most UPPER exactly when
;; q(epsilon) <= UPPER+epsilon for every positive rational epsilon.
(defun-sk putnam-2022-b5-real-at-most-p (upper)
  (forall (epsilon)
    (implies
     (putnam-2022-b5-positive-rational-p epsilon)
     (let ((value (putnam-2022-b5-p-approx epsilon)))
       (and
        (rationalp upper)
        (rationalp value)
        (<= value (+ upper epsilon)))))))

(defun putnam-2022-b5-integer-list-p (values)
  (if (consp values)
      (and
       (integerp (car values))
       (putnam-2022-b5-integer-list-p (cdr values)))
    (equal values nil)))

;; The source functions XSET, XPROB, and P are uniquely fixed by their
;; hypotheses. This recursive three-branch convolution is their definition:
;; X_i=1, 0, and -1 have respective weights p, 1-2p, and p.
(defun putnam-2022-b5-mass-value
    (p-value coefficients target)
  (if (consp coefficients)
      (let* ((coefficient (car coefficients))
             (rest (cdr coefficients))
             (zero-weight (- 1 (* 2 p-value))))
        (+
         (* p-value
            (putnam-2022-b5-mass-value
             p-value rest (- target coefficient)))
         (* zero-weight
            (putnam-2022-b5-mass-value
             p-value rest target))
         (* p-value
            (putnam-2022-b5-mass-value
             p-value rest (+ target coefficient)))))
    (if (equal target 0) 1 0)))

(defun putnam-2022-b5-error-scale (length)
  (* (+ (nfix length) 1)
     (expt 6 (+ (nfix length) 1))))

(defun putnam-2022-b5-comparison-precision
    (coefficients epsilon)
  (let ((candidate
         (/ epsilon
            (putnam-2022-b5-error-scale
             (len coefficients)))))
    (if (< candidate 1/4)
        candidate
      1/4)))

(defun putnam-2022-b5-mass
    (coefficients target epsilon)
  (let* ((precision
          (putnam-2022-b5-comparison-precision
           coefficients epsilon))
         (p-value
          (putnam-2022-b5-p-approx precision)))
    (putnam-2022-b5-mass-value
     p-value coefficients target)))

;; When 0 <= p <= 1/2, the selected precision gives a uniform error below
;; EPSILON for each finite mass. Thus the following comparison for every
;; positive EPSILON is equivalent to the exact inequality
;; P(0,a_1,...,a_n) >= P(b,a_1,...,a_n).
(defun-sk putnam-2022-b5-maximum-at-zero-p ()
  (forall (target coefficients epsilon)
    (implies
     (and
      (integerp target)
      (putnam-2022-b5-integer-list-p coefficients)
      (consp coefficients)
      (putnam-2022-b5-positive-rational-p epsilon))
     (let* ((precision
             (putnam-2022-b5-comparison-precision
              coefficients epsilon))
            (zero-mass
             (putnam-2022-b5-mass
              coefficients 0 epsilon))
            (target-mass
             (putnam-2022-b5-mass
              coefficients target epsilon)))
       (and
        (putnam-2022-b5-positive-rational-p precision)
        (rationalp zero-mass)
        (rationalp target-mass)
        (<= target-mass
            (+ zero-mass epsilon epsilon)))))))

;; The DEFSTUB is schematic, so this zero-arity predicate states the
;; characterization for an arbitrary represented real p.
(defun putnambench-putnam-2022-b5-statement ()
  (implies
   (putnam-2022-b5-real-name-p)
   (iff
    (and
     (putnam-2022-b5-real-at-least-p 0)
     (putnam-2022-b5-real-at-most-p 1/2)
     (putnam-2022-b5-maximum-at-zero-p))
    (and
     (putnam-2022-b5-real-at-least-p 0)
     (putnam-2022-b5-real-at-most-p 1/4)))))

(value-triple :itpeval-statement-checked)
:q
