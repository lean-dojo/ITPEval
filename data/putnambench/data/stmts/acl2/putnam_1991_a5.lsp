;; Statement-only formalization of PutnamBench corpus artifact putnam_1991_a5:
;; the maximum over 0 <= y <= 1 of the integral from 0 to y of
;; sqrt(x^4 + (y-y^2)^2) is 1/3. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; For nonnegative rational X and positive integer SCALE, this is a rational
;; upper approximation to sqrt(X), with error at most 1/SCALE.
(defun putnam-1991-a5-isqrt-search (x candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp x))
          (not (natp candidate)))
      0
    (if (<= (* candidate candidate) x)
        candidate
      (putnam-1991-a5-isqrt-search
       x (- candidate 1)))))

(defun putnam-1991-a5-isqrt (x)
  (if (natp x)
      (putnam-1991-a5-isqrt-search x x)
    0))

(defun putnam-1991-a5-sqrt-upper (x scale)
  (if (and (rationalp x)
           (<= 0 x)
           (posp scale))
      (/ (+ 1
            (putnam-1991-a5-isqrt
             (floor (* x scale scale) 1)))
         scale)
    0))

(defun putnam-1991-a5-integrand-upper (x y scale)
  (putnam-1991-a5-sqrt-upper
   (+ (expt x 4)
      (expt (- y (expt y 2)) 2))
   scale))

;; The right-endpoint sum is an upper Riemann sum because the integrand is
;; nondecreasing in x on [0,y].
(defun putnam-1991-a5-sum-through (y n scale i)
  (declare (xargs :measure (nfix i)))
  (if (or (not (rationalp y))
          (not (posp n))
          (not (posp scale))
          (not (natp i))
          (zp i))
      0
    (+ (putnam-1991-a5-integrand-upper
        (/ (* y i) n)
        y
        scale)
       (putnam-1991-a5-sum-through
        y n scale (- i 1)))))

(defun putnam-1991-a5-integral-upper (y n scale)
  (if (and (rationalp y)
           (<= 0 y)
           (<= y 1)
           (posp n)
           (posp scale))
      (* (/ y n)
         (putnam-1991-a5-sum-through
          y n scale n))
    0))

(defun putnam-1991-a5-solution ()
  1/3)

;; The rational upper sums converge to the source integral for each rational
;; y in [0,1]. The integral depends continuously on the real parameter y, and
;; rationals are dense, so its upper bound on rational y is equivalent in both
;; directions to its upper bound on every real y. The witness is quantified
;; internally, matching IsGreatest rather than naming a maximizing endpoint in
;; the statement.
(defun-sk putnam-1991-a5-tail-p (witness epsilon cutoff)
  (forall (y n scale)
    (implies
     (and
      (rationalp y)
      (<= 0 y)
      (<= y 1)
      (natp n)
      (<= cutoff n)
      (natp scale)
      (<= cutoff scale))
     (and
      (< (putnam-1991-a5-integral-upper y n scale)
         (+ (putnam-1991-a5-solution) epsilon))
      (< (abs
          (- (putnam-1991-a5-integral-upper witness n scale)
             (putnam-1991-a5-solution)))
         epsilon)))))

(defun-sk putnam-1991-a5-cutoff-exists-p
    (witness epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1991-a5-tail-p
      witness epsilon cutoff))))

(defun-sk putnam-1991-a5-maximum-witness-p (witness)
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-1991-a5-cutoff-exists-p
      witness epsilon))))

(defun-sk putnambench-putnam-1991-a5-statement ()
  (exists (witness)
    (and
     (rationalp witness)
     (<= 0 witness)
     (<= witness 1)
     (putnam-1991-a5-maximum-witness-p witness))))

(value-triple :itpeval-statement-checked)
:q
