;; Statement-only formalization of PutnamBench corpus artifact putnam_2011_b5:
;; a whole-line integral bound for finite sums of Cauchy kernels implies a
;; positive cubic lower bound for the pairwise squared-distance sum. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; This conservative generic symbol supplies a regular rational Cauchy name
;; for a_n at every natural n. It is an arbitrary function symbol, not a
;; rational-valued sequence or a finite table. Every real sequence admits such
;; a name, and every name satisfying PUTNAM-2011-B5-REGULAR-NAME-P determines
;; a unique real sequence.
(defstub putnam-2011-b5-a-approx (n epsilon) t)

(defun putnam-2011-b5-positive-rational-p (x)
  (and
   (rationalp x)
   (< 0 x)))

(defun-sk putnam-2011-b5-regular-name-p ()
  (forall (n epsilon eta)
    (implies
     (and
      (natp n)
      (putnam-2011-b5-positive-rational-p epsilon)
      (putnam-2011-b5-positive-rational-p eta))
     (let ((at-epsilon
            (putnam-2011-b5-a-approx n epsilon))
           (at-eta
            (putnam-2011-b5-a-approx n eta)))
       (and
        (rationalp at-epsilon)
        (rationalp at-eta)
        (<=
         (abs (- at-epsilon at-eta))
         (+ epsilon eta)))))))

;; Expanding the square in the source integral and integrating termwise uses
;; the exact identity
;;
;;   integral_R 1/((1+(x-u)^2)(1+(x-v)^2)) dx
;;     = 2*pi/(4+(u-v)^2).
;;
;; Thus the source hypothesis is equivalent to a linear bound on the finite
;; double sum of 1/(4+(a_i-a_j)^2). The positive factor 2*pi is absorbed into
;; the existential constant. A real bound exists exactly when a rational
;; bound exists, since a larger rational may be chosen.

(defun putnam-2011-b5-reciprocal-row
    (left-value remaining precision)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let* ((index (- (nfix remaining) 1))
           (right-value
            (putnam-2011-b5-a-approx index precision))
           (difference (- left-value right-value)))
      (+ (/ 1 (+ 4 (* difference difference)))
         (putnam-2011-b5-reciprocal-row
          left-value index precision)))))

(defun putnam-2011-b5-reciprocal-sum-aux
    (remaining total precision)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let* ((index (- (nfix remaining) 1))
           (left-value
            (putnam-2011-b5-a-approx index precision)))
      (+ (putnam-2011-b5-reciprocal-row
          left-value total precision)
         (putnam-2011-b5-reciprocal-sum-aux
          index total precision)))))

;; The reciprocal kernel is globally Lipschitz. With this precision, the
;; approximation error in the terms-by-terms double sum is strictly less than
;; the requested epsilon.
(defun putnam-2011-b5-reciprocal-precision
    (epsilon terms)
  (/ epsilon
     (* 4
        (expt (+ (nfix terms) 1) 2))))

(defun putnam-2011-b5-reciprocal-sum
    (terms epsilon)
  (let ((precision
         (putnam-2011-b5-reciprocal-precision
          epsilon terms)))
    (putnam-2011-b5-reciprocal-sum-aux
     terms terms precision)))

(defun-sk putnam-2011-b5-upper-bound-p (constant)
  (forall (terms epsilon)
    (implies
     (and
      (natp terms)
      (putnam-2011-b5-positive-rational-p epsilon))
     (<=
      (putnam-2011-b5-reciprocal-sum
       terms epsilon)
      (+ (* constant terms)
         epsilon)))))

(defun-sk putnam-2011-b5-upper-bound-exists-p ()
  (exists (constant)
    (and
     (rationalp constant)
     (putnam-2011-b5-upper-bound-p constant))))

;; A precision-one approximation gives a finite magnitude bound for every
;; entry in the prefix. This makes the chosen precision below control the
;; error introduced by squaring unbounded real differences.

(defun putnam-2011-b5-prefix-bound (remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      1
    (let ((index (- (nfix remaining) 1)))
      (+ 2
         (abs
          (putnam-2011-b5-a-approx index 1))
         (putnam-2011-b5-prefix-bound index)))))

(defun putnam-2011-b5-square-row
    (left-value remaining precision)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let* ((index (- (nfix remaining) 1))
           (right-value
            (putnam-2011-b5-a-approx index precision))
           (difference (- left-value right-value)))
      (+ 1
         (* difference difference)
         (putnam-2011-b5-square-row
          left-value index precision)))))

(defun putnam-2011-b5-square-sum-aux
    (remaining total precision)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let* ((index (- (nfix remaining) 1))
           (left-value
            (putnam-2011-b5-a-approx index precision)))
      (+ (putnam-2011-b5-square-row
          left-value total precision)
         (putnam-2011-b5-square-sum-aux
          index total precision)))))

(defun putnam-2011-b5-square-precision
    (terms epsilon)
  (let ((candidate
         (/ epsilon
            (* 16
               (putnam-2011-b5-prefix-bound terms)
               (expt (+ (nfix terms) 1) 2)))))
    (if (< candidate 1)
        candidate
      1)))

(defun putnam-2011-b5-square-sum
    (terms epsilon)
  (let ((precision
         (putnam-2011-b5-square-precision
          terms epsilon)))
    (putnam-2011-b5-square-sum-aux
     terms terms precision)))

;; Requiring the epsilon-relaxed comparison at every positive rational
;; epsilon is exactly the comparison between the represented real sum and
;; B*n^3. Restricting B to positive rationals is equivalent to the source's
;; positive real witness, since a smaller positive rational may be chosen.

(defun-sk putnam-2011-b5-lower-bound-p (constant)
  (forall (terms epsilon)
    (implies
     (and
      (natp terms)
      (putnam-2011-b5-positive-rational-p epsilon))
     (<=
      (* constant (expt terms 3))
      (+ (putnam-2011-b5-square-sum
          terms epsilon)
         epsilon)))))

(defun-sk putnam-2011-b5-lower-bound-exists-p ()
  (exists (constant)
    (and
     (putnam-2011-b5-positive-rational-p constant)
     (putnam-2011-b5-lower-bound-p constant))))

(defun putnambench-putnam-2011-b5-statement ()
  (implies
   (and
    (putnam-2011-b5-regular-name-p)
    (putnam-2011-b5-upper-bound-exists-p))
   (putnam-2011-b5-lower-bound-exists-p)))

(value-triple :itpeval-statement-checked)
:q
