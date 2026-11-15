;; Statement-only formalization of PutnamBench corpus artifact putnam_1970_b1:
;; the real limit of a normalized finite product of positive nth roots,
;; evaluated as exp(2 log 5 - 4 + 2 arctan 2). This file contains no proof.

(in-package "ACL2")

;; For n > 0, put
;;
;;   P_n = product_(i=1)^(2n) (n^2+i^2).
;;
;; The source sequence is exactly P_n^(1/n)/n^4.  The scaled-root search
;; returns the greatest integer k with k^n <= P_n*scale^n, so k/scale is a
;; lower approximation to the positive real nth root with error below
;; 1/scale.  Thus the normalized rational value below differs from the source
;; term by less than 1/(scale*n^4); it does not replace the real root by a
;; rational root or restrict the source domain.

(defun putnam-1970-b1-product (n remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      1
    (* (+ (* n n)
          (* remaining remaining))
       (putnam-1970-b1-product n (- remaining 1)))))

(defun putnam-1970-b1-scaled-root-search
    (radicand degree scale candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (if (<= (expt candidate degree)
            (* radicand (expt scale degree)))
        candidate
      (putnam-1970-b1-scaled-root-search
       radicand degree scale (- candidate 1)))))

(defun putnam-1970-b1-scaled-root-floor (radicand degree scale)
  (if (and (natp radicand)
           (natp degree)
           (< 0 degree)
           (natp scale)
           (< 0 scale))
      (putnam-1970-b1-scaled-root-search
       radicand
       degree
       scale
       (* 25 (expt degree 4) scale))
    0))

(defun putnam-1970-b1-product-approximant (n scale)
  (if (and (natp n)
           (< 0 n)
           (natp scale)
           (< 0 scale))
      (/ (putnam-1970-b1-scaled-root-floor
          (putnam-1970-b1-product n (* 2 n))
          n
          scale)
         (* scale (expt n 4)))
    0))

;; The following exact rational prefixes independently represent the stated
;; target.  The identity
;;
;;   log 5 = 2*sum_(j>=0) (2/3)^(2j+1)/(2j+1)
;;
;; is the atanh series.  Machin's identity represents pi, and
;; arctan 2 = pi/2 - arctan(1/2).  Substitution into the exponential Taylor
;; series makes the target prefixes converge to
;;
;;   exp(2*log 5 - 4 + 2*arctan 2).

(defun putnam-1970-b1-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (putnam-1970-b1-factorial (- n 1)))))

(defun putnam-1970-b1-atan-prefix (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (sign (if (equal (mod index 2) 0) 1 -1))
           (exponent (+ (* 2 index) 1)))
      (+ (putnam-1970-b1-atan-prefix z index)
         (/ (* sign (expt z exponent))
            exponent)))))

(defun putnam-1970-b1-log-five-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (exponent (+ (* 2 index) 1)))
      (+ (putnam-1970-b1-log-five-prefix index)
         (* 2
            (/ (expt (/ 2 3) exponent)
               exponent))))))

(defun putnam-1970-b1-pi-prefix (terms)
  (- (* 16
        (putnam-1970-b1-atan-prefix (/ 1 5) terms))
     (* 4
        (putnam-1970-b1-atan-prefix (/ 1 239) terms))))

(defun putnam-1970-b1-atan-two-prefix (terms)
  (- (/ (putnam-1970-b1-pi-prefix terms) 2)
     (putnam-1970-b1-atan-prefix (/ 1 2) terms)))

(defun putnam-1970-b1-limit-exponent-prefix (terms)
  (+ (* 2 (putnam-1970-b1-log-five-prefix terms))
     -4
     (* 2 (putnam-1970-b1-atan-two-prefix terms))))

(defun putnam-1970-b1-exp-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- terms 1)))
      (+ (putnam-1970-b1-exp-prefix x index)
         (/ (expt x index)
            (putnam-1970-b1-factorial index))))))

(defun putnam-1970-b1-limit-approximant (terms)
  (putnam-1970-b1-exp-prefix
   (putnam-1970-b1-limit-exponent-prefix terms)
   terms))

;; Positive rational tolerances are cofinal among positive real tolerances.
;; Moreover,
;;
;;   log(P_n^(1/n)/n^4)
;;     = (1/n) * sum_(i=1)^(2n) log(1+(i/n)^2).
;;
;; This is the right Riemann sum for log(1+x^2) on [0,2], whose integral is
;; 2*log 5 - 4 + 2*arctan 2. The predicate below states that source limit
;; exactly through its epsilon definition. SCALE controls
;; only the floor approximation to the positive nth root, while TERMS controls
;; only the rational transcendental prefixes. One existential cutoff for the
;; three independent parameters states convergence without fabricating a
;; numerical rate.
(defun-sk putnam-1970-b1-common-tail-p (epsilon cutoff)
  (forall (n scale terms)
    (implies
     (and (natp n)
          (< 0 n)
          (natp scale)
          (< 0 scale)
          (natp terms)
          (< 0 terms)
          (<= cutoff n)
          (<= cutoff scale)
          (<= cutoff terms))
     (< (abs
         (- (putnam-1970-b1-product-approximant n scale)
            (putnam-1970-b1-limit-approximant terms)))
        epsilon))))

(defun-sk putnam-1970-b1-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and (natp cutoff)
         (< 0 cutoff)
         (putnam-1970-b1-common-tail-p epsilon cutoff))))

(defun putnambench-putnam-1970-b1-statement (epsilon)
  (implies
   (and (rationalp epsilon)
        (< 0 epsilon))
   (putnam-1970-b1-cutoff-exists-p epsilon)))

(value-triple :itpeval-statement-checked)
:q
