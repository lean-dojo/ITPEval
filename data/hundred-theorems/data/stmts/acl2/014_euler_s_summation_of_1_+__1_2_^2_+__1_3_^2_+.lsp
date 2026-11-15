;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__014, "Euler's Summation of 1 + (1/2)^2 +
;; (1/3)^2 + ...": the positive-integer reciprocal-square series converges
;; over the reals to pi^2 / 6. Exact rational partial sums and Leibniz
;; approximants to pi give a Cauchy-sequence formulation in the rational
;; completion. This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-014-reciprocal-square-prefix (terms)
  (if (zp terms)
      0
    (+ (hundred-theorems-014-reciprocal-square-prefix (- terms 1))
       (/ 1 (* terms terms)))))

(defun hundred-theorems-014-leibniz-pi-prefix (terms)
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (numerator (if (equal (mod index 2) 0) 4 -4))
           (denominator (+ (* 2 index) 1)))
      (+ (hundred-theorems-014-leibniz-pi-prefix index)
         (/ numerator denominator)))))

;; Beyond the two cutoffs, every reciprocal-square prefix is epsilon-close
;; to the square of every Leibniz approximation to pi, divided by six.
(defun-sk hundred-theorems-014-tail-p
    (epsilon series-cutoff pi-cutoff)
  (forall (terms pi-terms)
    (implies
     (and
      (natp terms)
      (<= series-cutoff terms)
      (natp pi-terms)
      (<= pi-cutoff pi-terms))
     (<
      (abs
       (- (hundred-theorems-014-reciprocal-square-prefix terms)
          (/ (expt
              (hundred-theorems-014-leibniz-pi-prefix pi-terms)
              2)
             6)))
      epsilon))))

(defun-sk hundred-theorems-014-cutoffs-exist-p (epsilon)
  (exists (series-cutoff pi-cutoff)
    (and
     (natp series-cutoff)
     (natp pi-cutoff)
     (hundred-theorems-014-tail-p
      epsilon series-cutoff pi-cutoff))))

(defun-sk hundred-theorems-014-euler-summation-statement ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (hundred-theorems-014-cutoffs-exist-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
