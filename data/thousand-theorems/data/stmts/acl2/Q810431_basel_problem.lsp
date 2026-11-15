;; Statement-only formalization of thousand-theorems corpus artifact Q810431,
;; "Basel problem": the real series with n-th term 1 / n^2, whose zero-index
;; term is zero under real-field division, has sum pi^2 / 6. Exact rational
;; partial sums and a full Cauchy representative of pi encode the real limit.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Machin's arctangent series is an exact rational Cauchy representative of
;; pi. No finite prefix is identified with pi.

(defun q810431-arctan-prefix (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (1- terms))
           (exponent (+ (* 2 index) 1))
           (unsigned-term (/ (expt z exponent) exponent))
           (term (if (equal (mod index 2) 0)
                     unsigned-term
                   (- unsigned-term))))
      (+ (q810431-arctan-prefix z index)
         term))))

(defun q810431-pi-prefix (terms)
  (- (* 16 (q810431-arctan-prefix (/ 1 5) terms))
     (* 4 (q810431-arctan-prefix (/ 1 239) terms))))

;; This is the sum over indices 0 through TERMS - 1. ACL2 division, like real
;; field division in the source, gives 1 / 0 = 0, so the zero-index term is
;; represented exactly rather than deleted.

(defun q810431-reciprocal-square-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (1- terms)))
      (+ (q810431-reciprocal-square-prefix index)
         (/ 1 (* index index))))))

(defun q810431-basel-limit-prefix (pi-terms)
  (/ (expt (q810431-pi-prefix pi-terms) 2)
     6))

;; A strict inequality to the represented real limit is encoded using an
;; internal rational bound below EPSILON and tails of both the source partial
;; sums and the Cauchy representative of pi^2 / 6.

(defun-sk q810431-close-tail-p
    (bound series-cutoff pi-cutoff)
  (forall (terms pi-terms)
    (implies
     (and
      (natp terms)
      (natp pi-terms)
      (natp series-cutoff)
      (natp pi-cutoff)
      (<= series-cutoff terms)
      (<= pi-cutoff pi-terms))
     (< (abs
         (- (q810431-reciprocal-square-prefix terms)
            (q810431-basel-limit-prefix pi-terms)))
        bound))))

(defun-sk q810431-cutoffs-exist-p (epsilon)
  (exists (bound series-cutoff pi-cutoff)
    (and
     (rationalp bound)
     (< 0 bound)
     (< bound epsilon)
     (natp series-cutoff)
     (natp pi-cutoff)
     (q810431-close-tail-p
      bound series-cutoff pi-cutoff))))

;; Positive rational tolerances are cofinal among positive real tolerances.
;; Thus this is the full epsilon-N HasSum statement over the reals, with all
;; approximation and convergence witnesses quantified internally.

(defun-sk thousand-theorems-q810431-basel-problem-statement ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (q810431-cutoffs-exist-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
