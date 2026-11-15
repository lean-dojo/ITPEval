;; Statement-only formalization of hundred-theorems corpus artifact
;; hundred-theorems__acl2__090, "Stirling's Formula": using exact Cauchy-real
;; representatives by rational sequences, the squared positive normalized
;; factorial ratio tends to 1 with an existential epsilon-N cutoff.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Ordinary ACL2 has exact rational arithmetic but no primitive real numbers.
;; Here a real is represented exactly by a rational Cauchy sequence.  The
;; factorial series represents e, Machin's arctangent series represents pi,
;; and, for each n, HT090-STIRLING-SQUARED-RATIO-APPROX is the full Cauchy
;; representative of
;;
;;   (n!)^2 * e^(2*n) / (2*pi*n^(2*n+1)).
;;
;; No n-dependent finite prefix is treated as the real value.  Strict
;; Cauchy-real inequalities below contain an internal rational bound and an
;; existential approximation cutoff.

(defun ht090-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (ht090-factorial (1- n)))))

(defun ht090-exp-one-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (1- terms)))
      (+ (ht090-exp-one-prefix index)
         (/ 1 (ht090-factorial index))))))

(defun ht090-arctan-prefix (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (1- terms))
           (exponent (+ (* 2 index) 1))
           (unsigned (/ (expt z exponent) exponent))
           (term (if (equal (mod index 2) 0)
                     unsigned
                   (- unsigned))))
      (+ (ht090-arctan-prefix z index)
         term))))

(defun ht090-pi-prefix (terms)
  (- (* 16 (ht090-arctan-prefix (/ 1 5) terms))
     (* 4 (ht090-arctan-prefix (/ 1 239) terms))))

(defun ht090-stirling-squared-ratio-approx (n terms)
  (let* ((fact-n (ht090-factorial n))
         (e-approx (ht090-exp-one-prefix terms))
         (pi-approx (ht090-pi-prefix terms))
         (twice-n (* 2 n)))
    (/ (* fact-n
          fact-n
          (expt e-approx twice-n))
       (* 2
          pi-approx
          (expt n (+ twice-n 1))))))

;; Eventually every rational approximation lies below BOUND.  Together with
;; 0 < BOUND < EPSILON, this is exactly the strict Cauchy-real inequality
;; |ratio(n) - 1| < EPSILON, including the boundary distinction.
(defun-sk ht090-cauchy-close-tail-p
    (n bound approximation-cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp approximation-cutoff)
      (<= approximation-cutoff terms))
     (< (abs
         (- (ht090-stirling-squared-ratio-approx n terms)
            1))
        bound))))

(defun-sk ht090-cauchy-real-close-p (n epsilon)
  (exists (bound approximation-cutoff)
    (and
     (rationalp bound)
     (< 0 bound)
     (< bound epsilon)
     (natp approximation-cutoff)
     (ht090-cauchy-close-tail-p
      n bound approximation-cutoff))))

(defun-sk ht090-stirling-tail-p (epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (ht090-cauchy-real-close-p n epsilon))))

(defun-sk ht090-stirling-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht090-stirling-tail-p epsilon cutoff))))

(defun-sk hundred-theorems-090-stirling-formula-statement ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (ht090-stirling-cutoff-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
