;; Statement-only formalization of thousand-theorems corpus artifact Q470877,
;; "Stirling's theorem": the exact real sequence
;; n! / (sqrt(2*n) * (n/exp(1))^n) converges to sqrt(pi), expressed through
;; equivalent rational Cauchy representatives. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; For positive n, divide the Stirling sequence by sqrt(pi) and square:
;;
;;   (n!)^2 * e^(2*n) / (2*pi*n^(2*n+1)).
;;
;; All factors are positive, so convergence of this normalized square to 1 is
;; bidirectionally equivalent to the source sequence converging to sqrt(pi).
;; Ordinary ACL2 has exact rational arithmetic but no primitive irrational
;; reals, so each real value is represented by its full rational Cauchy
;; sequence. The factorial series represents e and Machin's arctangent series
;; represents pi. No finite prefix is treated as the real value.

(defun q470877-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (q470877-factorial (1- n)))))

(defun q470877-exp-one-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (1- terms)))
      (+ (q470877-exp-one-prefix index)
         (/ 1 (q470877-factorial index))))))

(defun q470877-arctan-prefix (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (1- terms))
           (exponent (+ (* 2 index) 1))
           (unsigned (/ (expt z exponent) exponent))
           (term (if (equal (mod index 2) 0)
                     unsigned
                   (- unsigned))))
      (+ (q470877-arctan-prefix z index)
         term))))

(defun q470877-pi-prefix (terms)
  (- (* 16 (q470877-arctan-prefix (/ 1 5) terms))
     (* 4 (q470877-arctan-prefix (/ 1 239) terms))))

(defun q470877-normalized-square-approx (n terms)
  (let* ((fact-n (q470877-factorial n))
         (e-approx (q470877-exp-one-prefix terms))
         (pi-approx (q470877-pi-prefix terms))
         (twice-n (* 2 n)))
    (/ (* fact-n
          fact-n
          (expt e-approx twice-n))
       (* 2
          pi-approx
          (expt n (+ twice-n 1))))))

;; A strict inequality between the represented real ratio and 1 is encoded by
;; an internal rational bound strictly below EPSILON and an approximation
;; cutoff after which every Cauchy representative lies below that bound.

(defun-sk q470877-cauchy-close-tail-p
    (n bound approximation-cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp approximation-cutoff)
      (<= approximation-cutoff terms))
     (< (abs
         (- (q470877-normalized-square-approx n terms)
            1))
        bound))))

(defun-sk q470877-cauchy-real-close-p (n epsilon)
  (exists (bound approximation-cutoff)
    (and
     (rationalp bound)
     (< 0 bound)
     (< bound epsilon)
     (natp approximation-cutoff)
     (q470877-cauchy-close-tail-p
      n bound approximation-cutoff))))

(defun-sk q470877-stirling-tail-p (epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (q470877-cauchy-real-close-p n epsilon))))

(defun-sk q470877-stirling-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q470877-stirling-tail-p epsilon cutoff))))

;; Positive rational epsilon values are cofinal among positive real epsilon
;; values, so this is the full epsilon-N limit statement, not a restriction of
;; the source theorem to rational-valued sequence terms.

(defun-sk thousand-theorems-q470877-stirling-s-theorem-statement ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (q470877-stirling-cutoff-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
