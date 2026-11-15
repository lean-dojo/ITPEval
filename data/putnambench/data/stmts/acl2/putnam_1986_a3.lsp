;; Statement-only formalization of PutnamBench corpus artifact putnam_1986_a3:
;; evaluation of the infinite real series of arccot(n^2+n+1) as pi/2. This
;; file contains no proof.

(in-package "ACL2")

;; For 0 <= X <= 1, these exact rational alternating-series prefixes converge
;; to the real arctangent of X.
(defun putnam-1986-a3-arctan-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (exponent (+ (* 2 index) 1))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-1986-a3-arctan-prefix x index)
         (/ (* sign (expt x exponent))
            exponent)))))

;; The source argument n^2+n+1 is at least one. On the required interval
;; (0,pi/2], its arccotangent is arctan(1/(n^2+n+1)). Thus this is an exact
;; rational prefix for the corresponding source summand.
(defun putnam-1986-a3-summand-prefix (n arctan-terms)
  (putnam-1986-a3-arctan-prefix
   (/ 1 (+ (* n n) n 1))
   arctan-terms))

;; Exact rational approximation to the source partial sum over
;; n=0,...,SUM-TERMS-1.
(defun putnam-1986-a3-series-prefix
    (sum-terms arctan-terms)
  (declare (xargs :measure (nfix sum-terms)))
  (if (zp sum-terms)
      0
    (let ((n (- sum-terms 1)))
      (+ (putnam-1986-a3-series-prefix
          n arctan-terms)
         (putnam-1986-a3-summand-prefix
          n arctan-terms)))))

;; Machin's identity gives
;;   pi/2 = 8*arctan(1/5) - 2*arctan(1/239).
;; Hence these exact rational values form an independent Cauchy name for the
;; source solution pi/2.
(defun putnam-1986-a3-pi-half-prefix (terms)
  (- (* 8
        (putnam-1986-a3-arctan-prefix (/ 1 5) terms))
     (* 2
        (putnam-1986-a3-arctan-prefix (/ 1 239) terms))))

;; On (0,pi/2], cot is injective and cot(theta)=t is equivalent to
;; tan(theta)=1/t for t>0. Thus the canonical arctangent Cauchy name above
;; eliminates the source's uniquely characterized arccot without choosing an
;; additional function. Positive rational tolerances are cofinal among
;; positive real tolerances.
;;
;; The precision needed for the finitely many arctangent summands may depend
;; on the outer partial-sum index. All cutoffs are existential, so the
;; statement asserts only equality of the two limits and no particular rate.
(defun-sk putnam-1986-a3-precision-tail-p
    (epsilon sum-terms precision-cutoff)
  (forall (arctan-terms pi-terms)
    (implies
     (and
      (natp arctan-terms)
      (<= precision-cutoff arctan-terms)
      (natp pi-terms)
      (<= precision-cutoff pi-terms))
     (<
      (abs
       (- (putnam-1986-a3-series-prefix
           sum-terms arctan-terms)
          (putnam-1986-a3-pi-half-prefix pi-terms)))
      epsilon))))

(defun-sk putnam-1986-a3-precision-cutoff-exists-p
    (epsilon sum-terms)
  (exists (precision-cutoff)
    (and
     (posp precision-cutoff)
     (putnam-1986-a3-precision-tail-p
      epsilon sum-terms precision-cutoff))))

(defun-sk putnam-1986-a3-series-tail-p
    (epsilon sum-cutoff)
  (forall (sum-terms)
    (implies
     (and
      (natp sum-terms)
      (<= sum-cutoff sum-terms))
     (putnam-1986-a3-precision-cutoff-exists-p
      epsilon sum-terms))))

(defun-sk putnam-1986-a3-sum-cutoff-exists-p (epsilon)
  (exists (sum-cutoff)
    (and
     (posp sum-cutoff)
     (putnam-1986-a3-series-tail-p
      epsilon sum-cutoff))))

(defun-sk putnambench-putnam-1986-a3-statement ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-1986-a3-sum-cutoff-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
