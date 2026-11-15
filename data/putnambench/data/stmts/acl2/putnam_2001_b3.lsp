;; Statement-only formalization of PutnamBench corpus artifact putnam_2001_b3:
;; the infinite real series whose nth term uses the nearest integer to sqrt(n)
;; in the exponents of 2 converges to 3. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; For integral n there is no half-integer tie in rounding sqrt(n). The nearest
;; integer k is characterized by k*(k-1) < n <= k*(k+1). The recurrence below
;; computes exactly that k without replacing the square root by an approximation.
(defun putnam-2001-b3-nearest-sqrt (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (let ((previous
           (putnam-2001-b3-nearest-sqrt (- n 1))))
      (if (< (* previous (+ previous 1)) n)
          (+ previous 1)
        previous))))

(defun putnam-2001-b3-term (n)
  (if (posp n)
      (let* ((nearest
              (putnam-2001-b3-nearest-sqrt n))
             (power
              (expt 2 nearest)))
        (/ (+ power (/ 1 power))
           (expt 2 n)))
    0))

;; The exact rational sum of the source terms indexed from 1 through TERMS.
(defun putnam-2001-b3-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (+ (putnam-2001-b3-prefix (- terms 1))
       (putnam-2001-b3-term terms))))

;; Positive rational tolerances are cofinal in the positive reals. Since the
;; source series has rational terms and rational limit 3, quantifying over
;; positive rational tolerances gives exactly its real epsilon convergence.
(defun-sk putnam-2001-b3-tail-p (epsilon cutoff)
  (forall (terms)
    (implies
     (and (natp terms)
          (<= cutoff terms))
     (< (abs (- (putnam-2001-b3-prefix terms) 3))
        epsilon))))

(defun-sk putnam-2001-b3-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and (natp cutoff)
         (putnam-2001-b3-tail-p epsilon cutoff))))

(defun-sk putnambench-putnam-2001-b3-statement ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (putnam-2001-b3-cutoff-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
