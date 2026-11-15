;; Statement-only formalization of PutnamBench corpus artifact putnam_1965_b1:
;; the varying-dimensional unit-cube integrals of
;; cos^2((pi/(2n))*(x_1+...+x_n)) converge to 1/2.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; For source index N, DIMENSION=N+1 follows the Lean formalization's
;; zero-based indexing.  The exact rational values below are midpoint sums on
;; [0,1]^DIMENSION.  Their mesh is unbounded, while Machin prefixes for pi and
;; Taylor prefixes for cosine converge to the standard real functions.
;; Since the integrand is continuous on each compact cube, the inner limit is
;; exactly the source Lebesgue integral, not a finite quadrature replacement.

(defun putnam-1965-b1-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1965-b1-factorial (- n 1)))))

(defun putnam-1965-b1-arctan-prefix (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (+ (* 2 index) 1))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-1965-b1-arctan-prefix z index)
         (/ (* sign (expt z degree))
            degree)))))

;; Machin's identity: pi = 16*arctan(1/5) - 4*arctan(1/239).
(defun putnam-1965-b1-pi-prefix (terms)
  (- (* 16
        (putnam-1965-b1-arctan-prefix 1/5 terms))
     (* 4
        (putnam-1965-b1-arctan-prefix 1/239 terms))))

(defun putnam-1965-b1-cosine-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (* 2 index))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-1965-b1-cosine-prefix x index)
         (/ (* sign (expt x degree))
            (putnam-1965-b1-factorial degree))))))

;; CELL-INDEX is decoded in base SUBDIVISIONS.  Each digit selects one
;; midpoint coordinate, so this is x_1+...+x_DIMENSION for that grid cell.
(defun putnam-1965-b1-coordinate-sum
    (cell-index dimension subdivisions)
  (declare (xargs :measure (nfix dimension)))
  (if (zp dimension)
      0
    (+ (/ (+ (* 2 (mod cell-index subdivisions)) 1)
          (* 2 subdivisions))
       (putnam-1965-b1-coordinate-sum
        (floor cell-index subdivisions)
        (- dimension 1)
        subdivisions))))

(defun putnam-1965-b1-cell-value
    (cell-index dimension subdivisions series-terms)
  (let* ((coordinate-sum
          (putnam-1965-b1-coordinate-sum
           cell-index dimension subdivisions))
         (angle
          (/ (* (putnam-1965-b1-pi-prefix series-terms)
                coordinate-sum)
             (* 2 dimension)))
         (cosine
          (putnam-1965-b1-cosine-prefix
           angle series-terms)))
    (* cosine cosine)))

(defun putnam-1965-b1-cell-sum
    (remaining dimension subdivisions series-terms)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let ((cell-index (- remaining 1)))
      (+ (putnam-1965-b1-cell-value
          cell-index dimension subdivisions series-terms)
         (putnam-1965-b1-cell-sum
          cell-index dimension subdivisions series-terms)))))

(defun putnam-1965-b1-integral-approx (n precision)
  (if (posp precision)
      (let* ((dimension (+ 1 (nfix n)))
             (subdivisions precision)
             (series-terms precision)
             (cell-count
              (expt subdivisions dimension)))
        (/ (putnam-1965-b1-cell-sum
            cell-count dimension subdivisions series-terms)
           cell-count))
    0))

;; For fixed N, this is the epsilon-tail definition of the inner limit that
;; constructs the corresponding real integral from rational approximants.
(defun-sk putnam-1965-b1-precision-tail-p
    (n epsilon cutoff)
  (forall (precision)
    (implies
     (and (natp precision)
          (<= cutoff precision))
     (< (abs
         (- (putnam-1965-b1-integral-approx
             n precision)
            1/2))
        epsilon))))

(defun-sk putnam-1965-b1-term-within-p (n epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1965-b1-precision-tail-p
      n epsilon cutoff))))

;; Positive rational tolerances are cofinal among positive real tolerances.
;; The existential precision cutoff remains inside the universal sequence
;; index, matching "limit in precision" before "limit as N tends to infinity."
(defun-sk putnam-1965-b1-sequence-tail-p
    (epsilon start)
  (forall (n)
    (implies
     (and (natp n)
          (<= start n))
     (putnam-1965-b1-term-within-p n epsilon))))

(defun-sk putnam-1965-b1-limit-cutoff-exists-p (epsilon)
  (exists (start)
    (and
     (natp start)
     (putnam-1965-b1-sequence-tail-p
      epsilon start))))

(defun-sk putnambench-putnam-1965-b1-statement ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (putnam-1965-b1-limit-cutoff-exists-p
      epsilon))))

(value-triple :itpeval-statement-checked)
:q
