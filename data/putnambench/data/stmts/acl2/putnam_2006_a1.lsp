;; Statement-only formalization of PutnamBench corpus artifact putnam_2006_a1:
;; the three-dimensional Lebesgue volume of the real region
;; (x^2+y^2+z^2+8)^2 <= 36(x^2+y^2) is 6*pi^2. This file contains no proof.

(in-package "ACL2")

;; Standard ACL2 has exact rational arithmetic but no primitive completed
;; real field or Lebesgue measure. The midpoint voxel sums below form an exact
;; rational Cauchy name for the source region's volume. The region is contained
;; in [-4,4] x [-4,4] x [-1,1], and every membership test uses the original
;; polynomial inequality, so this is not a restriction to rational points or
;; a finite sampling of the region.
;;
;; The boundary is the torus with major radius 3 and minor radius 1. A voxel
;; misclassified by its midpoint lies in a shrinking tubular neighborhood of
;; that boundary, so these midpoint sums converge to its Lebesgue volume.

(defun putnam-2006-a1-in-region-p (x y z)
  (let* ((radial-square (+ (* x x) (* y y)))
         (left-base (+ radial-square (* z z) 8)))
    (<= (* left-base left-base)
        (* 36 radial-square))))

;; Midpoints for the 8*N equal subintervals of [-4,4].
(defun putnam-2006-a1-xy-coordinate (index subdivisions)
  (if (posp subdivisions)
      (/ (- (+ (* 2 index) 1)
            (* 8 subdivisions))
         (* 2 subdivisions))
    0))

;; Midpoints for the 2*N equal subintervals of [-1,1].
(defun putnam-2006-a1-z-coordinate (index subdivisions)
  (if (posp subdivisions)
      (/ (- (+ (* 2 index) 1)
            (* 2 subdivisions))
         (* 2 subdivisions))
    0))

(defun putnam-2006-a1-x-count
    (remaining y z subdivisions)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let* ((index (- (nfix remaining) 1))
           (x (putnam-2006-a1-xy-coordinate
               index subdivisions)))
      (+ (if (putnam-2006-a1-in-region-p x y z)
             1
           0)
         (putnam-2006-a1-x-count
          index y z subdivisions)))))

(defun putnam-2006-a1-y-count
    (remaining side-count z subdivisions)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let* ((index (- (nfix remaining) 1))
           (y (putnam-2006-a1-xy-coordinate
               index subdivisions)))
      (+ (putnam-2006-a1-x-count
          side-count y z subdivisions)
         (putnam-2006-a1-y-count
          index side-count z subdivisions)))))

(defun putnam-2006-a1-z-count
    (remaining side-count subdivisions)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let* ((index (- (nfix remaining) 1))
           (z (putnam-2006-a1-z-coordinate
               index subdivisions)))
      (+ (putnam-2006-a1-y-count
          side-count side-count z subdivisions)
         (putnam-2006-a1-z-count
          index side-count subdivisions)))))

;; Each voxel has side length 1/N and volume 1/N^3.
(defun putnam-2006-a1-volume-approx (subdivisions)
  (if (posp subdivisions)
      (let ((side-count (* 8 subdivisions))
            (height-count (* 2 subdivisions)))
        (/ (putnam-2006-a1-z-count
            height-count side-count subdivisions)
           (* subdivisions subdivisions subdivisions)))
    0))

;; Rational Leibniz prefixes converge to pi.
(defun putnam-2006-a1-leibniz-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- (nfix terms) 1))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-2006-a1-leibniz-prefix index)
         (/ sign (+ (* 2 index) 1))))))

(defun putnam-2006-a1-pi-prefix (terms)
  (* 4 (putnam-2006-a1-leibniz-prefix terms)))

(defun putnam-2006-a1-solution-approx (terms)
  (let ((pi-approx (putnam-2006-a1-pi-prefix terms)))
    (* 6 pi-approx pi-approx)))

;; Positive rational tolerances are cofinal among positive real tolerances.
;; The source states an equality of limits and supplies no rate, so both
;; approximation cutoffs are existential and every later pair of
;; approximations must remain within the requested tolerance.

(defun-sk putnam-2006-a1-approximation-tail-p
    (epsilon subdivision-cutoff pi-cutoff)
  (forall (subdivisions pi-terms)
    (implies
     (and
      (natp subdivisions)
      (<= subdivision-cutoff subdivisions)
      (natp pi-terms)
      (<= pi-cutoff pi-terms))
     (< (abs
         (- (putnam-2006-a1-volume-approx subdivisions)
            (putnam-2006-a1-solution-approx pi-terms)))
        epsilon))))

(defun-sk putnam-2006-a1-cutoffs-exist-p (epsilon)
  (exists (subdivision-cutoff pi-cutoff)
    (and
     (posp subdivision-cutoff)
     (posp pi-cutoff)
     (putnam-2006-a1-approximation-tail-p
      epsilon subdivision-cutoff pi-cutoff))))

(defun-sk putnambench-putnam-2006-a1-statement ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-2006-a1-cutoffs-exist-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
