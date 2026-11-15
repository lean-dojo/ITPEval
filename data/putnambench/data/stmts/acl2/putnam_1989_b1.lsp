;; Statement-only formalization of PutnamBench corpus artifact putnam_1989_b1:
;; the unit-square area probability of points nearer the center than every
;; edge is (4*sqrt(2)-5)/3. This file contains no proof.

(in-package "ACL2")

;; For an N by N midpoint grid, X and Y are the centered coordinates scaled
;; by 2*N. The four strict inequalities say that the squared distance to the
;; center is smaller than the squared distance to each edge. Since the nearest
;; point on an edge is its perpendicular projection, this is exactly the
;; source predicate "nearer to the center than to any edge."
(defun putnam-1989-b1-grid-point-closer-p (row column subdivisions)
  (and
   (posp subdivisions)
   (natp row)
   (< row subdivisions)
   (natp column)
   (< column subdivisions)
   (let* ((x (- (+ (* 2 column) 1) subdivisions))
          (y (- (+ (* 2 row) 1) subdivisions))
          (radius-squared (+ (* x x) (* y y)))
          (left-distance (+ subdivisions x))
          (right-distance (- subdivisions x))
          (bottom-distance (+ subdivisions y))
          (top-distance (- subdivisions y)))
     (and
      (< radius-squared (* left-distance left-distance))
      (< radius-squared (* right-distance right-distance))
      (< radius-squared (* bottom-distance bottom-distance))
      (< radius-squared (* top-distance top-distance))))))

(defun putnam-1989-b1-row-count
    (row remaining-columns subdivisions)
  (declare (xargs :measure (nfix remaining-columns)))
  (if (zp remaining-columns)
      0
    (+ (if (putnam-1989-b1-grid-point-closer-p
            row (- remaining-columns 1) subdivisions)
           1
         0)
       (putnam-1989-b1-row-count
        row (- remaining-columns 1) subdivisions))))

(defun putnam-1989-b1-grid-count
    (remaining-rows subdivisions)
  (declare (xargs :measure (nfix remaining-rows)))
  (if (zp remaining-rows)
      0
    (+ (putnam-1989-b1-row-count
        (- remaining-rows 1) subdivisions subdivisions)
       (putnam-1989-b1-grid-count
        (- remaining-rows 1) subdivisions))))

;; This exact rational midpoint sum converges to the Lebesgue area of the
;; semialgebraic closer-point subset. Its boundary is contained in finitely
;; many algebraic curves and therefore has planar measure zero.
(defun putnam-1989-b1-area-approx (subdivisions)
  (if (posp subdivisions)
      (/ (putnam-1989-b1-grid-count
          subdivisions subdivisions)
         (* subdivisions subdivisions))
    0))

(defun putnam-1989-b1-isqrt-down (number candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (if (<= (* candidate candidate) number)
        candidate
      (putnam-1989-b1-isqrt-down
       number (- candidate 1)))))

(defun putnam-1989-b1-isqrt (number)
  (let ((number (nfix number)))
    (putnam-1989-b1-isqrt-down number number)))

;; floor(sqrt(2*N^2))/N is an exact rational lower approximation to sqrt(2)
;; with error less than 1/N.
(defun putnam-1989-b1-sqrt-two-approx (subdivisions)
  (if (posp subdivisions)
      (/ (putnam-1989-b1-isqrt
          (* 2 subdivisions subdivisions))
         subdivisions)
    0))

(defun putnam-1989-b1-solution-approx (subdivisions)
  (/ (- (* 4
           (putnam-1989-b1-sqrt-two-approx subdivisions))
        5)
     3))

(defun putnam-1989-b1-error (subdivisions)
  (abs
   (- (putnam-1989-b1-area-approx subdivisions)
      (putnam-1989-b1-solution-approx subdivisions))))

(defun-sk putnam-1989-b1-limit-tail-p (epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (natp subdivisions)
      (<= cutoff subdivisions))
     (< (putnam-1989-b1-error subdivisions)
        epsilon))))

(defun-sk putnam-1989-b1-limit-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1989-b1-limit-tail-p epsilon cutoff))))

;; Positive rational tolerances are cofinal among positive real tolerances.
;; Thus equality of these two rational limits is bidirectionally equivalent
;; to the source equality between the Lebesgue-area ratio and
;; (4*sqrt(2)-5)/3. The square has area one, so the ratio is this area.
(defun-sk putnam-1989-b1-area-identity-p ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-1989-b1-limit-cutoff-exists-p epsilon))))

(defun-sk putnam-1989-b1-two-is-nonsquare-p ()
  (forall (n)
    (implies
     (integerp n)
     (not (equal (* n n) 2)))))

(defun putnambench-putnam-1989-b1-statement ()
  (and
   (< 0 2)
   (< 0 3)
   (putnam-1989-b1-two-is-nonsquare-p)
   (putnam-1989-b1-area-identity-p)))

(value-triple :itpeval-statement-checked)
:q
