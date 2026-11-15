;; Statement-only formalization of PutnamBench corpus artifact putnam_1984_a5:
;; the real triple integral of x*y^9*z^8*(1-x-y-z)^4 over the nonnegative
;; unit simplex equals 1!*9!*8!*4!/25!. This file contains no proof.

(in-package "ACL2")

(defun putnam-1984-a5-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (putnam-1984-a5-factorial (- n 1)))))

(defun putnam-1984-a5-solution ()
  (list 1 9 8 4 25))

(defun putnam-1984-a5-solution-value ()
  (let* ((solution (putnam-1984-a5-solution))
         (a (nth 0 solution))
         (b (nth 1 solution))
         (c (nth 2 solution))
         (d (nth 3 solution))
         (n (nth 4 solution)))
    (/ (* (putnam-1984-a5-factorial a)
          (putnam-1984-a5-factorial b)
          (putnam-1984-a5-factorial c)
          (putnam-1984-a5-factorial d))
       (putnam-1984-a5-factorial n))))

;; Extend the source integrand by zero from the simplex to the unit cube.
;; The arguments are grid indices, so every sampled value is exact rational
;; arithmetic even though the limit denotes the source's real integral.
(defun putnam-1984-a5-grid-integrand
    (x-index y-index z-index subdivisions)
  (if (posp subdivisions)
      (let* ((x (/ x-index subdivisions))
             (y (/ y-index subdivisions))
             (z (/ z-index subdivisions))
             (w (- 1 (+ x y z))))
        (if (<= 0 w)
            (* x
               (expt y 9)
               (expt z 8)
               (expt w 4))
          0))
    0))

(defun putnam-1984-a5-z-sum
    (x-index y-index remaining-z subdivisions)
  (declare (xargs :measure (nfix remaining-z)))
  (if (zp remaining-z)
      0
    (+ (putnam-1984-a5-grid-integrand
        x-index y-index remaining-z subdivisions)
       (putnam-1984-a5-z-sum
        x-index y-index (- remaining-z 1) subdivisions))))

(defun putnam-1984-a5-yz-sum
    (x-index remaining-y subdivisions)
  (declare (xargs :measure (nfix remaining-y)))
  (if (zp remaining-y)
      0
    (+ (putnam-1984-a5-z-sum
        x-index remaining-y subdivisions subdivisions)
       (putnam-1984-a5-yz-sum
        x-index (- remaining-y 1) subdivisions))))

(defun putnam-1984-a5-xyz-sum
    (remaining-x subdivisions)
  (declare (xargs :measure (nfix remaining-x)))
  (if (zp remaining-x)
      0
    (+ (putnam-1984-a5-yz-sum
        remaining-x subdivisions subdivisions)
       (putnam-1984-a5-xyz-sum
        (- remaining-x 1) subdivisions))))

(defun putnam-1984-a5-riemann-sum (subdivisions)
  (if (posp subdivisions)
      (/ (putnam-1984-a5-xyz-sum
          subdivisions subdivisions)
         (expt subdivisions 3))
    0))

;; Positive rational tolerances are cofinal among positive real tolerances.
;; Thus convergence of these exact rational grid sums states the real
;; Lebesgue (equivalently Riemann) integral equality without adding a rate.
(defun-sk putnam-1984-a5-tail-p (epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (natp subdivisions)
      (<= cutoff subdivisions))
     (< (abs
         (- (putnam-1984-a5-riemann-sum subdivisions)
            (putnam-1984-a5-solution-value)))
        epsilon))))

(defun-sk putnam-1984-a5-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (< 0 cutoff)
     (putnam-1984-a5-tail-p epsilon cutoff))))

(defun putnambench-putnam-1984-a5-statement (epsilon)
  (implies
   (and (rationalp epsilon)
        (< 0 epsilon))
   (let* ((solution (putnam-1984-a5-solution))
          (a (nth 0 solution))
          (b (nth 1 solution))
          (c (nth 2 solution))
          (d (nth 3 solution))
          (n (nth 4 solution)))
     (and (< 0 a)
          (< 0 b)
          (< 0 c)
          (< 0 d)
          (< 0 n)
          (putnam-1984-a5-cutoff-exists-p epsilon)))))

(value-triple :itpeval-statement-checked)
:q
