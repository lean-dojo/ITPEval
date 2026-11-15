;; Statement-only formalization of PutnamBench corpus artifact putnam_1993_a5:
;; the sum of the three stated definite real integrals of a squared rational
;; function is a rational number. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defun putnam-1993-a5-integrand (x)
  (let* ((numerator (- (* x x) x))
         (denominator (+ (* x x x) (* -3 x) 1))
         (quotient (/ numerator denominator)))
    (* quotient quotient)))

(defun putnam-1993-a5-grid-point
    (left right index subdivisions)
  (+ left
     (/ (* (- right left) index)
        subdivisions)))

(defun putnam-1993-a5-riemann-sum-aux
    (left right subdivisions remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (putnam-1993-a5-integrand
        (putnam-1993-a5-grid-point
         left right remaining subdivisions))
       (putnam-1993-a5-riemann-sum-aux
        left right subdivisions (- remaining 1)))))

(defun putnam-1993-a5-integral-approx
    (left right subdivisions)
  (if (posp subdivisions)
      (* (/ (- right left) subdivisions)
         (putnam-1993-a5-riemann-sum-aux
          left right subdivisions subdivisions))
    0))

;; These are the summed uniform right-endpoint Riemann approximations for
;; exactly the three source intervals. The rational function is continuous on
;; those intervals, so their limit is the source sum of definite integrals.
(defun putnam-1993-a5-three-integral-approx
    (subdivisions)
  (+ (putnam-1993-a5-integral-approx
      -100 -10 subdivisions)
     (putnam-1993-a5-integral-approx
      (/ 1 101) (/ 1 11) subdivisions)
     (putnam-1993-a5-integral-approx
      (/ 101 100) (/ 11 10) subdivisions)))

(defun-sk putnam-1993-a5-limit-tail-p
    (limit epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (posp subdivisions)
      (<= cutoff subdivisions))
     (< (abs
         (- (putnam-1993-a5-three-integral-approx
             subdivisions)
            limit))
        epsilon))))

(defun-sk putnam-1993-a5-limit-cutoff-exists-p
    (limit epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1993-a5-limit-tail-p
      limit epsilon cutoff))))

;; Positive rational tolerances are cofinal among positive real tolerances.
(defun-sk putnam-1993-a5-converges-to-p (limit)
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-1993-a5-limit-cutoff-exists-p
      limit epsilon))))

;; The rational value is existentially quantified inside the proposition.
(defun-sk putnambench-putnam-1993-a5-statement ()
  (exists (limit)
    (and
     (rationalp limit)
     (putnam-1993-a5-converges-to-p limit))))

(value-triple :itpeval-statement-checked)
:q
