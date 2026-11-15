;; Statement-only formalization of PutnamBench corpus artifact putnam_1969_a4:
;; the real integral of x^x on (0,1) equals the alternating infinite series
;; with nth term (-1)^(n+1)/n^n. This file contains no proof.

(in-package "ACL2")

(defun putnam-1969-a4-series-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((sign (if (equal (mod terms 2) 1) 1 -1)))
      (+ (putnam-1969-a4-series-prefix (- terms 1))
         (/ sign (expt terms terms))))))

;; For 1 <= INDEX <= SUBDIVISIONS, (INDEX/SUBDIVISIONS)^
;; (INDEX/SUBDIVISIONS) is the unique number in [0,1] whose SUBDIVISIONS-th
;; power is (INDEX/SUBDIVISIONS)^INDEX. Bisection therefore gives rational
;; lower approximations to the exact real integrand values.
(defun putnam-1969-a4-root-lower
    (radicand degree steps lower upper)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      lower
    (let ((midpoint (/ (+ lower upper) 2)))
      (if (<= (expt midpoint degree) radicand)
          (putnam-1969-a4-root-lower
           radicand degree (- steps 1) midpoint upper)
        (putnam-1969-a4-root-lower
         radicand degree (- steps 1) lower midpoint)))))

(defun putnam-1969-a4-grid-value
    (index subdivisions root-steps)
  (putnam-1969-a4-root-lower
   (expt (/ index subdivisions) index)
   subdivisions
   root-steps
   0
   1))

(defun putnam-1969-a4-riemann-sum-aux
    (index subdivisions root-steps)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      0
    (+ (putnam-1969-a4-grid-value
        index subdivisions root-steps)
       (putnam-1969-a4-riemann-sum-aux
        (- index 1) subdivisions root-steps))))

(defun putnam-1969-a4-riemann-sum
    (subdivisions root-steps)
  (if (and (natp subdivisions)
           (< 0 subdivisions)
           (natp root-steps))
      (/ (putnam-1969-a4-riemann-sum-aux
          subdivisions subdivisions root-steps)
         subdivisions)
    0))

;; The exact source equality is stated through its epsilon definition. The
;; first precision parameter truncates the alternating series, the second is
;; the right-Riemann mesh, and the third controls the exact-root bisections.
;; Requiring one existential cutoff for all three independent tails says that
;; the series prefixes and Riemann approximants have the same real limit. It
;; deliberately asserts no particular convergence rate.
(defun-sk putnam-1969-a4-common-tail-p (epsilon cutoff)
  (forall (terms subdivisions root-steps)
    (implies
     (and (natp terms)
          (natp subdivisions)
          (< 0 subdivisions)
          (natp root-steps)
          (<= cutoff terms)
          (<= cutoff subdivisions)
          (<= cutoff root-steps))
     (< (abs
         (- (putnam-1969-a4-series-prefix terms)
            (putnam-1969-a4-riemann-sum
             subdivisions root-steps)))
        epsilon))))

(defun-sk putnam-1969-a4-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and (natp cutoff)
         (< 0 cutoff)
         (putnam-1969-a4-common-tail-p epsilon cutoff))))

(defun putnambench-putnam-1969-a4-statement (epsilon)
  (implies
   (and (rationalp epsilon)
        (< 0 epsilon))
   (putnam-1969-a4-cutoff-exists-p epsilon)))

(value-triple :itpeval-statement-checked)
:q
