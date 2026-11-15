;; Statement-only formalization of PutnamBench corpus artifact putnam_1976_b1:
;; the real limit of a normalized sum of differences of integer floors,
;; evaluated as log 4 minus 1. This file contains no proof.

(in-package "ACL2")

(defun putnam-1976-b1-solution-a ()
  4)

(defun putnam-1976-b1-solution-b ()
  1)

;; This is the source sum
;;
;;   sum_(k=1)^n (floor(2n/k) - 2 floor(n/k)).
(defun putnam-1976-b1-floor-sum (n k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      0
    (+ (- (floor (* 2 n) k)
          (* 2 (floor n k)))
       (putnam-1976-b1-floor-sum n (- k 1)))))

(defun putnam-1976-b1-sequence-value (n)
  (if (and (natp n)
           (< 0 n))
      (/ (putnam-1976-b1-floor-sum n n) n)
    0))

;; The positive rational series
;;
;;   sum_(q=1)^infinity 1 / ((2q+1)(q+1))
;;
;; telescopes in harmonic-number prefixes to 2 log 2 - 1, hence represents
;; exactly log(4) - 1 rather than a rational replacement for that real.
(defun putnam-1976-b1-limit-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (+ (putnam-1976-b1-limit-prefix (- terms 1))
       (/ 1
          (* (+ (* 2 terms) 1)
             (+ terms 1))))))

;; Standard ACL2 represents the irrational target by its canonical rational
;; Cauchy sequence. The two independent tail indices say exactly that the
;; source sequence converges to the real represented by the series above;
;; no particular modulus of convergence is added to the source statement.
(defun-sk putnam-1976-b1-common-tail-p
    (epsilon sequence-cutoff series-cutoff)
  (forall (n terms)
    (implies
     (and
      (natp n)
      (<= sequence-cutoff n)
      (natp terms)
      (<= series-cutoff terms))
     (<
      (abs
       (- (putnam-1976-b1-sequence-value n)
          (putnam-1976-b1-limit-prefix terms)))
      epsilon))))

(defun-sk putnam-1976-b1-cutoffs-exist-p (epsilon)
  (exists (sequence-cutoff series-cutoff)
    (and
     (natp sequence-cutoff)
     (natp series-cutoff)
     (putnam-1976-b1-common-tail-p
      epsilon sequence-cutoff series-cutoff))))

(defun-sk putnam-1976-b1-converges-p ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-1976-b1-cutoffs-exist-p epsilon))))

(defun putnambench-putnam-1976-b1-statement ()
  (and
   (< 0 (putnam-1976-b1-solution-a))
   (< 0 (putnam-1976-b1-solution-b))
   (putnam-1976-b1-converges-p)))

(value-triple :itpeval-statement-checked)
:q
