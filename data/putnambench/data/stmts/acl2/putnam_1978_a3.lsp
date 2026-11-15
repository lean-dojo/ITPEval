;; Statement-only formalization of PutnamBench corpus artifact putnam_1978_a3:
;; the least of four improper real integrals of x^k divided by a fixed
;; reciprocal polynomial occurs at k = 2. This file contains no proof.

(in-package "ACL2")

;; Under x = t/(1-t), the source integral on [0,infinity) becomes the
;; integral on [0,1] of
;;
;;   t^k (1-t)^(4-k) / Q(t),
;;
;; where Q is the degree-six homogenization of the source polynomial.
;; This transformed integrand extends continuously to both endpoints.
(defun putnam-1978-a3-denominator (point)
  (let ((u (- 1 point)))
    (+ (* 2
          (+ (expt point 6)
             (expt u 6)))
       (* 4
          (+ (* (expt point 5) u)
             (* point (expt u 5))))
       (* 3
          (+ (* (expt point 4) (expt u 2))
             (* (expt point 2) (expt u 4))))
       (* 5
          (expt point 3)
          (expt u 3)))))

(defun putnam-1978-a3-valid-k-p (k)
  (and (natp k)
       (<= 1 k)
       (<= k 4)))

(defun putnam-1978-a3-transformed-integrand (k point)
  (if (and (putnam-1978-a3-valid-k-p k)
           (rationalp point)
           (<= 0 point)
           (<= point 1))
      (/ (* (expt point k)
            (expt (- 1 point) (- 4 k)))
         (putnam-1978-a3-denominator point))
    0))

(defun putnam-1978-a3-riemann-sum-aux
    (k index subdivisions)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      0
    (+ (putnam-1978-a3-transformed-integrand
        k (/ index subdivisions))
       (putnam-1978-a3-riemann-sum-aux
        k (- index 1) subdivisions))))

(defun putnam-1978-a3-riemann-sum (k subdivisions)
  (if (and (putnam-1978-a3-valid-k-p k)
           (natp subdivisions)
           (< 0 subdivisions))
      (/ (putnam-1978-a3-riemann-sum-aux
          k subdivisions subdivisions)
         subdivisions)
    0))

;; Positive rationals are cofinal among positive real tolerances. The
;; eventual comparison of every pair of sufficiently fine Riemann sums is
;; equivalent to the comparison of their exact real limits.
(defun-sk putnam-1978-a3-comparison-tail-p
    (k epsilon cutoff)
  (forall (subdivisions-2 subdivisions-k)
    (implies
     (and
      (natp subdivisions-2)
      (< 0 subdivisions-2)
      (<= cutoff subdivisions-2)
      (natp subdivisions-k)
      (< 0 subdivisions-k)
      (<= cutoff subdivisions-k))
     (<= (putnam-1978-a3-riemann-sum
          2 subdivisions-2)
         (+ (putnam-1978-a3-riemann-sum
             k subdivisions-k)
            epsilon)))))

(defun-sk putnam-1978-a3-comparison-cutoff-exists-p
    (k epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (< 0 cutoff)
     (putnam-1978-a3-comparison-tail-p
      k epsilon cutoff))))

(defun putnambench-putnam-1978-a3-statement (k epsilon)
  (implies
   (and
    (putnam-1978-a3-valid-k-p k)
    (rationalp epsilon)
    (< 0 epsilon))
   (and
    (putnam-1978-a3-valid-k-p 2)
    (putnam-1978-a3-comparison-cutoff-exists-p
     k epsilon))))

(value-triple :itpeval-statement-checked)
:q
