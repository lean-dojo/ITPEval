;; Statement-only formalization of PutnamBench corpus artifact putnam_2000_a4:
;; convergence of the improper real integral of sin(x)*sin(x^2) from zero
;; to an upper endpoint tending to positive infinity. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; For rational UPPER >= 0 and positive integer STAGE, the value below is a
;; rational midpoint sum on [0,UPPER]. Both sine factors are evaluated by
;; Maclaurin prefixes whose length tends to infinity with STAGE. For each
;; fixed rational UPPER these values converge to
;;
;;   integral_0^UPPER sin(x)*sin(x^2) dx.
;;
;; Thus this is a Cauchy name for the source finite real integral, not a fixed
;; quadrature or a rational-valued replacement for it.

(defun putnam-2000-a4-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-2000-a4-factorial (- n 1)))))

(defun putnam-2000-a4-sine-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (+ (* 2 index) 1))
           (sign (if (equal (mod index 2) 0)
                     1
                   -1)))
      (+ (putnam-2000-a4-sine-prefix x index)
         (/ (* sign (expt x degree))
            (putnam-2000-a4-factorial degree))))))

(defun putnam-2000-a4-midpoint
    (index upper subdivisions)
  (* upper
     (/ (+ (* 2 index) 1)
        (* 2 subdivisions))))

(defun putnam-2000-a4-midpoint-sum
    (remaining upper subdivisions terms)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let* ((index (- remaining 1))
           (x (putnam-2000-a4-midpoint
               index upper subdivisions))
           (sine-x
            (putnam-2000-a4-sine-prefix x terms))
           (sine-x-squared
            (putnam-2000-a4-sine-prefix
             (* x x) terms)))
      (+ (* sine-x sine-x-squared)
         (putnam-2000-a4-midpoint-sum
          index upper subdivisions terms)))))

(defun putnam-2000-a4-integral-approx (upper stage)
  (if (and (rationalp upper)
           (<= 0 upper)
           (posp stage))
      (* (/ upper stage)
         (putnam-2000-a4-midpoint-sum
          stage upper stage stage))
    0))

;; The source limit exists exactly when its finite-integral values satisfy the
;; Cauchy criterion at positive infinity. Nonnegative rational endpoints are
;; enough: they are cofinal and dense in the reals, and the finite-integral
;; function is continuous in its endpoint. Completeness of the reals then
;; recovers the source's internal existential limit.
;;
;; The source asserts convergence, not a particular quantitative rate.
;; Therefore every tail and approximation modulus below is existential. The
;; quantifier order is the Cauchy criterion for the endpoint-indexed finite
;; integrals, with each finite integral itself represented by its convergent
;; midpoint/Maclaurin approximation sequence.

(defun-sk putnam-2000-a4-stage-tail-p
    (epsilon left-upper right-upper
             left-cutoff right-cutoff)
  (forall (left-stage right-stage)
    (implies
     (and
      (natp left-stage)
      (<= left-cutoff left-stage)
      (natp right-stage)
      (<= right-cutoff right-stage))
     (< (abs
         (- (putnam-2000-a4-integral-approx
             left-upper left-stage)
            (putnam-2000-a4-integral-approx
             right-upper right-stage)))
        epsilon))))

(defun-sk putnam-2000-a4-stage-cutoffs-exist-p
    (epsilon left-upper right-upper)
  (exists (left-cutoff right-cutoff)
    (and
     (posp left-cutoff)
     (posp right-cutoff)
     (putnam-2000-a4-stage-tail-p
      epsilon left-upper right-upper
      left-cutoff right-cutoff))))

(defun-sk putnam-2000-a4-endpoint-tail-p
    (epsilon endpoint-cutoff)
  (forall (left-upper right-upper)
    (implies
     (and
      (rationalp left-upper)
      (<= endpoint-cutoff left-upper)
      (rationalp right-upper)
      (<= endpoint-cutoff right-upper))
     (putnam-2000-a4-stage-cutoffs-exist-p
      epsilon left-upper right-upper))))

(defun-sk putnam-2000-a4-endpoint-cutoff-exists-p
    (epsilon)
  (exists (endpoint-cutoff)
    (and
     (rationalp endpoint-cutoff)
     (<= 0 endpoint-cutoff)
     (putnam-2000-a4-endpoint-tail-p
      epsilon endpoint-cutoff))))

(defun-sk putnambench-putnam-2000-a4-statement ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-2000-a4-endpoint-cutoff-exists-p
      epsilon))))

(value-triple :itpeval-statement-checked)
:q
