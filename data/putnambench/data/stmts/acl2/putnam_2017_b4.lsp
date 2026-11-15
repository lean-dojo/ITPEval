;; Statement-only formalization of PutnamBench corpus artifact putnam_2017_b4:
;; the natural-logarithm series with coefficients 3,-1,-1,-1 in each block
;; of four consecutive denominators converges to (ln 2)^2. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; For a positive integer M, LOG-PREFIX is the exact rational prefix of
;;
;;   ln M = 2 * sum_(j>=0) ((M-1)/(M+1))^(2j+1)/(2j+1).
;;
;; If DELTA is a positive rational, M*(M+1)*denominator(DELTA) terms give an
;; error below DELTA. Thus LOG-APPROX is a rational regular Cauchy name for
;; the natural logarithm without restricting the source real values to
;; rationals.

(defun putnam-2017-b4-log-prefix (m terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (exponent (+ (* 2 index) 1))
           (ratio (/ (- m 1) (+ m 1))))
      (+ (putnam-2017-b4-log-prefix m index)
         (/ (* 2 (expt ratio exponent))
            exponent)))))

(defun putnam-2017-b4-log-terms (m delta)
  (if (and (natp m)
           (< 0 m)
           (rationalp delta)
           (< 0 delta))
      (* m
         (+ m 1)
         (denominator delta))
    0))

(defun putnam-2017-b4-log-approx (m delta)
  (if (and (natp m)
           (< 0 m)
           (rationalp delta)
           (< 0 delta))
      (putnam-2017-b4-log-prefix
       m
       (putnam-2017-b4-log-terms m delta))
    0))

(defun putnam-2017-b4-summand-approx (k delta)
  (let* ((four-k (* 4 k))
         (m2 (+ four-k 2))
         (m3 (+ four-k 3))
         (m4 (+ four-k 4))
         (m5 (+ four-k 5)))
    (-
     (-
      (-
       (/ (* 3 (putnam-2017-b4-log-approx m2 delta))
          m2)
       (/ (putnam-2017-b4-log-approx m3 delta)
          m3))
      (/ (putnam-2017-b4-log-approx m4 delta)
         m4))
     (/ (putnam-2017-b4-log-approx m5 delta)
        m5))))

(defun putnam-2017-b4-series-prefix-with-delta (terms delta)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- terms 1)))
      (+ (putnam-2017-b4-series-prefix-with-delta
          index delta)
         (putnam-2017-b4-summand-approx
          index delta)))))

;; TERMS is the number of summands, so this is the prefix k=0,...,TERMS-1.
;; Giving every logarithm precision/(16*(TERMS+1)) bounds the total error in
;; the represented real partial sum by a fixed fraction of PRECISION.
(defun putnam-2017-b4-series-approx (terms precision)
  (if (and (natp terms)
           (rationalp precision)
           (< 0 precision))
      (putnam-2017-b4-series-prefix-with-delta
       terms
       (/ precision (* 16 (+ terms 1))))
    0))

(defun putnam-2017-b4-solution-approx (precision)
  (if (and (rationalp precision)
           (< 0 precision))
      (let ((log-two
             (putnam-2017-b4-log-approx
              2
              (/ precision 8))))
        (* log-two log-two))
    0))

;; The remaining predicates express directly
;;
;;   for every positive rational epsilon, every prefix beyond a natural
;;   cutoff is epsilon-close to (ln 2)^2.
;;
;; Positive rational tolerances are cofinal in the positive real tolerances.
;; The controlled errors of the two Cauchy names are fixed fractions of
;; PRECISION. Consequently the following epsilon criterion is equivalent in
;; both directions to convergence of the represented real partial sums. The
;; natural cutoff is existentially quantified inside the statement, and the
;; tail index is universally quantified by DEFUN-SK.

(defun putnam-2017-b4-absolute-value (value)
  (if (< value 0)
      (- value)
    value))

(defun-sk putnam-2017-b4-eventually-close-p (epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (let* ((precision (/ epsilon 8))
            (series-value
             (putnam-2017-b4-series-approx terms precision))
            (solution-value
             (putnam-2017-b4-solution-approx precision)))
       (<
        (putnam-2017-b4-absolute-value
         (- series-value solution-value))
        epsilon)))))

(defun-sk putnam-2017-b4-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2017-b4-eventually-close-p
      epsilon cutoff))))

(defun-sk putnambench-putnam-2017-b4-statement ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (putnam-2017-b4-cutoff-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
