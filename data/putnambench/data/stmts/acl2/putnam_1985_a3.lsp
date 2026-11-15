;; Statement-only formalization of PutnamBench corpus artifact putnam_1985_a3:
;; for every real d, the diagonal of the quadratic recurrence converges to
;; exp(d) - 1. Reals are represented by rational Cauchy names, and exponential
;; by its defining power-series limit. This file contains no proof.

(in-package "ACL2")

;; This unconstrained function is a generic rational Cauchy name for the
;; arbitrary source real d. Its Cauchy and rational-valued requirements are
;; explicit hypotheses of the statement below.
(defstub putnam-1985-a3-d-value (index) t)

(defun-sk putnam-1985-a3-d-values-rational-p ()
  (forall (index)
    (implies
     (natp index)
     (rationalp (putnam-1985-a3-d-value index)))))

(defun-sk putnam-1985-a3-d-cauchy-tail-p
    (epsilon cutoff)
  (forall (left-index right-index)
    (implies
     (and (natp left-index)
          (natp right-index)
          (<= cutoff left-index)
          (<= cutoff right-index))
     (<
      (abs
       (- (putnam-1985-a3-d-value left-index)
          (putnam-1985-a3-d-value right-index)))
      epsilon))))

(defun-sk putnam-1985-a3-d-cauchy-cutoff-exists-p
    (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1985-a3-d-cauchy-tail-p
      epsilon cutoff))))

(defun-sk putnam-1985-a3-d-cauchy-p ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (putnam-1985-a3-d-cauchy-cutoff-exists-p
      epsilon))))

(defun putnam-1985-a3-real-name-p ()
  (and
   (putnam-1985-a3-d-values-rational-p)
   (putnam-1985-a3-d-cauchy-p)))

(defun putnam-1985-a3-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1985-a3-factorial (- n 1)))))

(defun putnam-1985-a3-exp-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((degree (- terms 1)))
      (+ (putnam-1985-a3-exp-prefix x degree)
         (/ (expt x degree)
            (putnam-1985-a3-factorial degree))))))

;; If b_m(j)=a_m(j)+1, the source recurrence becomes
;;
;;   b_m(0)=1+d/2^m,       b_m(j+1)=b_m(j)^2.
;;
;; Thus a_n(n)=(1+d/2^n)^(2^n)-1. Eliminating the source family a by this
;; uniquely determined closed form is a definitional equivalence under its
;; two recurrence hypotheses.
(defun putnam-1985-a3-diagonal-name-value
    (n precision-index)
  (- (expt
      (+ 1
         (/ (putnam-1985-a3-d-value precision-index)
            (expt 2 n)))
      (expt 2 n))
     1))

;; At precision index k, use k+1 exact rational Taylor terms evaluated at the
;; kth rational approximation to d. As k tends to infinity these values
;; converge to the real exp(d)-1; no finite prefix is used as the target.
(defun putnam-1985-a3-solution-name-value
    (precision-index)
  (-
   (putnam-1985-a3-exp-prefix
    (putnam-1985-a3-d-value precision-index)
    (+ 1 (nfix precision-index)))
   1))

;; For fixed n, both rational expressions below converge in PRECISION-INDEX
;; to the represented reals a_n(n) and exp(d)-1. Eventual distance below
;; EPSILON therefore expresses distance at most EPSILON between those reals.
(defun-sk putnam-1985-a3-precision-tail-p
    (n epsilon precision-cutoff)
  (forall (precision-index)
    (implies
     (and (natp precision-index)
          (<= precision-cutoff precision-index))
     (<
      (abs
       (- (putnam-1985-a3-diagonal-name-value
           n precision-index)
          (putnam-1985-a3-solution-name-value
           precision-index)))
      epsilon))))

(defun-sk putnam-1985-a3-precision-cutoff-exists-p
    (n epsilon)
  (exists (precision-cutoff)
    (and
     (natp precision-cutoff)
     (putnam-1985-a3-precision-tail-p
      n epsilon precision-cutoff))))

(defun-sk putnam-1985-a3-limit-tail-p
    (epsilon cutoff)
  (forall (n)
    (implies
     (and (natp n)
          (<= cutoff n))
     (putnam-1985-a3-precision-cutoff-exists-p
      n epsilon))))

(defun-sk putnam-1985-a3-limit-cutoff-exists-p
    (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1985-a3-limit-tail-p
      epsilon cutoff))))

;; Positive rational tolerances are cofinal among positive real tolerances.
;; Quantifying over every such tolerance also supplies the slack that makes
;; the nested Cauchy-name comparison bidirectionally equivalent to the usual
;; real epsilon-N limit.
(defun-sk putnam-1985-a3-diagonal-converges-p ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (putnam-1985-a3-limit-cutoff-exists-p
      epsilon))))

(defun putnambench-putnam-1985-a3-statement ()
  (implies
   (putnam-1985-a3-real-name-p)
   (putnam-1985-a3-diagonal-converges-p)))

(value-triple :itpeval-statement-checked)
:q
