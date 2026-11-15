;; Statement-only formalization of PutnamBench corpus artifact putnam_2019_b2:
;; the normalized trigonometric sums with angles (2k-1)pi/(2n) converge
;; to 8/pi^3. This file contains no proof.

(in-package "ACL2")

; All real quantities below are represented by concrete rational regular
; Cauchy names.  P19B2-PI-NAME-VALUE uses Machin's formula, and the
; trigonometric names use rational complex binomial approximants to exp(ix).
; The explicit precision budgets make each returned rational lie within its
; requested positive rational tolerance of the represented real.

(defun p19b2-positive-rational-p (x)
  (and (rationalp x)
       (< 0 x)))

(defun p19b2-arctan-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((j (1- terms))
           (power (expt x (+ (* 2 j) 1)))
           (term (/ power (+ (* 2 j) 1))))
      (+ (p19b2-arctan-prefix x j)
         (if (evenp j) term (- term))))))

(defun p19b2-pi-prefix (terms)
  (- (* 16 (p19b2-arctan-prefix 1/5 terms))
     (* 4 (p19b2-arctan-prefix 1/239 terms))))

(defun p19b2-pi-name-value (epsilon)
  (if (p19b2-positive-rational-p epsilon)
      (p19b2-pi-prefix
       (+ 24 (floor 64 epsilon)))
    0))

(defun p19b2-binomial-steps (x epsilon)
  (if (and (rationalp x)
           (p19b2-positive-rational-p epsilon))
      (expt 2
            (+ 64
               (* 16 (floor (abs x) 1))
               (floor 64 epsilon)))
    1))

(defun p19b2-binomial-trig-value (x epsilon cosine-p)
  (if (and (rationalp x)
           (p19b2-positive-rational-p epsilon))
      (let* ((steps (p19b2-binomial-steps x epsilon))
             (base (complex 1 (/ x steps)))
             (power (expt base steps)))
        (if cosine-p
            (realpart power)
          (imagpart power)))
    0))

(defun p19b2-angle-trig-name-value
    (numerator denominator epsilon cosine-p)
  (if (and (natp numerator)
           (posp denominator)
           (<= numerator denominator)
           (p19b2-positive-rational-p epsilon))
      (let* ((inner (/ epsilon 16))
             (pi-value (p19b2-pi-name-value inner))
             (angle (/ (* numerator pi-value) denominator)))
        (p19b2-binomial-trig-value angle inner cosine-p))
    0))

; For 1 <= k < n, both cosine factors are at least 1/n.  Consequently
; the power (n+1)^16 and the factor 2^20 below dominate the accumulated
; error from four powers, reciprocal formation, n-1 summands, and the
; final division by n^3.
(defun p19b2-working-precision (n epsilon)
  (if (and (posp n)
           (p19b2-positive-rational-p epsilon))
      (/ (if (< epsilon 1) epsilon 1)
         (* 1048576 (expt (+ n 1) 16)))
    1))

(defun p19b2-summand-name-value (n k precision)
  (if (and (posp n)
           (posp k)
           (< k n)
           (p19b2-positive-rational-p precision))
      (let* ((two-n (* 2 n))
             (sine
              (p19b2-angle-trig-name-value
               (- (* 2 k) 1) two-n precision nil))
             (cos-left
              (p19b2-angle-trig-name-value
               (- k 1) two-n precision t))
             (cos-right
              (p19b2-angle-trig-name-value
               k two-n precision t))
             (denominator
              (* (expt cos-left 2)
                 (expt cos-right 2))))
        (/ sine denominator))
    0))

(defun p19b2-sum-through-name-value (n k precision)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      0
    (+ (p19b2-sum-through-name-value n (1- k) precision)
       (p19b2-summand-name-value n k precision))))

(defun p19b2-normalized-name-value (n epsilon)
  (if (and (posp n)
           (p19b2-positive-rational-p epsilon))
      (let ((precision (p19b2-working-precision n epsilon)))
        (/ (p19b2-sum-through-name-value n (1- n) precision)
           (expt n 3)))
    0))

(defun p19b2-solution-name-value (epsilon)
  (if (p19b2-positive-rational-p epsilon)
      (let* ((precision
              (/ (if (< epsilon 1) epsilon 1) 4096))
             (pi-value (p19b2-pi-name-value precision)))
        (/ 8 (expt pi-value 3)))
    0))

; If q_n(delta) and q(delta) are the regular-name values above, each is
; within delta of its represented real.  Thus
;   |q_n(epsilon/8)-q(epsilon/8)| < 3 epsilon/4
; implies real distance < epsilon.  Conversely, a real tail within
; epsilon/2 satisfies this displayed test.  Since positive rational
; epsilons are cofinal among positive real epsilons, the following is
; bidirectionally equivalent to the usual real epsilon-N limit.
(defun p19b2-name-distance-within-p (n epsilon)
  (and (posp n)
       (p19b2-positive-rational-p epsilon)
       (< (abs
           (- (p19b2-normalized-name-value n (/ epsilon 8))
              (p19b2-solution-name-value (/ epsilon 8))))
          (* 3/4 epsilon))))

(defun-sk p19b2-limit-tail-p (epsilon start)
  (forall (n)
    (implies (and (natp n)
                  (<= start n))
             (p19b2-name-distance-within-p n epsilon))))

(defun-sk p19b2-limit-cutoff-exists-p (epsilon)
  (exists (start)
    (and (natp start)
         (p19b2-limit-tail-p epsilon start))))

(defun-sk putnambench-putnam-2019-b2-statement ()
  (forall (epsilon)
    (implies (p19b2-positive-rational-p epsilon)
             (p19b2-limit-cutoff-exists-p epsilon))))

(value-triple :itpeval-statement-checked)

:q
