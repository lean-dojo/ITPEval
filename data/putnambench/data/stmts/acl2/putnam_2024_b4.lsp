;; Statement-only formalization of PutnamBench corpus artifact putnam_2024_b4:
;; the normalized expected terminal position of the independent uniform
;; integer-driven walk converges to (1 - exp(-2))/2. This file contains no
;; proof.

(in-package "ACL2")

;; Codes from 0 through n^n-1 are the base-n encodings of all length-n draw
;; sequences from {1,...,n}. Thus averaging over these codes is exactly the
;; product-space expectation of the source's independent uniform variables.
;; The update below is the source recurrence, so no sample path or possible
;; value is omitted.
(defun putnam-2024-b4-terminal-state (n code steps position)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      position
    (let* ((choice (+ 1 (mod code n)))
           (next-state
            (cond ((> choice position) (+ position 1))
                  ((equal choice position) position)
                  (t (- position 1)))))
      (putnam-2024-b4-terminal-state
       n
       (floor code n)
       (- steps 1)
       next-state))))

(defun putnam-2024-b4-terminal-sum (n remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (putnam-2024-b4-terminal-state
        n (- remaining 1) n 1)
       (putnam-2024-b4-terminal-sum
        n (- remaining 1)))))

(defun putnam-2024-b4-normalized-expectation (n)
  (if (posp n)
      (let ((sample-count (expt n n)))
        (/ (putnam-2024-b4-terminal-sum
            n sample-count)
           (* sample-count n)))
    0))

(defun putnam-2024-b4-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-2024-b4-factorial (- n 1)))))

;; These exact rational Taylor prefixes form a Cauchy name for exp(-2).
(defun putnam-2024-b4-exp-minus-two-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((degree (- terms 1)))
      (+ (putnam-2024-b4-exp-minus-two-prefix degree)
         (/ (expt -2 degree)
            (putnam-2024-b4-factorial degree))))))

(defun putnam-2024-b4-solution-approx (terms)
  (/ (- 1
        (putnam-2024-b4-exp-minus-two-prefix terms))
     2))

;; Positive rational tolerances are cofinal among positive real tolerances.
;; The product-space averages above are exact rationals, while the Taylor
;; prefixes are an unbounded exact-real presentation rather than a rational
;; replacement for exp(-2). The nested DEFUN-SK predicates preserve the
;; source limit's quantifier order exactly: for every positive tolerance
;; there exists a common tail threshold, after which every normalized
;; expectation and every sufficiently accurate solution prefix are close.

(defun-sk putnam-2024-b4-tail-p
    (epsilon cutoff)
  (forall (n exp-terms)
    (implies
     (and
      (natp n)
      (<= cutoff n)
      (natp exp-terms)
      (<= cutoff exp-terms))
     (< (abs
         (- (putnam-2024-b4-normalized-expectation n)
            (putnam-2024-b4-solution-approx exp-terms)))
        epsilon))))

(defun-sk putnam-2024-b4-cutoff-exists-p
    (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2024-b4-tail-p epsilon cutoff))))

(defun-sk putnam-2024-b4-limit-p ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-2024-b4-cutoff-exists-p epsilon))))

(defun putnambench-putnam-2024-b4-statement ()
  (putnam-2024-b4-limit-p))

(value-triple :itpeval-statement-checked)
:q
