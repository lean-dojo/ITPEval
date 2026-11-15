;; Statement-only formalization of PutnamBench corpus artifact putnam_2022_a4:
;; the expected dyadically weighted sum stopped at the first ascent of
;; independent uniform variables on [0,1] equals 2*exp(1/2)-3, represented by
;; an exact Cauchy-limit equality. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These are the midpoints of the GRID-SIZE equal subintervals of [0,1].
(defun putnam-2022-a4-grid-points (count grid-size)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (/ (- (* 2 count) 1)
             (* 2 grid-size))
          (putnam-2022-a4-grid-points
           (- count 1) grid-size))))

(defun putnam-2022-a4-prepend-to-each (value tuples)
  (declare (xargs :measure (acl2-count tuples)))
  (if (endp tuples)
      nil
    (cons (cons value (car tuples))
          (putnam-2022-a4-prepend-to-each
           value (cdr tuples)))))

(defun putnam-2022-a4-extend-tuples (points tuples)
  (declare (xargs :measure (acl2-count points)))
  (if (endp points)
      nil
    (append
     (putnam-2022-a4-prepend-to-each
      (car points) tuples)
     (putnam-2022-a4-extend-tuples
      (cdr points) tuples))))

;; Enumerate all TERMS-tuples from the midpoint grid. As GRID-SIZE is
;; unbounded in the statement below, this is a Riemann name for the full
;; continuum distribution, not a replacement by a fixed finite carrier.
(defun putnam-2022-a4-grid-tuples (terms points)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (list nil)
    (putnam-2022-a4-extend-tuples
     points
     (putnam-2022-a4-grid-tuples
      (- terms 1) points))))

;; Once PREVIOUS <= the next sample, the least-ascent stopping rule excludes
;; that next sample and every later one. EXPONENT is its one-based dyadic
;; exponent when the strict descent continues.
(defun putnam-2022-a4-stopped-tail
    (samples previous exponent)
  (declare (xargs :measure (acl2-count samples)))
  (if (endp samples)
      0
    (if (< (car samples) previous)
        (+ (/ (car samples)
              (expt 2 exponent))
           (putnam-2022-a4-stopped-tail
            (cdr samples)
            (car samples)
            (+ exponent 1)))
      0)))

(defun putnam-2022-a4-stopped-prefix (samples)
  (if (endp samples)
      0
    (+ (/ (car samples) 2)
       (putnam-2022-a4-stopped-tail
        (cdr samples) (car samples) 2))))

(defun putnam-2022-a4-sum-stopped-prefixes (tuples)
  (declare (xargs :measure (acl2-count tuples)))
  (if (endp tuples)
      0
    (+ (putnam-2022-a4-stopped-prefix
        (car tuples))
       (putnam-2022-a4-sum-stopped-prefixes
        (cdr tuples)))))

;; This average applies the source stopping rule directly to every tuple in
;; the canonical independent uniform midpoint grid. Letting TERMS and
;; GRID-SIZE tend to infinity is therefore an exact rational Cauchy name for
;; the source stopped expectation, independently of any evaluated simplex
;; moments.
(defun putnam-2022-a4-expectation-prefix
    (terms grid-size)
  (if (and (natp terms)
           (posp grid-size))
      (/ (putnam-2022-a4-sum-stopped-prefixes
          (putnam-2022-a4-grid-tuples
           terms
           (putnam-2022-a4-grid-points
            grid-size grid-size)))
         (expt grid-size terms))
    0))

(defun putnam-2022-a4-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-2022-a4-factorial (- n 1)))))

;; Exact rational Taylor prefixes for exp(1/2), kept independent of the
;; stopped-expectation Riemann prefixes above.
(defun putnam-2022-a4-exp-half-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- terms 1)))
      (+ (putnam-2022-a4-exp-half-prefix index)
         (/ 1
            (* (expt 2 index)
               (putnam-2022-a4-factorial index)))))))

(defun putnam-2022-a4-solution-prefix (terms)
  (- (* 2
        (putnam-2022-a4-exp-half-prefix terms))
     3))

;; At stage N, use N variables and a 4^N midpoint grid in every coordinate.
;; The dyadic stopped-sum tail tends to zero, while the midpoint error tends
;; to zero because N/4^N does. Thus this diagonal sequence is a rational
;; Cauchy name for the exact continuous iid-uniform expectation, not a fixed
;; finite approximation.
(defun putnam-2022-a4-expectation-name-value (stage)
  (if (natp stage)
      (putnam-2022-a4-expectation-prefix
       stage (expt 4 stage))
    0))

(defun putnam-2022-a4-solution-name-value (stage)
  (if (natp stage)
      (putnam-2022-a4-solution-prefix stage)
    0))

(defun putnam-2022-a4-positive-rational-p (epsilon)
  (and (rationalp epsilon)
       (< 0 epsilon)))

(defun putnam-2022-a4-name-distance-within-p
    (stage epsilon)
  (and
   (natp stage)
   (putnam-2022-a4-positive-rational-p epsilon)
   (< (abs
       (- (putnam-2022-a4-expectation-name-value stage)
          (putnam-2022-a4-solution-name-value stage)))
      epsilon)))

(defun-sk putnam-2022-a4-limit-tail-p
    (epsilon start)
  (forall (stage)
    (implies
     (and (natp stage)
          (<= start stage))
     (putnam-2022-a4-name-distance-within-p
      stage epsilon))))

(defun-sk putnam-2022-a4-limit-cutoff-exists-p
    (epsilon)
  (exists (start)
    (and
     (natp start)
     (putnam-2022-a4-limit-tail-p
      epsilon start))))

;; Positive rationals are cofinal among positive reals, so this is exact
;; equality of the two represented real limits.
(defun-sk putnambench-putnam-2022-a4-statement ()
  (forall (epsilon)
    (implies
     (putnam-2022-a4-positive-rational-p epsilon)
     (putnam-2022-a4-limit-cutoff-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
