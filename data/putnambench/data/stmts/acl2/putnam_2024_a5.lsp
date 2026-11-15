;; Statement-only formalization of PutnamBench corpus artifact putnam_2024_a5:
;; the origin-centered radius-nine circle has its unique probability-minimizing
;; radius-one target disk at the origin. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; This generic function is an arbitrary rational Cauchy presentation of r.
;; Regularity and the interval restriction are explicit in the root predicate.
(defstub putnam-2024-a5-r-approx (precision) t)

(defun putnam-2024-a5-positive-rational-p (value)
  (and
   (rationalp value)
   (< 0 value)))

(defun-sk putnam-2024-a5-regular-real-name-p ()
  (forall (precision eta)
    (implies
     (and
      (putnam-2024-a5-positive-rational-p precision)
      (putnam-2024-a5-positive-rational-p eta))
     (let ((left (putnam-2024-a5-r-approx precision))
           (right (putnam-2024-a5-r-approx eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ precision eta)))))))

;; For a regular name these are the exact strict comparisons r < q and q < r.
(defun-sk putnam-2024-a5-real-less-than-rational-p (q)
  (exists (precision margin)
    (and
     (rationalp q)
     (putnam-2024-a5-positive-rational-p precision)
     (putnam-2024-a5-positive-rational-p margin)
     (let ((sample (putnam-2024-a5-r-approx precision)))
       (and
        (rationalp sample)
        (< (+ sample precision margin) q))))))

(defun-sk putnam-2024-a5-rational-less-than-real-p (q)
  (exists (precision margin)
    (and
     (rationalp q)
     (putnam-2024-a5-positive-rational-p precision)
     (putnam-2024-a5-positive-rational-p margin)
     (let ((sample (putnam-2024-a5-r-approx precision)))
       (and
        (rationalp sample)
        (< (+ q precision margin) sample))))))

(defun putnam-2024-a5-real-zero-p ()
  (and
   (putnam-2024-a5-regular-real-name-p)
   (not (putnam-2024-a5-real-less-than-rational-p 0))
   (not (putnam-2024-a5-rational-less-than-real-p 0))))

(defun putnam-2024-a5-radius-in-range-p ()
  (and
   (putnam-2024-a5-regular-real-name-p)
   (not (putnam-2024-a5-real-less-than-rational-p 0))
   (not (putnam-2024-a5-rational-less-than-real-p 8))))

;; Rational partial sums for pi, cosine, and arcsine provide canonical Cauchy
;; presentations of the transcendental values in the chord probability.
(defun putnam-2024-a5-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (putnam-2024-a5-factorial (- n 1)))))

(defun putnam-2024-a5-alternating-sign (n)
  (if (equal (mod (nfix n) 2) 0)
      1
    -1))

(defun putnam-2024-a5-pi-series-sum (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((k (- terms 1)))
      (+
       (putnam-2024-a5-pi-series-sum k)
       (/
        (putnam-2024-a5-alternating-sign k)
        (+ (* 2 k) 1))))))

(defun putnam-2024-a5-pi-approx (terms)
  (* 4 (putnam-2024-a5-pi-series-sum terms)))

(defun putnam-2024-a5-cos-series-sum (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((k (- terms 1)))
      (+
       (putnam-2024-a5-cos-series-sum x k)
       (/
        (*
         (putnam-2024-a5-alternating-sign k)
         (expt x (* 2 k)))
        (putnam-2024-a5-factorial (* 2 k)))))))

(defun putnam-2024-a5-central-binomial (k)
  (/
   (putnam-2024-a5-factorial (* 2 k))
   (*
    (putnam-2024-a5-factorial k)
    (putnam-2024-a5-factorial k))))

(defun putnam-2024-a5-clamp-unit (x)
  (cond
   ((< x -1) -1)
   ((< 1 x) 1)
   (t x)))

(defun putnam-2024-a5-asin-series-sum (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((k (- terms 1)))
      (+
       (putnam-2024-a5-asin-series-sum x k)
       (/
        (*
         (putnam-2024-a5-central-binomial k)
         (expt x (+ (* 2 k) 1)))
        (*
         (expt 4 k)
         (+ (* 2 k) 1)))))))

;; If alpha and beta are the two endpoint angles, the line through the
;; endpoints has signed offset 9*cos((alpha-beta)/2). After the
;; measure-preserving torus change of variables, conditioning on its normal
;; angle theta gives the kernel
;;
;;   asin((r*cos(theta)+1)/9) - asin((r*cos(theta)-1)/9).
;;
;; Its angular average differs from the source volume only by a fixed positive
;; factor, so it has exactly the same minimizers.
(defun putnam-2024-a5-kernel-sample
    (r-sample pi-sample numerator denominator terms)
  (let* ((angle
          (/ (* 2 pi-sample numerator)
             denominator))
         (cosine
          (putnam-2024-a5-cos-series-sum angle terms))
         (projection (* r-sample cosine))
         (upper
          (putnam-2024-a5-clamp-unit
           (/ (+ projection 1) 9)))
         (lower
          (putnam-2024-a5-clamp-unit
           (/ (- projection 1) 9))))
    (-
     (putnam-2024-a5-asin-series-sum upper terms)
     (putnam-2024-a5-asin-series-sum lower terms))))

(defun putnam-2024-a5-riemann-sum-aux
    (count total r-sample pi-sample terms)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (let ((k (- count 1)))
      (+
       (putnam-2024-a5-riemann-sum-aux
        k total r-sample pi-sample terms)
       (putnam-2024-a5-kernel-sample
        r-sample pi-sample k total terms)))))

(defun putnam-2024-a5-probability-sum (n)
  (if (zp n)
      0
    (let* ((precision (/ 1 (+ n 1)))
           (r-sample (putnam-2024-a5-r-approx precision))
           (pi-sample (putnam-2024-a5-pi-approx n)))
      (if (rationalp r-sample)
          (/
           (putnam-2024-a5-riemann-sum-aux
            n n r-sample pi-sample n)
           n)
        0))))

(defun putnam-2024-a5-origin-probability-sum (n)
  (if (zp n)
      0
    (/
     (putnam-2024-a5-riemann-sum-aux
      n n 0 (putnam-2024-a5-pi-approx n) n)
     n)))

;; Equality of these two rational sequences is equality of the exact angular
;; averages, hence equality of the original intersection probabilities.
(defun-sk putnam-2024-a5-probability-tail-close-p (epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (<
      (abs
       (-
        (putnam-2024-a5-probability-sum n)
        (putnam-2024-a5-origin-probability-sum n)))
      epsilon))))

(defun-sk putnam-2024-a5-probability-close-at-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2024-a5-probability-tail-close-p
      epsilon cutoff))))

(defun-sk putnam-2024-a5-probability-equals-origin-p ()
  (forall (epsilon)
    (implies
     (putnam-2024-a5-positive-rational-p epsilon)
     (putnam-2024-a5-probability-close-at-p epsilon))))

;; For convergent rational presentations, this eventual epsilon inequality is
;; exactly the limit order Prob(0) <= Prob(r).
(defun-sk putnam-2024-a5-origin-order-tail-p (epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (<
      (putnam-2024-a5-origin-probability-sum n)
      (+
       (putnam-2024-a5-probability-sum n)
       epsilon)))))

(defun-sk putnam-2024-a5-origin-order-at-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2024-a5-origin-order-tail-p
      epsilon cutoff))))

(defun-sk putnam-2024-a5-origin-probability-less-or-equal-p ()
  (forall (epsilon)
    (implies
     (putnam-2024-a5-positive-rational-p epsilon)
     (putnam-2024-a5-origin-order-at-p epsilon))))

;; For every represented r in 0 <= r <= 8, the source minimizer set is {0}
;; exactly when Prob(0) <= Prob(r), and Prob(r) = Prob(0) exactly when r=0.
;; The generic real name makes this predicate universal over the full interval.
(defun putnambench-putnam-2024-a5-statement ()
  (implies
   (putnam-2024-a5-radius-in-range-p)
   (and
    (putnam-2024-a5-origin-probability-less-or-equal-p)
    (equal
     (putnam-2024-a5-probability-equals-origin-p)
     (putnam-2024-a5-real-zero-p)))))

(value-triple :itpeval-statement-checked)
:q
