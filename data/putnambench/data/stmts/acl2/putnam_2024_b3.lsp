;; Statement-only formalization of PutnamBench corpus artifact putnam_2024_b3:
;; consecutive positive solutions of tan(x)=x exceed pi in spacing by an
;; amount strictly between zero and 1/((n^2+n)*pi). This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; PUTNAM-2024-B3-SEQUENCE-APPROX is a generic oracle: at positive index n
;; and positive rational precision epsilon it approximates r_n.  Its
;; regular-Cauchy law is explicit below, so the source's arbitrary function
;; N+ -> R is not restricted to an APPLY$ function object or a finite table.
;; Every universal precision and index scope is represented directly by
;; DEFUN-SK.
;;
;; Machin's identity and rational alternating sums define pi.  For rational
;; q, (1+i*q/m)^m tends to exp(i*q), so its real and imaginary parts define
;; cosine and sine approximants.  The root condition localizes r_n to
;; [(n+1/4)*pi,(n+1/2)*pi], the interval containing exactly the nth positive
;; solution of tan(x)=x.  This is equivalent to the source's strict ordering,
;; first-root minimality, root equations, and root-free consecutive gaps.

(defstub putnam-2024-b3-sequence-approx
    (index precision)
  t)

(defun putnam-2024-b3-positive-rational-p (value)
  (and
   (rationalp value)
   (< 0 value)))

(defun putnam-2024-b3-min-one (value)
  (if (< 1 value) 1 value))

(defun-sk putnam-2024-b3-real-sequence-p ()
  (forall (index epsilon eta)
    (implies
     (and
      (posp index)
      (putnam-2024-b3-positive-rational-p epsilon)
      (putnam-2024-b3-positive-rational-p eta))
     (let ((left
            (putnam-2024-b3-sequence-approx
             index epsilon))
           (right
            (putnam-2024-b3-sequence-approx
             index eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

;; Exact rational alternating sums for
;; pi = 16*arctan(1/5) - 4*arctan(1/239).

(defun putnam-2024-b3-arctan-prefix (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (1- terms))
           (exponent (+ (* 2 index) 1))
           (term
            (/ (expt z exponent)
               exponent)))
      (+
       (putnam-2024-b3-arctan-prefix z index)
       (if (evenp index)
           term
         (- term))))))

(defun putnam-2024-b3-pi-prefix (terms)
  (-
   (* 16
      (putnam-2024-b3-arctan-prefix
       1/5 terms))
   (* 4
      (putnam-2024-b3-arctan-prefix
       1/239 terms))))

(defun putnam-2024-b3-pi-approx (epsilon)
  (if (putnam-2024-b3-positive-rational-p epsilon)
      (putnam-2024-b3-pi-prefix
       (+ 24 (floor 64 epsilon)))
    0))

;; Rational complex-binomial approximants to cosine and sine at r_index.

(defun putnam-2024-b3-binomial-steps
    (sample epsilon)
  (if (and
       (rationalp sample)
       (putnam-2024-b3-positive-rational-p epsilon))
      (expt
       2
       (+ 64
          (* 16 (floor (abs sample) 1))
          (floor 64 epsilon)))
    1))

(defun putnam-2024-b3-trig-power
    (index epsilon)
  (if (and
       (posp index)
       (putnam-2024-b3-positive-rational-p epsilon))
      (let* ((sample-precision
              (putnam-2024-b3-min-one
               (/ epsilon 16)))
             (sample
              (putnam-2024-b3-sequence-approx
               index sample-precision)))
        (if (rationalp sample)
            (let* ((steps
                    (putnam-2024-b3-binomial-steps
                     sample epsilon))
                   (base
                    (complex 1 (/ sample steps))))
              (expt base steps))
          1))
    1))

(defun putnam-2024-b3-cosine-approx
    (index epsilon)
  (realpart
   (putnam-2024-b3-trig-power
    index epsilon)))

(defun putnam-2024-b3-sine-approx
    (index epsilon)
  (imagpart
   (putnam-2024-b3-trig-power
    index epsilon)))

(defun-sk putnam-2024-b3-root-branches-p ()
  (forall (index eta)
    (implies
     (and
      (posp index)
      (putnam-2024-b3-positive-rational-p eta))
     (let* ((coarse
             (putnam-2024-b3-sequence-approx
              index 1))
            (cap
             (putnam-2024-b3-min-one eta))
            (magnitude
             (+ 4 (abs coarse)))
            (precision
             (/ cap (* 512 magnitude)))
            (x
             (putnam-2024-b3-sequence-approx
              index precision))
            (sine
             (putnam-2024-b3-sine-approx
              index precision))
            (cosine
             (putnam-2024-b3-cosine-approx
              index precision))
            (residual
             (abs (- sine (* x cosine))))
            (pi-precision
             (/ cap (* 128 (+ index 1))))
            (pi-value
             (putnam-2024-b3-pi-approx
              pi-precision))
            (lower
             (* (+ index 1/4) pi-value))
            (upper
             (* (+ index 1/2) pi-value)))
       (and
        (rationalp coarse)
        (rationalp x)
        (rationalp sine)
        (rationalp cosine)
        (rationalp pi-value)
        (<= residual eta)
        (<= lower (+ x eta))
        (<= x (+ upper eta)))))))

(defun putnam-2024-b3-r-definition-p ()
  (and
   (putnam-2024-b3-real-sequence-p)
   (putnam-2024-b3-root-branches-p)))

;; These value functions are the direct first-order counterparts of regular
;; Cauchy-name subtraction and multiplication.  Their precision allocations
;; make them regular names for
;;
;;   gap_n = r_(n+1) - r_n - pi
;;   scaled-gap_n = (n^2+n)*pi*gap_n.

(defun putnam-2024-b3-gap-approx
    (n epsilon)
  (if (and
       (posp n)
       (putnam-2024-b3-positive-rational-p epsilon))
      (-
       (-
        (putnam-2024-b3-sequence-approx
         (+ n 1) (/ epsilon 4))
        (putnam-2024-b3-sequence-approx
         n (/ epsilon 4)))
       (putnam-2024-b3-pi-approx
        (/ epsilon 2)))
    0))

(defun putnam-2024-b3-product-precision
    (left-at-one right-at-one epsilon)
  (putnam-2024-b3-min-one
   (/ epsilon
      (* 8
         (+ 3
            (abs left-at-one)
            (abs right-at-one))))))

(defun putnam-2024-b3-scale (n)
  (+ (* n n) n))

(defun putnam-2024-b3-scaled-pi-approx
    (n epsilon)
  (if (and
       (posp n)
       (putnam-2024-b3-positive-rational-p epsilon))
      (let* ((scale
              (putnam-2024-b3-scale n))
             (precision
              (putnam-2024-b3-product-precision
               scale
               (putnam-2024-b3-pi-approx 1)
               epsilon)))
        (* scale
           (putnam-2024-b3-pi-approx
            precision)))
    0))

(defun putnam-2024-b3-scaled-gap-approx
    (n epsilon)
  (if (and
       (posp n)
       (putnam-2024-b3-positive-rational-p epsilon))
      (let ((precision
             (putnam-2024-b3-product-precision
              (putnam-2024-b3-scaled-pi-approx n 1)
              (putnam-2024-b3-gap-approx n 1)
              epsilon)))
        (*
         (putnam-2024-b3-scaled-pi-approx
          n precision)
         (putnam-2024-b3-gap-approx
          n precision)))
    0))

;; For regular names A and B, A <= B iff every positive rational eta satisfies
;; A(eta/4) <= B(eta/4)+eta.  Negating the relevant universal predicate gives
;; the two strict inequalities in the source conclusion.

(defun-sk putnam-2024-b3-gap-le-zero-p (n)
  (forall (eta)
    (implies
     (putnam-2024-b3-positive-rational-p eta)
     (let ((gap
            (putnam-2024-b3-gap-approx
             n (/ eta 4))))
       (and
        (rationalp gap)
        (<= gap eta))))))

(defun-sk putnam-2024-b3-one-le-scaled-gap-p
    (n)
  (forall (eta)
    (implies
     (putnam-2024-b3-positive-rational-p eta)
     (let ((scaled-gap
            (putnam-2024-b3-scaled-gap-approx
             n (/ eta 4))))
       (and
        (rationalp scaled-gap)
        (<= 1 (+ scaled-gap eta)))))))

(defun putnambench-putnam-2024-b3-statement
    (n)
  (implies
   (and
    (posp n)
    (putnam-2024-b3-r-definition-p))
   (and
    (not
     (putnam-2024-b3-gap-le-zero-p n))
    (not
     (putnam-2024-b3-one-le-scaled-gap-p
      n)))))

(value-triple :itpeval-statement-checked)
:q
