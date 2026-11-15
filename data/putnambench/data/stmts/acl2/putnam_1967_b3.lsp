;; Statement-only formalization of PutnamBench corpus artifact putnam_1967_b3:
;; continuous real-valued functions of period one have asymptotically
;; decorrelated unit-interval integrals under integer dilation. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The two conservative generic symbols are arbitrary regular rational Cauchy
;; names for values on rational points of [0,1]. The predicates below require
;; uniform continuity and equality of the endpoint values. Hence each
;; admissible name has a unique continuous extension to [0,1], and its
;; endpoint identification has a unique continuous 1-periodic extension to
;; the real line. Conversely, every continuous real-valued 1-periodic
;; function supplies such a name. Thus rational arguments and approximants
;; encode, rather than restrict, the source's arbitrary real functions.
;;
;; Uniform right-endpoint Riemann sums with value precision tending to zero
;; converge to the Lebesgue integrals in the source because all relevant
;; integrands are continuous on [0,1]. The inner mesh cutoff keeps those
;; integral limits internal. The outer epsilon/dilation cutoff is exactly the
;; asserted limit as the natural (equivalently, integer at-top) dilation tends
;; to infinity.

(defstub p67b3-f-approx (x precision) t)
(defstub p67b3-g-approx (x precision) t)

(defun p67b3-abs (x)
  (if (< x 0) (- x) x))

(defun p67b3-positive-rational-p (x)
  (and (rationalp x)
       (< 0 x)))

(defun p67b3-unit-rational-p (x)
  (and (rationalp x)
       (<= 0 x)
       (<= x 1)))

(defun p67b3-value (kind x precision)
  (if (equal kind :f)
      (p67b3-f-approx x precision)
    (p67b3-g-approx x precision)))

(defun-sk p67b3-regular-name-p (kind)
  (forall (x epsilon eta)
    (implies
     (and
      (p67b3-unit-rational-p x)
      (p67b3-positive-rational-p epsilon)
      (p67b3-positive-rational-p eta))
     (and
      (rationalp (p67b3-value kind x epsilon))
      (rationalp (p67b3-value kind x eta))
      (<=
       (p67b3-abs
        (- (p67b3-value kind x epsilon)
           (p67b3-value kind x eta)))
       (+ epsilon eta))))))

;; At precision epsilon/8, the displayed 3*epsilon/4 bound is equivalent to
;; exact value distance below epsilon after passing to the represented reals.

(defun-sk p67b3-uniform-continuity-neighborhood-p
    (kind epsilon delta)
  (forall (x y)
    (implies
     (and
      (p67b3-unit-rational-p x)
      (p67b3-unit-rational-p y)
      (< (p67b3-abs (- x y)) delta))
     (<
      (p67b3-abs
       (- (p67b3-value kind x (/ epsilon 8))
          (p67b3-value kind y (/ epsilon 8))))
      (* 3/4 epsilon)))))

(defun-sk p67b3-uniform-continuity-radius-exists-p
    (kind epsilon)
  (exists (delta)
    (and
     (p67b3-positive-rational-p delta)
     (p67b3-uniform-continuity-neighborhood-p
      kind epsilon delta))))

(defun-sk p67b3-uniformly-continuous-p (kind)
  (forall (epsilon)
    (implies
     (p67b3-positive-rational-p epsilon)
     (p67b3-uniform-continuity-radius-exists-p
      kind epsilon))))

(defun-sk p67b3-endpoints-equal-p (kind)
  (forall (epsilon)
    (implies
     (p67b3-positive-rational-p epsilon)
     (<=
      (p67b3-abs
       (- (p67b3-value kind 0 epsilon)
          (p67b3-value kind 1 epsilon)))
      (* 2 epsilon)))))

(defun p67b3-admissible-periodic-function-p (kind)
  (and
   (p67b3-regular-name-p kind)
   (p67b3-uniformly-continuous-p kind)
   (p67b3-endpoints-equal-p kind)))

(defun p67b3-mesh-precision (pieces)
  (if (posp pieces)
      (/ 1 pieces)
    1))

(defun p67b3-periodic-argument (x)
  (- x (floor x 1)))

(defun p67b3-integral-numerator
    (kind index pieces)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      0
    (let* ((x (/ index pieces))
           (precision (p67b3-mesh-precision pieces)))
      (+
       (p67b3-value kind x precision)
       (p67b3-integral-numerator
        kind (- index 1) pieces)))))

(defun p67b3-integral-approx (kind pieces)
  (if (posp pieces)
      (/
       (p67b3-integral-numerator
        kind pieces pieces)
       pieces)
    0))

(defun p67b3-correlation-numerator
    (index pieces dilation)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      0
    (let* ((x (/ index pieces))
           (precision (p67b3-mesh-precision pieces))
           (periodic-x
            (p67b3-periodic-argument
             (* dilation x))))
      (+
       (*
        (p67b3-value :f x precision)
        (p67b3-value :g periodic-x precision))
       (p67b3-correlation-numerator
        (- index 1) pieces dilation)))))

(defun p67b3-correlation-integral-approx
    (dilation pieces)
  (if (and (natp dilation)
           (posp pieces))
      (/
       (p67b3-correlation-numerator
        pieces pieces dilation)
       pieces)
    0))

(defun p67b3-limit-difference-approx
    (dilation pieces)
  (-
   (p67b3-correlation-integral-approx
    dilation pieces)
   (*
    (p67b3-integral-approx :f pieces)
    (p67b3-integral-approx :g pieces))))

;; For fixed dilation, letting PIECES tend to infinity recovers the exact
;; difference between the correlation integral and the product of the two
;; means. Requiring an eventual bound for every positive rational epsilon is
;; equivalent to convergence of that exact difference to zero.

(defun-sk p67b3-integration-tail-p
    (dilation epsilon mesh-cutoff)
  (forall (pieces)
    (implies
     (and
      (posp pieces)
      (posp mesh-cutoff)
      (<= mesh-cutoff pieces))
     (<
      (p67b3-abs
       (p67b3-limit-difference-approx
        dilation pieces))
      epsilon))))

(defun-sk p67b3-integration-cutoff-exists-p
    (dilation epsilon)
  (exists (mesh-cutoff)
    (and
     (posp mesh-cutoff)
     (p67b3-integration-tail-p
      dilation epsilon mesh-cutoff))))

(defun-sk p67b3-dilation-tail-p
    (epsilon dilation-cutoff)
  (forall (dilation)
    (implies
     (and
      (natp dilation)
      (natp dilation-cutoff)
      (<= dilation-cutoff dilation))
     (p67b3-integration-cutoff-exists-p
      dilation epsilon))))

(defun-sk p67b3-dilation-cutoff-exists-p (epsilon)
  (exists (dilation-cutoff)
    (and
     (natp dilation-cutoff)
     (p67b3-dilation-tail-p
      epsilon dilation-cutoff))))

(defun-sk p67b3-correlation-limit-p ()
  (forall (epsilon)
    (implies
     (p67b3-positive-rational-p epsilon)
     (p67b3-dilation-cutoff-exists-p epsilon))))

(defun putnambench-putnam-1967-b3-statement ()
  (implies
   (and
    (p67b3-admissible-periodic-function-p :f)
    (p67b3-admissible-periodic-function-p :g))
   (p67b3-correlation-limit-p)))

(value-triple :itpeval-statement-checked)
:q
