;; Statement-only formalization of VERINA corpus artifact verina_basic_25,
;; catalog title "sumAndAverage": for a positive natural below 2^53, a
;; deterministic program returns the sum from zero through the input and its
;; IEEE-754 binary64 average. This file contains no proof.

(in-package "ACL2")

;; Binary64 finite nonzero values are represented by their exact dyadic
;; rationals; the non-rational IEEE special values and both signed zeros have
;; distinct tags. The following arithmetic definitions give exact binary
;; round-to-nearest, ties-to-even without relying on an external book.

(defun verina-basic-25-nat-floor-log2 (n)
  (if (and
       (integerp n)
       (< 0 n))
      (- (integer-length n) 1)
    0))

(defun verina-basic-25-positive-rational-binary-exponent (x)
  (if (and
       (rationalp x)
       (< 0 x))
      (let* ((num (numerator x))
             (den (denominator x))
             (candidate
              (-
               (verina-basic-25-nat-floor-log2 num)
               (verina-basic-25-nat-floor-log2 den))))
        (if (< x (expt 2 candidate))
            (- candidate 1)
          candidate))
    0))

(defun verina-basic-25-round-positive-rational-to-even-integer (x)
  (let* ((lower (floor x 1))
         (fraction (- x lower)))
    (cond
     ((< fraction 1/2)
      lower)
     ((< 1/2 fraction)
      (+ lower 1))
     ((evenp lower)
      lower)
     (t
      (+ lower 1)))))

(defun verina-basic-25-round-positive-rational-to-float64 (x)
  (if (and
       (rationalp x)
       (< 0 x))
      (let* ((exponent
              (verina-basic-25-positive-rational-binary-exponent x))
             (quantum
              (expt 2 (- exponent 52)))
             (significand
              (verina-basic-25-round-positive-rational-to-even-integer
               (/ x quantum))))
        (* significand quantum))
    :float64-positive-zero))

(defun verina-basic-25-finite-nonzero-float64-p (x)
  (and
   (rationalp x)
   (not (equal x 0))
   (or
    ;; Subnormals are nonzero integral multiples of 2^-1074 below 2^-1022.
    (and
     (< (abs x) (expt 2 -1022))
     (integerp (* x (expt 2 1074))))
    ;; Normals have a 53-bit significand and unbiased exponent -1022..1023.
    (let* ((magnitude (abs x))
           (exponent
            (verina-basic-25-positive-rational-binary-exponent magnitude)))
      (and
       (<= -1022 exponent)
       (<= exponent 1023)
       (integerp
        (* magnitude
           (expt 2 (- 52 exponent)))))))))

(defun verina-basic-25-float64-p (x)
  (or
   (verina-basic-25-finite-nonzero-float64-p x)
   (member-eq
    x
    '(:float64-positive-zero
      :float64-negative-zero
      :float64-positive-infinity
      :float64-negative-infinity
      :float64-nan))))

(defun verina-basic-25-float64-zero-p (x)
  (or
   (eq x :float64-positive-zero)
   (eq x :float64-negative-zero)))

;; This is Float BEq: NaN is unequal to every value, while the two signed
;; zeros are equal and all other represented values compare by exact identity.

(defun verina-basic-25-float64-beq (x y)
  (and
   (verina-basic-25-float64-p x)
   (verina-basic-25-float64-p y)
   (not (eq x :float64-nan))
   (not (eq y :float64-nan))
   (or
    (and
     (verina-basic-25-float64-zero-p x)
     (verina-basic-25-float64-zero-p y))
    (equal x y))))

;; This is the source precondition, including the strict precision bound.

(defun verina-basic-25-sum-and-average-precond (n)
  (and
   (natp n)
   (< 0 n)
   (< n 9007199254740992)))

;; List.range (n + 1) contains 0 through n. Its sum is represented by this
;; structurally recursive computation, which adds exactly those naturals.

(defun verina-basic-25-sum-through (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ n
       (verina-basic-25-sum-through (- n 1)))))

;; Lean Nat.toFloat is binary64 conversion with round-to-nearest, ties-to-even.

(defun verina-basic-25-nat-to-float64 (n)
  (if (zp n)
      :float64-positive-zero
    (verina-basic-25-round-positive-rational-to-float64
     (nfix n))))

;; On source-valid calls both operands are positive finite binary64 rationals.
;; IEEE division is exact rational division followed by one binary64 rounding.

(defun verina-basic-25-positive-float64-div (numerator denominator)
  (verina-basic-25-round-positive-rational-to-float64
   (/ numerator denominator)))

;; Int x Float is encoded bijectively as a dotted pair whose car is an
;; arbitrary ACL2 integer and whose cdr is a binary64 floating-point datum.

(defun verina-basic-25-result-p (result)
  (and
   (consp result)
   (integerp (car result))
   (verina-basic-25-float64-p (cdr result))))

(defun verina-basic-25-result-beq (left right)
  (and
   (verina-basic-25-result-p left)
   (verina-basic-25-result-p right)
   (equal (car left) (car right))
   (verina-basic-25-float64-beq
    (cdr left)
    (cdr right))))

;; The proof-valued precondition argument is computationally irrelevant and is
;; erased. The conditional, recursive sum, conversions, division, and returned
;; pair reproduce the complete source implementation.

(defun verina-basic-25-sum-and-average (n)
  (if (<= n 0)
      (cons 0 :float64-positive-zero)
    (let* ((sum (verina-basic-25-sum-through n))
           (average
            (verina-basic-25-positive-float64-div
             (verina-basic-25-nat-to-float64 sum)
             (verina-basic-25-nat-to-float64 n))))
      (cons sum average))))

;; ACL2 FLOOR on these nonnegative integers is Lean Nat/Int division by two.

(defun verina-basic-25-closed-form-sum (n)
  (floor
   (* n (+ n 1))
   2))

;; This preserves both implications in the source postcondition. The average
;; branch independently converts the closed-form sum and input to binary64,
;; divides those rounded operands, and rounds the quotient exactly once.

(defun verina-basic-25-sum-and-average-postcond
    (n result)
  (and
   (natp n)
   (verina-basic-25-result-p result)
   (implies
    (equal n 0)
    (verina-basic-25-result-beq
     result
     (cons 0 :float64-positive-zero)))
   (implies
    (< 0 n)
    (let ((closed-sum
           (verina-basic-25-closed-form-sum n)))
      (and
       (equal
        (car result)
        closed-sum)
       (verina-basic-25-float64-beq
        (cdr result)
        (verina-basic-25-positive-float64-div
         (verina-basic-25-nat-to-float64 closed-sum)
         (verina-basic-25-nat-to-float64 n))))))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the full Nat domain, applies the complete source precondition, and
;; connects the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-25-sum-and-average-spec-satisfied-statement
    ()
  (forall (n)
    (implies
     (and
      (natp n)
      (verina-basic-25-sum-and-average-precond n))
     (verina-basic-25-sum-and-average-postcond
      n
      (verina-basic-25-sum-and-average n)))))

(value-triple :itpeval-statement-checked)
:q
