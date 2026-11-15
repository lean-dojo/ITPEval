;; Statement-only formalization of VERINA corpus artifact verina_basic_63,
;; catalog title "has_close_elements": a deterministic pair scan over finite
;; IEEE-754 binary64 values reports whether two list elements have absolute
;; difference below a nonnegative threshold. This file contains no proof.

(in-package "ACL2")

;; Finite nonzero binary64 values are represented by their exact dyadic
;; rationals. Signed zeros, infinities, and NaN have distinct tags. Since the
;; source contract excludes NaN everywhere it can affect the result, one NaN
;; tag faithfully represents the observationally equivalent NaN payloads.

(defun verina-basic-63-nat-floor-log2 (n)
  (if (and
       (integerp n)
       (< 0 n))
      (- (integer-length n) 1)
    0))

(defun verina-basic-63-positive-rational-binary-exponent (x)
  (if (and
       (rationalp x)
       (< 0 x))
      (let* ((num (numerator x))
             (den (denominator x))
             (candidate
              (-
               (verina-basic-63-nat-floor-log2 num)
               (verina-basic-63-nat-floor-log2 den))))
        (if (< x (expt 2 candidate))
            (- candidate 1)
          candidate))
    0))

(defun verina-basic-63-round-positive-rational-to-even-integer (x)
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

(defun verina-basic-63-finite-nonzero-float64-p (x)
  (and
   (rationalp x)
   (not (equal x 0))
   (or
    ;; Subnormal values are nonzero multiples of 2^-1074 below 2^-1022.
    (and
     (< (abs x) (expt 2 -1022))
     (integerp (* x (expt 2 1074))))
    ;; Normal values have a 53-bit significand and exponent -1022..1023.
    (let* ((magnitude (abs x))
           (exponent
            (verina-basic-63-positive-rational-binary-exponent
             magnitude)))
      (and
       (<= -1022 exponent)
       (<= exponent 1023)
       (integerp
        (* magnitude
           (expt 2 (- 52 exponent)))))))))

(defun verina-basic-63-float64-p (x)
  (or
   (verina-basic-63-finite-nonzero-float64-p x)
   (member-eq
    x
    '(:float64-positive-zero
      :float64-negative-zero
      :float64-positive-infinity
      :float64-negative-infinity
      :float64-nan))))

(defun verina-basic-63-float64-zero-p (x)
  (or
   (eq x :float64-positive-zero)
   (eq x :float64-negative-zero)))

(defun verina-basic-63-float64-nan-p (x)
  (eq x :float64-nan))

(defun verina-basic-63-float64-infinite-p (x)
  (or
   (eq x :float64-positive-infinity)
   (eq x :float64-negative-infinity)))

(defun verina-basic-63-float64-finite-p (x)
  (or
   (verina-basic-63-finite-nonzero-float64-p x)
   (verina-basic-63-float64-zero-p x)))

(defun verina-basic-63-float64-finite-value (x)
  (if (rationalp x)
      x
    0))

;; Round an arbitrary nonzero rational to binary64 under round-to-nearest,
;; ties-to-even. Subnormal rounding uses the fixed 2^-1074 quantum. Normal
;; rounding uses the source exponent. A rounded 2^53 significand renormalizes
;; at lower exponents; only that carry at exponent 1023 crosses the IEEE
;; overflow boundary to signed infinity.

(defun verina-basic-63-round-nonzero-rational-to-float64 (x)
  (let* ((negative (< x 0))
         (magnitude (abs x)))
    (if (< magnitude (expt 2 -1022))
        (let* ((quantum (expt 2 -1074))
               (significand
                (verina-basic-63-round-positive-rational-to-even-integer
                 (/ magnitude quantum))))
          (if (equal significand 0)
              (if negative
                  :float64-negative-zero
                :float64-positive-zero)
            (let ((rounded (* significand quantum)))
              (if negative
                  (- rounded)
                rounded))))
      (let* ((exponent
              (verina-basic-63-positive-rational-binary-exponent
               magnitude)))
        (if (< 1023 exponent)
            (if negative
                :float64-negative-infinity
              :float64-positive-infinity)
          (let* ((quantum (expt 2 (- exponent 52)))
                 (significand
                  (verina-basic-63-round-positive-rational-to-even-integer
                   (/ magnitude quantum))))
            (if (and
                 (equal exponent 1023)
                 (<= (expt 2 53) significand))
                (if negative
                    :float64-negative-infinity
                  :float64-positive-infinity)
              (let ((rounded (* significand quantum)))
                (if negative
                    (- rounded)
                  rounded)))))))))

;; IEEE ordered comparison: every comparison with NaN is false, infinities
;; have their usual endpoints, signed zeros compare equal, and finite values
;; compare by their exact rational values.

(defun verina-basic-63-float64-le (x y)
  (and
   (verina-basic-63-float64-p x)
   (verina-basic-63-float64-p y)
   (not (verina-basic-63-float64-nan-p x))
   (not (verina-basic-63-float64-nan-p y))
   (cond
    ((eq x :float64-negative-infinity)
     t)
    ((eq y :float64-positive-infinity)
     t)
    ((eq x :float64-positive-infinity)
     (eq y :float64-positive-infinity))
    ((eq y :float64-negative-infinity)
     nil)
    (t
     (<=
      (verina-basic-63-float64-finite-value x)
      (verina-basic-63-float64-finite-value y))))))

(defun verina-basic-63-float64-lt (x y)
  (and
   (verina-basic-63-float64-le x y)
   (not
    (verina-basic-63-float64-le y x))))

(defun verina-basic-63-float64-ge (x y)
  (verina-basic-63-float64-le y x))

;; For exact-zero subtraction, round-to-nearest produces negative zero only
;; for -0 - +0; every other exact cancellation produces positive zero.

(defun verina-basic-63-zero-subtraction-result (x y)
  (if (and
       (eq x :float64-negative-zero)
       (eq y :float64-positive-zero))
      :float64-negative-zero
    :float64-positive-zero))

;; This is IEEE binary64 subtraction on the complete represented Float
;; domain. Finite subtraction is exact rational subtraction followed by one
;; round-to-nearest-even operation.

(defun verina-basic-63-float64-sub (x y)
  (cond
   ((or
     (not (verina-basic-63-float64-p x))
     (not (verina-basic-63-float64-p y))
     (verina-basic-63-float64-nan-p x)
     (verina-basic-63-float64-nan-p y))
    :float64-nan)
   ((eq x :float64-positive-infinity)
    (if (eq y :float64-positive-infinity)
        :float64-nan
      :float64-positive-infinity))
   ((eq x :float64-negative-infinity)
    (if (eq y :float64-negative-infinity)
        :float64-nan
      :float64-negative-infinity))
   ((eq y :float64-positive-infinity)
    :float64-negative-infinity)
   ((eq y :float64-negative-infinity)
    :float64-positive-infinity)
   (t
    (let ((difference
           (-
            (verina-basic-63-float64-finite-value x)
            (verina-basic-63-float64-finite-value y))))
      (if (equal difference 0)
          (verina-basic-63-zero-subtraction-result x y)
        (verina-basic-63-round-nonzero-rational-to-float64
         difference))))))

;; This is the source helper: subtract once for the branch test, then return
;; either the reverse subtraction or that first subtraction.

(defun verina-basic-63-abs-diff (a b)
  (let ((a-minus-b
         (verina-basic-63-float64-sub a b)))
    (if
     (verina-basic-63-float64-lt
      a-minus-b
      :float64-positive-zero)
     (verina-basic-63-float64-sub b a)
      a-minus-b)))

(defun verina-basic-63-float64-list-p (numbers)
  (declare (xargs :measure (acl2-count numbers)))
  (if (consp numbers)
      (and
       (verina-basic-63-float64-p (car numbers))
       (verina-basic-63-float64-list-p (cdr numbers)))
    (equal numbers nil)))

(defun verina-basic-63-all-finite-float64-p (numbers)
  (declare (xargs :measure (acl2-count numbers)))
  (if (consp numbers)
      (and
       (verina-basic-63-float64-finite-p (car numbers))
       (verina-basic-63-all-finite-float64-p (cdr numbers)))
    (equal numbers nil)))

;; This is the complete source precondition: a nonnegative, non-NaN threshold
;; and a list containing no NaN or infinite values.

(defun verina-basic-63-has-close-elements-precond
    (numbers threshold)
  (and
   (verina-basic-63-float64-list-p numbers)
   (verina-basic-63-float64-p threshold)
   (verina-basic-63-float64-ge
    threshold
    :float64-positive-zero)
   (not
    (verina-basic-63-float64-nan-p threshold))
   (verina-basic-63-all-finite-float64-p numbers)))

;; INNER scans the already visited prefix in its original order. OUTER visits
;; list indices from zero upward and appends each current value to that prefix,
;; reproducing the source idx/idx2 loop order and short-circuit result.

(defun verina-basic-63-inner-scan (prefix current threshold)
  (declare (xargs :measure (acl2-count prefix)))
  (if (consp prefix)
      (if
       (verina-basic-63-float64-lt
        (verina-basic-63-abs-diff
         (car prefix)
         current)
        threshold)
       t
        (verina-basic-63-inner-scan
         (cdr prefix)
         current
         threshold))
    nil))

(defun verina-basic-63-outer-scan (remaining prefix threshold)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if
       (verina-basic-63-inner-scan
        prefix
        (car remaining)
        threshold)
       t
        (verina-basic-63-outer-scan
         (cdr remaining)
         (append prefix (list (car remaining)))
         threshold))
    nil))

;; The proof-valued precondition argument is computationally irrelevant and is
;; erased. Empty lists, singleton lists, and every source loop branch retain
;; their exact Boolean behavior.

(defun verina-basic-63-has-close-elements (numbers threshold)
  (verina-basic-63-outer-scan numbers nil threshold))

;; These structural predicates are exactly List.Pairwise
;; (fun a b => absDiff a b >= threshold): every head is related to every
;; later element, recursively.

(defun verina-basic-63-head-separated-from-all-p
    (head tail threshold)
  (declare (xargs :measure (acl2-count tail)))
  (if (consp tail)
      (and
       (verina-basic-63-float64-ge
        (verina-basic-63-abs-diff
         head
         (car tail))
        threshold)
       (verina-basic-63-head-separated-from-all-p
        head
        (cdr tail)
        threshold))
    (equal tail nil)))

(defun verina-basic-63-pairwise-separated-p
    (numbers threshold)
  (declare (xargs :measure (acl2-count numbers)))
  (if (consp numbers)
      (and
       (verina-basic-63-head-separated-from-all-p
        (car numbers)
        (cdr numbers)
        threshold)
       (verina-basic-63-pairwise-separated-p
        (cdr numbers)
        threshold))
    (equal numbers nil)))

;; This is the complete source postcondition:
;;   not result iff every distinct ordered-by-position pair is separated by
;;   at least the threshold.

(defun verina-basic-63-has-close-elements-postcond
    (numbers threshold result)
  (and
   (verina-basic-63-float64-list-p numbers)
   (verina-basic-63-float64-p threshold)
   (or
    (equal result t)
    (equal result nil))
   (iff
    (not result)
    (verina-basic-63-pairwise-separated-p
     numbers
     threshold))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite binary64 list and every binary64 threshold satisfying the
;; exact source precondition, and connects the full postcondition to the exact
;; executable result.

(defun-sk
    verina-basic-63-has-close-elements-spec-satisfied-statement
    ()
  (forall (numbers threshold)
    (implies
     (verina-basic-63-has-close-elements-precond
      numbers
      threshold)
     (verina-basic-63-has-close-elements-postcond
      numbers
      threshold
      (verina-basic-63-has-close-elements
       numbers
       threshold)))))

(value-triple :itpeval-statement-checked)
:q
