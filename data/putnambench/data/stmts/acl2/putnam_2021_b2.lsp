;; Statement-only formalization of PutnamBench corpus artifact putnam_2021_b2:
;; the maximum of the weighted geometric-mean series over nonnegative real
;; sequences with sum 1 is 2/3. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative symbols give arbitrary rational regular-Cauchy
;; approximations to a real sequence A, its nonnegative geometric means G,
;; and a possible value S of the weighted series. They are genuine unbounded
;; functions, not finite tables. Every real sequence has such approximations.

(defstub putnam-2021-b2-a-approx (n epsilon) t)
(defstub putnam-2021-b2-g-approx (n epsilon) t)
(defstub putnam-2021-b2-s-approx (epsilon) t)

(defun putnam-2021-b2-positive-rational-p (x)
  (and (rationalp x)
       (< 0 x)))

(defun putnam-2021-b2-sequence-approx (which n epsilon)
  (if (equal which :a)
      (putnam-2021-b2-a-approx n epsilon)
    (putnam-2021-b2-g-approx n epsilon)))

;; Regular Cauchy names are an exact presentation of arbitrary real values.

(defun-sk putnam-2021-b2-sequence-regular-p (which)
  (forall (n epsilon eta)
    (implies
     (and
      (natp n)
      (putnam-2021-b2-positive-rational-p epsilon)
      (putnam-2021-b2-positive-rational-p eta))
     (let ((left
            (putnam-2021-b2-sequence-approx
             which n epsilon))
           (right
            (putnam-2021-b2-sequence-approx
             which n eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

(defun-sk putnam-2021-b2-target-regular-p ()
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2021-b2-positive-rational-p epsilon)
      (putnam-2021-b2-positive-rational-p eta))
     (let ((left
            (putnam-2021-b2-s-approx epsilon))
           (right
            (putnam-2021-b2-s-approx eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

;; This epsilon condition is equivalent to nonnegativity of every represented
;; real term.

(defun-sk putnam-2021-b2-sequence-nonnegative-p (which)
  (forall (n epsilon)
    (implies
     (and
      (natp n)
      (putnam-2021-b2-positive-rational-p epsilon))
     (<= (- epsilon)
         (putnam-2021-b2-sequence-approx
          which n epsilon)))))

(defun putnam-2021-b2-a-prefix (terms precision)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- (nfix terms) 1)))
      (+ (putnam-2021-b2-a-prefix index precision)
         (putnam-2021-b2-a-approx index precision)))))

(defun putnam-2021-b2-a-product (terms precision)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      1
    (let ((index (- (nfix terms) 1)))
      (* (putnam-2021-b2-a-product index precision)
         (putnam-2021-b2-a-approx index precision)))))

;; The precision epsilon/(4*(terms+1)) keeps the total Cauchy-name error in an
;; arbitrary finite prefix uniformly below epsilon/4. Thus this is exactly
;; convergence of sum A_n to 1, with the cutoff existentially quantified.

(defun-sk putnam-2021-b2-sum-one-tail-p (epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (<
      (abs
       (-
        (putnam-2021-b2-a-prefix
         terms
         (/ epsilon (* 4 (+ terms 1))))
        1))
      epsilon))))

(defun-sk putnam-2021-b2-sum-one-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2021-b2-sum-one-tail-p
      epsilon cutoff))))

(defun-sk putnam-2021-b2-sums-to-one-p ()
  (forall (epsilon)
    (implies
     (putnam-2021-b2-positive-rational-p epsilon)
     (putnam-2021-b2-sum-one-cutoff-exists-p
      epsilon))))

;; G_n is the principal (n+1)-st root of product_{k=0}^n A_k. Existence of an
;; arbitrarily small positive working precision expresses exact equality of
;; the represented reals; nonnegativity of G selects the principal root.

(defun-sk putnam-2021-b2-root-precision-exists-p
    (n epsilon)
  (exists (precision)
    (and
     (putnam-2021-b2-positive-rational-p precision)
     (< precision epsilon)
     (<
      (abs
       (-
        (expt
         (putnam-2021-b2-g-approx n precision)
         (+ n 1))
        (putnam-2021-b2-a-product
         (+ n 1) precision)))
      epsilon))))

(defun-sk putnam-2021-b2-geometric-means-p ()
  (forall (n epsilon)
    (implies
     (and
      (natp n)
      (putnam-2021-b2-positive-rational-p epsilon))
     (putnam-2021-b2-root-precision-exists-p
      n epsilon))))

(defun putnam-2021-b2-weighted-prefix (terms precision)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- (nfix terms) 1))
           (n (+ index 1)))
      (+
       (putnam-2021-b2-weighted-prefix
        index precision)
       (*
        (/ n (expt 2 n))
        (putnam-2021-b2-g-approx
         index precision))))))

;; The weights n/2^n have bounded total mass. Requiring all sufficiently fine
;; Cauchy approximations makes these predicates exactly the Cauchy criterion
;; and convergence to the represented target S for the source series.

(defun-sk putnam-2021-b2-series-cauchy-tail-p
    (epsilon cutoff precision-bound)
  (forall (left-terms right-terms precision)
    (implies
     (and
      (natp left-terms)
      (natp right-terms)
      (<= cutoff left-terms)
      (<= cutoff right-terms)
      (putnam-2021-b2-positive-rational-p precision)
      (<= precision precision-bound))
     (<
      (abs
       (-
        (putnam-2021-b2-weighted-prefix
         left-terms precision)
        (putnam-2021-b2-weighted-prefix
         right-terms precision)))
      epsilon))))

(defun-sk putnam-2021-b2-series-cauchy-cutoffs-exist-p
    (epsilon)
  (exists (cutoff precision-bound)
    (and
     (natp cutoff)
     (putnam-2021-b2-positive-rational-p
      precision-bound)
     (putnam-2021-b2-series-cauchy-tail-p
      epsilon cutoff precision-bound))))

(defun-sk putnam-2021-b2-series-cauchy-p ()
  (forall (epsilon)
    (implies
     (putnam-2021-b2-positive-rational-p epsilon)
     (putnam-2021-b2-series-cauchy-cutoffs-exist-p
      epsilon))))

(defun-sk putnam-2021-b2-series-limit-tail-p
    (epsilon cutoff precision-bound)
  (forall (terms term-precision target-precision)
    (implies
     (and
      (natp terms)
      (<= cutoff terms)
      (putnam-2021-b2-positive-rational-p
       term-precision)
      (<= term-precision precision-bound)
      (putnam-2021-b2-positive-rational-p
       target-precision)
      (<= target-precision precision-bound))
     (<
      (abs
       (-
        (putnam-2021-b2-weighted-prefix
         terms term-precision)
        (putnam-2021-b2-s-approx
         target-precision)))
      epsilon))))

(defun-sk putnam-2021-b2-series-limit-cutoffs-exist-p
    (epsilon)
  (exists (cutoff precision-bound)
    (and
     (natp cutoff)
     (putnam-2021-b2-positive-rational-p
      precision-bound)
     (putnam-2021-b2-series-limit-tail-p
      epsilon cutoff precision-bound))))

(defun-sk putnam-2021-b2-series-has-target-p ()
  (forall (epsilon)
    (implies
     (putnam-2021-b2-positive-rational-p epsilon)
     (putnam-2021-b2-series-limit-cutoffs-exist-p
      epsilon))))

(defun-sk putnam-2021-b2-target-at-most-two-thirds-p ()
  (forall (epsilon)
    (implies
     (putnam-2021-b2-positive-rational-p epsilon)
     (<=
      (putnam-2021-b2-s-approx epsilon)
      (+ 2/3 epsilon)))))

;; The internal existential witness for attainment is made concrete:
;; A_n = 3/4^(n+1), whose sum is 1, and
;; G_n = 3/2^(n+2), its corresponding geometric mean.

(defun putnam-2021-b2-star-a (n)
  (/ 3 (expt 4 (+ (nfix n) 1))))

(defun putnam-2021-b2-star-g (n)
  (/ 3 (expt 2 (+ (nfix n) 2))))

(defun putnam-2021-b2-star-a-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- (nfix terms) 1)))
      (+ (putnam-2021-b2-star-a-prefix index)
         (putnam-2021-b2-star-a index)))))

(defun putnam-2021-b2-star-a-product (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      1
    (let ((index (- (nfix terms) 1)))
      (* (putnam-2021-b2-star-a-product index)
         (putnam-2021-b2-star-a index)))))

(defun putnam-2021-b2-star-weighted-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- (nfix terms) 1))
           (n (+ index 1)))
      (+
       (putnam-2021-b2-star-weighted-prefix index)
       (*
        (/ n (expt 2 n))
        (putnam-2021-b2-star-g index))))))

(defun-sk putnam-2021-b2-star-nonnegative-p ()
  (forall (n)
    (implies
     (natp n)
     (<= 0 (putnam-2021-b2-star-a n)))))

(defun-sk putnam-2021-b2-star-sum-tail-p
    (epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (<
      (abs
       (- (putnam-2021-b2-star-a-prefix terms)
          1))
      epsilon))))

(defun-sk putnam-2021-b2-star-sum-cutoff-exists-p
    (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2021-b2-star-sum-tail-p
      epsilon cutoff))))

(defun-sk putnam-2021-b2-star-sums-to-one-p ()
  (forall (epsilon)
    (implies
     (putnam-2021-b2-positive-rational-p epsilon)
     (putnam-2021-b2-star-sum-cutoff-exists-p
      epsilon))))

(defun-sk putnam-2021-b2-star-roots-p ()
  (forall (n)
    (implies
     (natp n)
     (and
      (<= 0 (putnam-2021-b2-star-g n))
      (equal
       (expt
        (putnam-2021-b2-star-g n)
        (+ n 1))
       (putnam-2021-b2-star-a-product
        (+ n 1)))))))

(defun-sk putnam-2021-b2-star-series-tail-p
    (epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (<
      (abs
       (-
        (putnam-2021-b2-star-weighted-prefix terms)
        2/3))
      epsilon))))

(defun-sk putnam-2021-b2-star-series-cutoff-exists-p
    (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2021-b2-star-series-tail-p
      epsilon cutoff))))

(defun-sk putnam-2021-b2-star-series-sums-to-two-thirds-p ()
  (forall (epsilon)
    (implies
     (putnam-2021-b2-positive-rational-p epsilon)
     (putnam-2021-b2-star-series-cutoff-exists-p
      epsilon))))

;; The first conjunct is attainment of 2/3. Since the DEFSTUB functions are
;; arbitrary, the implication is universally generic over every admissible
;; real sequence, its principal geometric means, and every represented series
;; value. Its conclusion states convergence and the universal upper bound.

(defun putnambench-putnam-2021-b2-statement ()
  (and
   (putnam-2021-b2-star-nonnegative-p)
   (putnam-2021-b2-star-sums-to-one-p)
   (putnam-2021-b2-star-roots-p)
   (putnam-2021-b2-star-series-sums-to-two-thirds-p)
   (implies
    (and
     (putnam-2021-b2-sequence-regular-p :a)
     (putnam-2021-b2-sequence-nonnegative-p :a)
     (putnam-2021-b2-sums-to-one-p)
     (putnam-2021-b2-sequence-regular-p :g)
     (putnam-2021-b2-sequence-nonnegative-p :g)
     (putnam-2021-b2-geometric-means-p))
    (and
     (putnam-2021-b2-series-cauchy-p)
     (implies
      (and
       (putnam-2021-b2-target-regular-p)
       (putnam-2021-b2-series-has-target-p))
      (putnam-2021-b2-target-at-most-two-thirds-p))))))

(value-triple :itpeval-statement-checked)
:q
