;; Statement-only formalization of PutnamBench corpus artifact putnam_1982_b3:
;; if p_n is the probability that the sum of two independent uniform choices
;; from 1 through n is a perfect square, then p_n*sqrt(n) converges to
;; (4/3)*(sqrt(2)-1). This file contains no proof or error-bound construction.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Standard ACL2 has no primitive carrier for arbitrary real values. These
;; conservative interfaces describe a complete Archimedean ordered field,
;; hence the real field up to ordered-field isomorphism.

(defstub putnam-1982-b3-real-p (real-type value) t)
(defstub putnam-1982-b3-zero (real-type) t)
(defstub putnam-1982-b3-one (real-type) t)
(defstub putnam-1982-b3-add (real-type left right) t)
(defstub putnam-1982-b3-mul (real-type left right) t)
(defstub putnam-1982-b3-neg (real-type value) t)
(defstub putnam-1982-b3-inv (real-type value) t)
(defstub putnam-1982-b3-less (real-type left right) t)
(defstub putnam-1982-b3-integer-embed (real-type value) t)
(defstub putnam-1982-b3-supremum (real-type set) t)
(defstub putnam-1982-b3-sqrt (real-type value) t)

(defun putnam-1982-b3-leq (real-type left right)
  (not (putnam-1982-b3-less real-type right left)))

(defun putnam-1982-b3-sub (real-type left right)
  (putnam-1982-b3-add
   real-type left (putnam-1982-b3-neg real-type right)))

(defun putnam-1982-b3-div (real-type numerator denominator)
  (putnam-1982-b3-mul
   real-type numerator (putnam-1982-b3-inv real-type denominator)))

(defun putnam-1982-b3-abs (real-type value)
  (if (putnam-1982-b3-less
       real-type value (putnam-1982-b3-zero real-type))
      (putnam-1982-b3-neg real-type value)
    value))

(defun putnam-1982-b3-real-set-member-p (set value)
  (if (apply$ set (list value)) t nil))

(defun-sk putnam-1982-b3-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1982-b3-real-p real-type x)
      (putnam-1982-b3-real-p real-type y)
      (putnam-1982-b3-real-p real-type z))
     (let* ((zero (putnam-1982-b3-zero real-type))
            (one (putnam-1982-b3-one real-type))
            (x-plus-y (putnam-1982-b3-add real-type x y))
            (y-plus-z (putnam-1982-b3-add real-type y z))
            (x-times-y (putnam-1982-b3-mul real-type x y))
            (y-times-z (putnam-1982-b3-mul real-type y z))
            (minus-x (putnam-1982-b3-neg real-type x))
            (inverse-x (putnam-1982-b3-inv real-type x)))
       (and
        (putnam-1982-b3-real-p real-type x-plus-y)
        (putnam-1982-b3-real-p real-type x-times-y)
        (putnam-1982-b3-real-p real-type minus-x)
        (putnam-1982-b3-real-p real-type inverse-x)
        (equal
         (putnam-1982-b3-add real-type x-plus-y z)
         (putnam-1982-b3-add real-type x y-plus-z))
        (equal x-plus-y (putnam-1982-b3-add real-type y x))
        (equal (putnam-1982-b3-add real-type x zero) x)
        (equal (putnam-1982-b3-add real-type x minus-x) zero)
        (equal
         (putnam-1982-b3-mul real-type x-times-y z)
         (putnam-1982-b3-mul real-type x y-times-z))
        (equal x-times-y (putnam-1982-b3-mul real-type y x))
        (equal (putnam-1982-b3-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1982-b3-mul real-type x inverse-x)
          one))
        (equal
         (putnam-1982-b3-mul real-type x y-plus-z)
         (putnam-1982-b3-add
          real-type
          (putnam-1982-b3-mul real-type x y)
          (putnam-1982-b3-mul real-type x z))))))))

(defun-sk putnam-1982-b3-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1982-b3-real-p real-type x)
      (putnam-1982-b3-real-p real-type y)
      (putnam-1982-b3-real-p real-type z))
     (let ((zero (putnam-1982-b3-zero real-type)))
       (and
        (not (putnam-1982-b3-less real-type x x))
        (or
         (putnam-1982-b3-less real-type x y)
         (equal x y)
         (putnam-1982-b3-less real-type y x))
        (implies
         (and
          (putnam-1982-b3-less real-type x y)
          (putnam-1982-b3-less real-type y z))
         (putnam-1982-b3-less real-type x z))
        (implies
         (putnam-1982-b3-less real-type x y)
         (putnam-1982-b3-less
          real-type
          (putnam-1982-b3-add real-type x z)
          (putnam-1982-b3-add real-type y z)))
        (implies
         (and
          (putnam-1982-b3-less real-type zero x)
          (putnam-1982-b3-less real-type zero y))
         (putnam-1982-b3-less
          real-type
          zero
          (putnam-1982-b3-mul real-type x y))))))))

(defun-sk putnam-1982-b3-integer-embedding-laws-p (real-type)
  (forall (m n)
    (implies
     (and (integerp m) (integerp n))
     (and
      (putnam-1982-b3-real-p
       real-type
       (putnam-1982-b3-integer-embed real-type m))
      (equal
       (putnam-1982-b3-integer-embed real-type (+ m n))
       (putnam-1982-b3-add
        real-type
        (putnam-1982-b3-integer-embed real-type m)
        (putnam-1982-b3-integer-embed real-type n)))
      (equal
       (putnam-1982-b3-integer-embed real-type (* m n))
       (putnam-1982-b3-mul
        real-type
        (putnam-1982-b3-integer-embed real-type m)
        (putnam-1982-b3-integer-embed real-type n)))
      (iff
       (< m n)
       (putnam-1982-b3-less
        real-type
        (putnam-1982-b3-integer-embed real-type m)
        (putnam-1982-b3-integer-embed real-type n)))))))

(defun-sk putnam-1982-b3-valid-real-set-p (real-type set)
  (forall (value)
    (implies
     (putnam-1982-b3-real-set-member-p set value)
     (putnam-1982-b3-real-p real-type value))))

(defun-sk putnam-1982-b3-upper-bound-p (real-type set upper)
  (forall (value)
    (implies
     (and
      (putnam-1982-b3-real-p real-type value)
      (putnam-1982-b3-real-set-member-p set value))
     (putnam-1982-b3-leq real-type value upper))))

(defun-sk putnam-1982-b3-real-set-nonempty-p (real-type set)
  (exists (value)
    (and
     (putnam-1982-b3-real-p real-type value)
     (putnam-1982-b3-real-set-member-p set value))))

(defun-sk putnam-1982-b3-real-set-bounded-p (real-type set)
  (exists (upper)
    (and
     (putnam-1982-b3-real-p real-type upper)
     (putnam-1982-b3-upper-bound-p real-type set upper))))

(defun-sk putnam-1982-b3-least-upper-bound-p
    (real-type set supremum)
  (forall (upper)
    (implies
     (and
      (putnam-1982-b3-real-p real-type upper)
      (putnam-1982-b3-upper-bound-p real-type set upper))
     (putnam-1982-b3-leq real-type supremum upper))))

(defun-sk putnam-1982-b3-completeness-p (real-type)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1982-b3-valid-real-set-p real-type set)
      (putnam-1982-b3-real-set-nonempty-p real-type set)
      (putnam-1982-b3-real-set-bounded-p real-type set))
     (let ((supremum
            (putnam-1982-b3-supremum real-type set)))
       (and
        (putnam-1982-b3-real-p real-type supremum)
        (putnam-1982-b3-upper-bound-p
         real-type set supremum)
        (putnam-1982-b3-least-upper-bound-p
         real-type set supremum))))))

(defun-sk putnam-1982-b3-archimedean-witness-p
    (real-type value)
  (exists (n)
    (and
     (natp n)
     (putnam-1982-b3-less
      real-type
      value
      (putnam-1982-b3-integer-embed real-type n)))))

(defun-sk putnam-1982-b3-archimedean-p (real-type)
  (forall (value)
    (implies
     (putnam-1982-b3-real-p real-type value)
     (putnam-1982-b3-archimedean-witness-p
      real-type value))))

(defun putnam-1982-b3-real-field-p (real-type)
  (let ((zero (putnam-1982-b3-zero real-type))
        (one (putnam-1982-b3-one real-type)))
    (and
     (putnam-1982-b3-real-p real-type zero)
     (putnam-1982-b3-real-p real-type one)
     (not (equal zero one))
     (putnam-1982-b3-field-laws-p real-type)
     (putnam-1982-b3-order-laws-p real-type)
     (putnam-1982-b3-less real-type zero one)
     (equal
      (putnam-1982-b3-integer-embed real-type 0)
      zero)
     (equal
      (putnam-1982-b3-integer-embed real-type 1)
      one)
     (putnam-1982-b3-integer-embedding-laws-p real-type)
     (putnam-1982-b3-completeness-p real-type)
     (putnam-1982-b3-archimedean-p real-type))))

;; The square-root operation is the exact nonnegative square root on
;; nonnegative carrier values; no rational approximation is involved.

(defun-sk putnam-1982-b3-sqrt-laws-p (real-type)
  (forall (x)
    (implies
     (and
      (putnam-1982-b3-real-p real-type x)
      (putnam-1982-b3-leq
       real-type (putnam-1982-b3-zero real-type) x))
     (let ((root (putnam-1982-b3-sqrt real-type x)))
       (and
        (putnam-1982-b3-real-p real-type root)
        (putnam-1982-b3-leq
         real-type (putnam-1982-b3-zero real-type) root)
        (equal
         (putnam-1982-b3-mul real-type root root)
         x))))))

;; Exact finite cardinality of ordered pairs (c,d) in {1,...,n}^2 whose sum
;; is a square.

(defun putnam-1982-b3-isqrt-search (x candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp x))
          (not (natp candidate)))
      0
    (if (<= (* candidate candidate) x)
        candidate
      (putnam-1982-b3-isqrt-search
       x (- candidate 1)))))

(defun putnam-1982-b3-isqrt (x)
  (if (natp x)
      (putnam-1982-b3-isqrt-search x x)
    0))

(defun putnam-1982-b3-pairs-with-sum (n sum)
  (if (and
       (natp n)
       (natp sum)
       (<= 2 sum)
       (<= sum (* 2 n)))
      (if (<= sum (+ n 1))
          (- sum 1)
        (+ (- (* 2 n) sum) 1))
    0))

(defun putnam-1982-b3-square-sum-count-through (n k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      0
    (+
     (putnam-1982-b3-pairs-with-sum n (* k k))
     (putnam-1982-b3-square-sum-count-through
      n (- k 1)))))

(defun putnam-1982-b3-square-sum-count (n)
  (if (natp n)
      (putnam-1982-b3-square-sum-count-through
       n (putnam-1982-b3-isqrt (* 2 n)))
    0))

(defun putnam-1982-b3-probability (real-type n)
  (let* ((n-real
          (putnam-1982-b3-integer-embed real-type n))
         (count-real
          (putnam-1982-b3-integer-embed
           real-type
           (putnam-1982-b3-square-sum-count n))))
    (putnam-1982-b3-div
     real-type
     count-real
     (putnam-1982-b3-mul real-type n-real n-real))))

(defun putnam-1982-b3-sequence-value (real-type n)
  (putnam-1982-b3-mul
   real-type
   (putnam-1982-b3-probability real-type n)
   (putnam-1982-b3-sqrt
    real-type
    (putnam-1982-b3-integer-embed real-type n))))

(defun putnam-1982-b3-solution (real-type)
  (let ((one
         (putnam-1982-b3-integer-embed real-type 1))
        (two
         (putnam-1982-b3-integer-embed real-type 2))
        (three
         (putnam-1982-b3-integer-embed real-type 3))
        (four
         (putnam-1982-b3-integer-embed real-type 4)))
    (putnam-1982-b3-mul
     real-type
     (putnam-1982-b3-div real-type four three)
     (putnam-1982-b3-sub
      real-type
      (putnam-1982-b3-sqrt real-type two)
      one))))

;; Literal epsilon-N convergence of the exact source sequence.

(defun-sk putnam-1982-b3-tail-p
    (real-type epsilon cutoff)
  (forall (n)
    (implies
     (and (natp n) (<= cutoff n))
     (putnam-1982-b3-less
      real-type
      (putnam-1982-b3-abs
       real-type
       (putnam-1982-b3-sub
        real-type
        (putnam-1982-b3-sequence-value real-type n)
        (putnam-1982-b3-solution real-type)))
      epsilon))))

(defun-sk putnam-1982-b3-cutoff-exists-p
    (real-type epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1982-b3-tail-p
      real-type epsilon cutoff))))

(defun-sk putnam-1982-b3-converges-p (real-type)
  (forall (epsilon)
    (implies
     (and
      (putnam-1982-b3-real-p real-type epsilon)
      (putnam-1982-b3-less
       real-type
       (putnam-1982-b3-zero real-type)
       epsilon))
     (putnam-1982-b3-cutoff-exists-p
      real-type epsilon))))

(defun putnambench-putnam-1982-b3-statement (real-type)
  (implies
   (and
    (putnam-1982-b3-real-field-p real-type)
    (putnam-1982-b3-sqrt-laws-p real-type))
   (putnam-1982-b3-converges-p real-type)))

(value-triple :itpeval-statement-checked)
:q
