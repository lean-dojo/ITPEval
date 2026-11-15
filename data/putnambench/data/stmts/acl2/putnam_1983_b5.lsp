;; Statement-only formalization of PutnamBench corpus artifact putnam_1983_b5:
;; the normalized integral of the distance from n/x to the nearest integer
;; converges to log(4/pi), assuming the Wallis product. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Ordinary ACL2 has no native irrational real numbers. These conservative
;; interfaces present an arbitrary Archimedean ordered field. Every field,
;; order, floor, integral, logarithm, and limit property used by the statement
;; is explicit below; no operation symbol supplies an unstated law.

(defstub p83b5-member-p (real-type value) t)
(defstub p83b5-zero (real-type) t)
(defstub p83b5-one (real-type) t)
(defstub p83b5-add (real-type left right) t)
(defstub p83b5-multiply (real-type left right) t)
(defstub p83b5-negate (real-type value) t)
(defstub p83b5-inverse (real-type value) t)
(defstub p83b5-less (real-type left right) t)
(defstub p83b5-floor (real-type value) t)
(defstub p83b5-integral-value (real-type n) t)
(defstub p83b5-pi (real-type) t)
(defstub p83b5-log-four-over-pi (real-type) t)

(defun p83b5-r-add (real-type left right)
  (p83b5-add real-type left right))

(defun p83b5-r-multiply (real-type left right)
  (p83b5-multiply real-type left right))

(defun p83b5-r-negate (real-type value)
  (p83b5-negate real-type value))

(defun p83b5-r-inverse (real-type value)
  (p83b5-inverse real-type value))

(defun p83b5-r-subtract (real-type left right)
  (p83b5-r-add
   real-type left (p83b5-r-negate real-type right)))

(defun p83b5-r-divide (real-type numerator denominator)
  (p83b5-r-multiply
   real-type numerator (p83b5-r-inverse real-type denominator)))

(defun p83b5-r-leq (real-type left right)
  (not (p83b5-less real-type right left)))

(defun p83b5-r-absolute-value (real-type value)
  (if (p83b5-less real-type value (p83b5-zero real-type))
      (p83b5-r-negate real-type value)
    value))

(defun p83b5-r-nat (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p83b5-zero real-type)
    (p83b5-r-add
     real-type
     (p83b5-one real-type)
     (p83b5-r-nat real-type (1- n)))))

(defun p83b5-r-int (real-type integer)
  (if (and (integerp integer) (< integer 0))
      (p83b5-r-negate
       real-type
       (p83b5-r-nat real-type (- integer)))
    (p83b5-r-nat real-type (nfix integer))))

(defun-sk p83b5-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p83b5-member-p real-type x)
      (p83b5-member-p real-type y)
      (p83b5-member-p real-type z))
     (let* ((zero (p83b5-zero real-type))
            (one (p83b5-one real-type))
            (xy-add (p83b5-r-add real-type x y))
            (yz-add (p83b5-r-add real-type y z))
            (xy-mul (p83b5-r-multiply real-type x y))
            (yz-mul (p83b5-r-multiply real-type y z))
            (neg-x (p83b5-r-negate real-type x))
            (inv-x (p83b5-r-inverse real-type x)))
       (and
        (p83b5-member-p real-type xy-add)
        (p83b5-member-p real-type xy-mul)
        (p83b5-member-p real-type neg-x)
        (p83b5-member-p real-type inv-x)
        (equal
         (p83b5-r-add real-type xy-add z)
         (p83b5-r-add real-type x yz-add))
        (equal xy-add (p83b5-r-add real-type y x))
        (equal (p83b5-r-add real-type x zero) x)
        (equal (p83b5-r-add real-type x neg-x) zero)
        (equal
         (p83b5-r-multiply real-type xy-mul z)
         (p83b5-r-multiply real-type x yz-mul))
        (equal xy-mul (p83b5-r-multiply real-type y x))
        (equal (p83b5-r-multiply real-type x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal
          (p83b5-r-multiply real-type x inv-x)
          one))
        (equal
         (p83b5-r-multiply real-type x yz-add)
         (p83b5-r-add
          real-type
          (p83b5-r-multiply real-type x y)
          (p83b5-r-multiply real-type x z))))))))

(defun-sk p83b5-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p83b5-member-p real-type x)
      (p83b5-member-p real-type y)
      (p83b5-member-p real-type z))
     (let ((zero (p83b5-zero real-type)))
       (and
        (not (p83b5-less real-type x x))
        (or
         (p83b5-less real-type x y)
         (equal x y)
         (p83b5-less real-type y x))
        (implies
         (and
          (p83b5-less real-type x y)
          (p83b5-less real-type y z))
         (p83b5-less real-type x z))
        (implies
         (p83b5-less real-type x y)
         (p83b5-less
          real-type
          (p83b5-r-add real-type x z)
          (p83b5-r-add real-type y z)))
        (implies
         (and
          (p83b5-less real-type zero x)
          (p83b5-less real-type zero y))
         (p83b5-less
          real-type
          zero
          (p83b5-r-multiply real-type x y))))))))

(defun-sk p83b5-archimedean-bound-exists-p
    (real-type value)
  (exists (n)
    (and
     (natp n)
     (p83b5-less
      real-type value (p83b5-r-nat real-type n)))))

(defun-sk p83b5-archimedean-p (real-type)
  (forall (value)
    (implies
     (p83b5-member-p real-type value)
     (p83b5-archimedean-bound-exists-p
      real-type value))))

(defun p83b5-real-field-p (real-type)
  (let ((zero (p83b5-zero real-type))
        (one (p83b5-one real-type)))
    (and
     (p83b5-member-p real-type zero)
     (p83b5-member-p real-type one)
     (not (equal zero one))
     (p83b5-field-laws-p real-type)
     (p83b5-order-laws-p real-type)
     (p83b5-less real-type zero one)
     (p83b5-archimedean-p real-type))))

;; FLOOR is characterized as the unique integer k with k <= x < k+1.
(defun-sk p83b5-floor-laws-p (real-type)
  (forall (x)
    (implies
     (p83b5-member-p real-type x)
     (let ((k (p83b5-floor real-type x)))
       (and
        (integerp k)
        (p83b5-r-leq
         real-type (p83b5-r-int real-type k) x)
        (p83b5-less
         real-type
         x
         (p83b5-r-int real-type (+ k 1))))))))

(defun p83b5-nearest-integer-distance (real-type x)
  (let* ((k (p83b5-floor real-type x))
         (lower
          (p83b5-r-subtract
           real-type x (p83b5-r-int real-type k)))
         (upper
          (p83b5-r-subtract
           real-type
           (p83b5-r-int real-type (+ k 1))
           x)))
    (if (p83b5-less real-type lower upper)
        lower
      upper)))

;; The source integral is retained directly. For each natural n its value is
;; characterized by convergence of uniform right Riemann sums for
;;
;;   x |-> dist(n/x, Z)
;;
;; on the oriented interval [1,n]. This continuous integrand has the same
;; Riemann and Lebesgue integral used by the ground-truth statements.
(defun p83b5-nearest-integrand (real-type n x)
  (p83b5-nearest-integer-distance
   real-type
   (p83b5-r-divide
    real-type (p83b5-r-nat real-type n) x)))

(defun p83b5-nearest-riemann-sum-aux
    (real-type n pieces count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (p83b5-zero real-type)
    (let* ((index (1- count))
           (left (p83b5-one real-type))
           (right (p83b5-r-nat real-type n))
           (step
            (p83b5-r-divide
             real-type
             (p83b5-r-subtract real-type right left)
             (p83b5-r-nat real-type pieces)))
           (tag
            (p83b5-r-add
             real-type
             left
             (p83b5-r-multiply
              real-type
              (p83b5-r-nat real-type (+ index 1))
              step))))
      (p83b5-r-add
       real-type
       (p83b5-nearest-riemann-sum-aux
        real-type n pieces index)
       (p83b5-r-multiply
        real-type
        (p83b5-nearest-integrand real-type n tag)
        step)))))

(defun p83b5-nearest-riemann-sum
    (real-type n pieces)
  (if (posp pieces)
      (p83b5-nearest-riemann-sum-aux
       real-type n pieces pieces)
    (p83b5-zero real-type)))

(defun p83b5-normalized-integral (real-type n)
  (p83b5-r-multiply
   real-type
   (p83b5-r-divide
    real-type
    (p83b5-one real-type)
    (p83b5-r-nat real-type n))
   (p83b5-integral-value real-type n)))

;; The target is not an opaque token: log(4/pi) is characterized by the
;; defining integral integral_1^(4/pi) 1/x dx, again through exact uniform
;; right Riemann sums.
(defun p83b5-log-integrand (real-type x)
  (p83b5-r-inverse real-type x))

(defun p83b5-log-riemann-sum-aux
    (real-type upper pieces count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (p83b5-zero real-type)
    (let* ((index (1- count))
           (left (p83b5-one real-type))
           (step
            (p83b5-r-divide
             real-type
             (p83b5-r-subtract real-type upper left)
             (p83b5-r-nat real-type pieces)))
           (tag
            (p83b5-r-add
             real-type
             left
             (p83b5-r-multiply
              real-type
              (p83b5-r-nat real-type (+ index 1))
              step))))
      (p83b5-r-add
       real-type
       (p83b5-log-riemann-sum-aux
        real-type upper pieces index)
       (p83b5-r-multiply
        real-type
        (p83b5-log-integrand real-type tag)
        step)))))

(defun p83b5-log-riemann-sum
    (real-type upper pieces)
  (if (posp pieces)
      (p83b5-log-riemann-sum-aux
       real-type upper pieces pieces)
    (p83b5-zero real-type)))

(defun p83b5-four-over-pi (real-type)
  (p83b5-r-divide
   real-type
   (p83b5-r-nat real-type 4)
   (p83b5-pi real-type)))

;; Finite Wallis products over k=1,...,N, exactly as in the source assumption.
(defun p83b5-wallis-factor (real-type index)
  (let* ((two-k
          (p83b5-r-multiply
           real-type
           (p83b5-r-nat real-type 2)
           (p83b5-r-nat real-type index)))
         (lower
          (p83b5-r-subtract
           real-type two-k (p83b5-one real-type)))
         (upper
          (p83b5-r-add
           real-type two-k (p83b5-one real-type))))
    (p83b5-r-multiply
     real-type
     (p83b5-r-divide real-type two-k lower)
     (p83b5-r-divide real-type two-k upper))))

(defun p83b5-wallis-product (real-type terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (p83b5-one real-type)
    (p83b5-r-multiply
     real-type
     (p83b5-wallis-product real-type (1- terms))
     (p83b5-wallis-factor real-type terms))))

;; The four sequence kinds below are concrete named sequences, not external
;; witnesses. Convergence has the source's full epsilon-N quantifier order.
(defun-sk p83b5-sequence-tail-p
    (real-type sequence-kind parameter limit epsilon cutoff)
  (forall (index)
    (implies
     (and
      (natp index)
      (natp cutoff)
      (<= cutoff index))
     (p83b5-less
      real-type
      (p83b5-r-absolute-value
       real-type
       (p83b5-r-subtract
        real-type
        (cond
         ((equal sequence-kind 'wallis)
          (p83b5-wallis-product real-type index))
         ((equal sequence-kind 'integral-sums)
          (p83b5-nearest-riemann-sum
           real-type parameter (+ 1 index)))
         ((equal sequence-kind 'log-sums)
          (p83b5-log-riemann-sum
           real-type parameter (+ 1 index)))
         (t
          (p83b5-normalized-integral real-type index)))
        limit))
      epsilon))))

(defun-sk p83b5-sequence-cutoff-exists-p
    (real-type sequence-kind parameter limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p83b5-sequence-tail-p
      real-type sequence-kind parameter limit epsilon cutoff))))

(defun-sk p83b5-converges-p
    (real-type sequence-kind parameter limit)
  (forall (epsilon)
    (implies
     (and
      (p83b5-member-p real-type epsilon)
      (p83b5-less
       real-type (p83b5-zero real-type) epsilon))
     (p83b5-sequence-cutoff-exists-p
      real-type sequence-kind parameter limit epsilon))))

(defun-sk p83b5-all-integral-values-p (real-type)
  (forall (n)
    (implies
     (natp n)
     (and
      (p83b5-member-p
       real-type (p83b5-integral-value real-type n))
      (p83b5-converges-p
       real-type
       'integral-sums
       n
       (p83b5-integral-value real-type n))))))

(defun p83b5-log-value-p (real-type)
  (and
   (p83b5-member-p
    real-type (p83b5-log-four-over-pi real-type))
   (p83b5-converges-p
    real-type
    'log-sums
    (p83b5-four-over-pi real-type)
    (p83b5-log-four-over-pi real-type))))

(defun p83b5-wallis-product-fact-p (real-type)
  (and
   (p83b5-member-p real-type (p83b5-pi real-type))
   (p83b5-converges-p
    real-type
    'wallis
    nil
    (p83b5-r-divide
     real-type
     (p83b5-pi real-type)
     (p83b5-r-nat real-type 2)))))

(defun putnambench-putnam-1983-b5-statement (real-type)
  (implies
   (and
    (p83b5-real-field-p real-type)
    (p83b5-floor-laws-p real-type)
    (p83b5-all-integral-values-p real-type)
    (p83b5-log-value-p real-type)
    (p83b5-wallis-product-fact-p real-type))
   (p83b5-converges-p
    real-type
    'normalized-integrals
    nil
    (p83b5-log-four-over-pi real-type))))

(value-triple :itpeval-statement-checked)
:q
