;; Statement-only formalization of PutnamBench corpus artifact putnam_1987_b4:
;; the real planar sine-cosine recurrence from (4/5, 3/5) converges coordinatewise
;; to (-1, 0). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; REAL-TYPE indexes an arbitrary presentation of an Archimedean ordered field.
;; Such a field has a unique order-preserving embedding into the real numbers.
;; Sine and cosine are fixed, rather than assumed opaque, by convergence of
;; their complete power series.  The two conservative sequence interfaces are
;; arbitrary functions on the natural numbers; all typing, recurrence, and
;; convergence conditions occur explicitly in the statement predicate.

(defstub putnam-1987-b4-member-p (real-type value) t)
(defstub putnam-1987-b4-zero (real-type) t)
(defstub putnam-1987-b4-one (real-type) t)
(defstub putnam-1987-b4-add (real-type left right) t)
(defstub putnam-1987-b4-multiply (real-type left right) t)
(defstub putnam-1987-b4-negate (real-type value) t)
(defstub putnam-1987-b4-inverse (real-type value) t)
(defstub putnam-1987-b4-less (real-type left right) t)
(defstub putnam-1987-b4-sine (real-type value) t)
(defstub putnam-1987-b4-cosine (real-type value) t)
(defstub putnam-1987-b4-x (real-type index) t)
(defstub putnam-1987-b4-y (real-type index) t)

(defun putnam-1987-b4-r-add (real-type left right)
  (putnam-1987-b4-add real-type left right))

(defun putnam-1987-b4-r-multiply (real-type left right)
  (putnam-1987-b4-multiply real-type left right))

(defun putnam-1987-b4-r-negate (real-type value)
  (putnam-1987-b4-negate real-type value))

(defun putnam-1987-b4-r-inverse (real-type value)
  (putnam-1987-b4-inverse real-type value))

(defun putnam-1987-b4-r-subtract (real-type left right)
  (putnam-1987-b4-r-add
   real-type
   left
   (putnam-1987-b4-r-negate real-type right)))

(defun putnam-1987-b4-r-divide (real-type numerator denominator)
  (putnam-1987-b4-r-multiply
   real-type
   numerator
   (putnam-1987-b4-r-inverse real-type denominator)))

(defun putnam-1987-b4-r-absolute-value (real-type value)
  (if (putnam-1987-b4-less
       real-type value (putnam-1987-b4-zero real-type))
      (putnam-1987-b4-r-negate real-type value)
    value))

(defun putnam-1987-b4-r-nat (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-1987-b4-zero real-type)
    (putnam-1987-b4-r-add
     real-type
     (putnam-1987-b4-one real-type)
     (putnam-1987-b4-r-nat real-type (1- n)))))

(defun putnam-1987-b4-r-power (real-type base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (putnam-1987-b4-one real-type)
    (putnam-1987-b4-r-multiply
     real-type
     base
     (putnam-1987-b4-r-power
      real-type base (1- exponent)))))

(defun putnam-1987-b4-r-factorial (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-1987-b4-one real-type)
    (putnam-1987-b4-r-multiply
     real-type
     (putnam-1987-b4-r-nat real-type n)
     (putnam-1987-b4-r-factorial
      real-type (1- n)))))

(defun-sk putnam-1987-b4-field-laws-p (real-type)
  (forall (a b c)
    (implies
     (and
      (putnam-1987-b4-member-p real-type a)
      (putnam-1987-b4-member-p real-type b)
      (putnam-1987-b4-member-p real-type c))
     (let* ((zero (putnam-1987-b4-zero real-type))
            (one (putnam-1987-b4-one real-type))
            (a-plus-b
             (putnam-1987-b4-r-add real-type a b))
            (b-plus-c
             (putnam-1987-b4-r-add real-type b c))
            (a-times-b
             (putnam-1987-b4-r-multiply real-type a b))
            (b-times-c
             (putnam-1987-b4-r-multiply real-type b c))
            (negative-a
             (putnam-1987-b4-r-negate real-type a))
            (inverse-a
             (putnam-1987-b4-r-inverse real-type a)))
       (and
        (putnam-1987-b4-member-p real-type a-plus-b)
        (putnam-1987-b4-member-p real-type a-times-b)
        (putnam-1987-b4-member-p real-type negative-a)
        (putnam-1987-b4-member-p real-type inverse-a)
        (equal
         (putnam-1987-b4-r-add real-type a-plus-b c)
         (putnam-1987-b4-r-add real-type a b-plus-c))
        (equal
         a-plus-b
         (putnam-1987-b4-r-add real-type b a))
        (equal
         (putnam-1987-b4-r-add real-type a zero)
         a)
        (equal
         (putnam-1987-b4-r-add real-type a negative-a)
         zero)
        (equal
         (putnam-1987-b4-r-multiply real-type a-times-b c)
         (putnam-1987-b4-r-multiply real-type a b-times-c))
        (equal
         a-times-b
         (putnam-1987-b4-r-multiply real-type b a))
        (equal
         (putnam-1987-b4-r-multiply real-type a one)
         a)
        (implies
         (equal a zero)
         (equal inverse-a zero))
        (implies
         (not (equal a zero))
         (equal
          (putnam-1987-b4-r-multiply
           real-type a inverse-a)
          one))
        (equal
         (putnam-1987-b4-r-multiply real-type a b-plus-c)
         (putnam-1987-b4-r-add
          real-type
          (putnam-1987-b4-r-multiply real-type a b)
          (putnam-1987-b4-r-multiply real-type a c))))))))

(defun-sk putnam-1987-b4-order-laws-p (real-type)
  (forall (a b c)
    (implies
     (and
      (putnam-1987-b4-member-p real-type a)
      (putnam-1987-b4-member-p real-type b)
      (putnam-1987-b4-member-p real-type c))
     (let ((zero (putnam-1987-b4-zero real-type)))
       (and
        (not (putnam-1987-b4-less real-type a a))
        (or
         (equal a b)
         (putnam-1987-b4-less real-type a b)
         (putnam-1987-b4-less real-type b a))
        (implies
         (and
          (putnam-1987-b4-less real-type a b)
          (putnam-1987-b4-less real-type b c))
         (putnam-1987-b4-less real-type a c))
        (implies
         (putnam-1987-b4-less real-type a b)
         (putnam-1987-b4-less
          real-type
          (putnam-1987-b4-r-add real-type a c)
          (putnam-1987-b4-r-add real-type b c)))
        (implies
         (and
          (putnam-1987-b4-less real-type zero a)
          (putnam-1987-b4-less real-type zero b))
         (putnam-1987-b4-less
          real-type
          zero
          (putnam-1987-b4-r-multiply real-type a b))))))))

(defun-sk putnam-1987-b4-archimedean-bound-exists-p
    (real-type value)
  (exists (n)
    (and
     (natp n)
     (putnam-1987-b4-less
      real-type
      value
      (putnam-1987-b4-r-nat real-type n)))))

(defun-sk putnam-1987-b4-archimedean-p (real-type)
  (forall (value)
    (implies
     (putnam-1987-b4-member-p real-type value)
     (putnam-1987-b4-archimedean-bound-exists-p
      real-type value))))

(defun putnam-1987-b4-real-field-p (real-type)
  (let ((zero (putnam-1987-b4-zero real-type))
        (one (putnam-1987-b4-one real-type)))
    (and
     (putnam-1987-b4-member-p real-type zero)
     (putnam-1987-b4-member-p real-type one)
     (not (equal zero one))
     (putnam-1987-b4-field-laws-p real-type)
     (putnam-1987-b4-order-laws-p real-type)
     (putnam-1987-b4-less real-type zero one)
     (putnam-1987-b4-archimedean-p real-type))))

(defun putnam-1987-b4-sine-term (real-type x index)
  (let* ((exponent (+ (* 2 index) 1))
         (unsigned
          (putnam-1987-b4-r-divide
           real-type
           (putnam-1987-b4-r-power
            real-type x exponent)
           (putnam-1987-b4-r-factorial
            real-type exponent))))
    (if (equal (mod index 2) 0)
        unsigned
      (putnam-1987-b4-r-negate real-type unsigned))))

(defun putnam-1987-b4-cosine-term (real-type x index)
  (let* ((exponent (* 2 index))
         (unsigned
          (putnam-1987-b4-r-divide
           real-type
           (putnam-1987-b4-r-power
            real-type x exponent)
           (putnam-1987-b4-r-factorial
            real-type exponent))))
    (if (equal (mod index 2) 0)
        unsigned
      (putnam-1987-b4-r-negate real-type unsigned))))

(defun putnam-1987-b4-sine-prefix (real-type x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (putnam-1987-b4-zero real-type)
    (let ((index (1- terms)))
      (putnam-1987-b4-r-add
       real-type
       (putnam-1987-b4-sine-prefix real-type x index)
       (putnam-1987-b4-sine-term
        real-type x index)))))

(defun putnam-1987-b4-cosine-prefix (real-type x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (putnam-1987-b4-zero real-type)
    (let ((index (1- terms)))
      (putnam-1987-b4-r-add
       real-type
       (putnam-1987-b4-cosine-prefix real-type x index)
       (putnam-1987-b4-cosine-term
        real-type x index)))))

(defun-sk putnam-1987-b4-sine-tail-p
    (real-type x epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (putnam-1987-b4-less
      real-type
      (putnam-1987-b4-r-absolute-value
       real-type
       (putnam-1987-b4-r-subtract
        real-type
        (putnam-1987-b4-sine-prefix
         real-type x terms)
        (putnam-1987-b4-sine real-type x)))
      epsilon))))

(defun-sk putnam-1987-b4-sine-cutoff-exists-p
    (real-type x epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1987-b4-sine-tail-p
      real-type x epsilon cutoff))))

(defun-sk putnam-1987-b4-sine-series-p (real-type x)
  (forall (epsilon)
    (implies
     (and
      (putnam-1987-b4-member-p real-type epsilon)
      (putnam-1987-b4-less
       real-type
       (putnam-1987-b4-zero real-type)
       epsilon))
     (putnam-1987-b4-sine-cutoff-exists-p
      real-type x epsilon))))

(defun-sk putnam-1987-b4-cosine-tail-p
    (real-type x epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (putnam-1987-b4-less
      real-type
      (putnam-1987-b4-r-absolute-value
       real-type
       (putnam-1987-b4-r-subtract
        real-type
        (putnam-1987-b4-cosine-prefix
         real-type x terms)
        (putnam-1987-b4-cosine real-type x)))
      epsilon))))

(defun-sk putnam-1987-b4-cosine-cutoff-exists-p
    (real-type x epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1987-b4-cosine-tail-p
      real-type x epsilon cutoff))))

(defun-sk putnam-1987-b4-cosine-series-p (real-type x)
  (forall (epsilon)
    (implies
     (and
      (putnam-1987-b4-member-p real-type epsilon)
      (putnam-1987-b4-less
       real-type
       (putnam-1987-b4-zero real-type)
       epsilon))
     (putnam-1987-b4-cosine-cutoff-exists-p
      real-type x epsilon))))

(defun-sk putnam-1987-b4-trigonometric-laws-p (real-type)
  (forall (x)
    (implies
     (putnam-1987-b4-member-p real-type x)
     (and
      (putnam-1987-b4-member-p
       real-type (putnam-1987-b4-sine real-type x))
      (putnam-1987-b4-member-p
       real-type (putnam-1987-b4-cosine real-type x))
      (putnam-1987-b4-sine-series-p real-type x)
      (putnam-1987-b4-cosine-series-p real-type x)))))

(defun-sk putnam-1987-b4-sequences-typed-p (real-type)
  (forall (n)
    (implies
     (natp n)
     (and
      (putnam-1987-b4-member-p
       real-type (putnam-1987-b4-x real-type n))
      (putnam-1987-b4-member-p
       real-type (putnam-1987-b4-y real-type n))))))

(defun putnam-1987-b4-four-fifths (real-type)
  (putnam-1987-b4-r-divide
   real-type
   (putnam-1987-b4-r-nat real-type 4)
   (putnam-1987-b4-r-nat real-type 5)))

(defun putnam-1987-b4-three-fifths (real-type)
  (putnam-1987-b4-r-divide
   real-type
   (putnam-1987-b4-r-nat real-type 3)
   (putnam-1987-b4-r-nat real-type 5)))

(defun putnam-1987-b4-initial-values-p (real-type)
  (and
   (equal
    (putnam-1987-b4-x real-type 1)
    (putnam-1987-b4-four-fifths real-type))
   (equal
    (putnam-1987-b4-y real-type 1)
    (putnam-1987-b4-three-fifths real-type))))

(defun-sk putnam-1987-b4-recurrence-p (real-type)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= 1 n))
     (let* ((xn (putnam-1987-b4-x real-type n))
            (yn (putnam-1987-b4-y real-type n))
            (sin-yn
             (putnam-1987-b4-sine real-type yn))
            (cos-yn
             (putnam-1987-b4-cosine real-type yn)))
       (and
        (equal
         (putnam-1987-b4-x real-type (+ 1 n))
         (putnam-1987-b4-r-subtract
          real-type
          (putnam-1987-b4-r-multiply
           real-type xn cos-yn)
          (putnam-1987-b4-r-multiply
           real-type yn sin-yn)))
        (equal
         (putnam-1987-b4-y real-type (+ 1 n))
         (putnam-1987-b4-r-add
          real-type
          (putnam-1987-b4-r-multiply
           real-type xn sin-yn)
          (putnam-1987-b4-r-multiply
           real-type yn cos-yn))))))))

(defun putnam-1987-b4-sequence-value
    (real-type coordinate n)
  (if (equal coordinate :x)
      (putnam-1987-b4-x real-type n)
    (putnam-1987-b4-y real-type n)))

(defun-sk putnam-1987-b4-limit-tail-p
    (real-type coordinate limit epsilon start)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= start n))
     (putnam-1987-b4-less
      real-type
      (putnam-1987-b4-r-absolute-value
       real-type
       (putnam-1987-b4-r-subtract
        real-type
        (putnam-1987-b4-sequence-value
         real-type coordinate n)
        limit))
      epsilon))))

(defun-sk putnam-1987-b4-limit-start-exists-p
    (real-type coordinate limit epsilon)
  (exists (start)
    (and
     (natp start)
     (putnam-1987-b4-limit-tail-p
      real-type coordinate limit epsilon start))))

(defun-sk putnam-1987-b4-converges-p
    (real-type coordinate limit)
  (forall (epsilon)
    (implies
     (and
      (putnam-1987-b4-member-p real-type epsilon)
      (putnam-1987-b4-less
       real-type
       (putnam-1987-b4-zero real-type)
       epsilon))
     (putnam-1987-b4-limit-start-exists-p
      real-type coordinate limit epsilon))))

(defun putnambench-putnam-1987-b4-statement (real-type)
  (implies
   (and
    (putnam-1987-b4-real-field-p real-type)
    (putnam-1987-b4-trigonometric-laws-p real-type)
    (putnam-1987-b4-sequences-typed-p real-type)
    (putnam-1987-b4-initial-values-p real-type)
    (putnam-1987-b4-recurrence-p real-type))
   (and
    (putnam-1987-b4-converges-p
     real-type
     :x
     (putnam-1987-b4-r-negate
      real-type (putnam-1987-b4-one real-type)))
    (putnam-1987-b4-converges-p
     real-type
     :y
     (putnam-1987-b4-zero real-type)))))

(value-triple :itpeval-statement-checked)
:q
