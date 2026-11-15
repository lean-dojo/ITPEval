;; Statement-only formalization of PutnamBench corpus artifact putnam_2006_a5:
;; for positive odd n and irrational theta/pi, the sum-to-product ratio of
;; tan(theta + k*pi/n), k = 1,...,n, is n or -n according to n modulo 4.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; REAL-TYPE indexes an arbitrary presentation of an Archimedean ordered
;; field.  The conservative interfaces below supply no facts: all field,
;; order, pi, trigonometric, irrationality, and tangent-family conditions are
;; explicit in the statement predicate.  Pi is fixed by the convergent Machin
;; series, and sine and cosine are fixed by their complete power series.

(defstub p06a5-member-p (real-type value) t)
(defstub p06a5-zero (real-type) t)
(defstub p06a5-one (real-type) t)
(defstub p06a5-add (real-type left right) t)
(defstub p06a5-multiply (real-type left right) t)
(defstub p06a5-negate (real-type value) t)
(defstub p06a5-inverse (real-type value) t)
(defstub p06a5-less (real-type left right) t)
(defstub p06a5-pi (real-type) t)
(defstub p06a5-sine (real-type value) t)
(defstub p06a5-cosine (real-type value) t)
(defstub p06a5-a (real-type index) t)

(defun p06a5-r-add (real-type left right)
  (p06a5-add real-type left right))

(defun p06a5-r-multiply (real-type left right)
  (p06a5-multiply real-type left right))

(defun p06a5-r-negate (real-type value)
  (p06a5-negate real-type value))

(defun p06a5-r-inverse (real-type value)
  (p06a5-inverse real-type value))

(defun p06a5-r-subtract (real-type left right)
  (p06a5-r-add
   real-type
   left
   (p06a5-r-negate real-type right)))

(defun p06a5-r-divide (real-type numerator denominator)
  (p06a5-r-multiply
   real-type
   numerator
   (p06a5-r-inverse real-type denominator)))

(defun p06a5-r-absolute-value (real-type value)
  (if (p06a5-less real-type value (p06a5-zero real-type))
      (p06a5-r-negate real-type value)
    value))

(defun p06a5-r-nat (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p06a5-zero real-type)
    (p06a5-r-add
     real-type
     (p06a5-one real-type)
     (p06a5-r-nat real-type (1- n)))))

(defun p06a5-r-int (real-type integer)
  (if (and (integerp integer)
           (< integer 0))
      (p06a5-r-negate
       real-type
       (p06a5-r-nat real-type (- integer)))
    (p06a5-r-nat real-type integer)))

(defun p06a5-r-power (real-type base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (p06a5-one real-type)
    (p06a5-r-multiply
     real-type
     base
     (p06a5-r-power real-type base (1- exponent)))))

(defun p06a5-r-factorial (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p06a5-one real-type)
    (p06a5-r-multiply
     real-type
     (p06a5-r-nat real-type n)
     (p06a5-r-factorial real-type (1- n)))))

(defun-sk p06a5-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p06a5-member-p real-type x)
      (p06a5-member-p real-type y)
      (p06a5-member-p real-type z))
     (let* ((zero (p06a5-zero real-type))
            (one (p06a5-one real-type))
            (x-plus-y (p06a5-r-add real-type x y))
            (y-plus-z (p06a5-r-add real-type y z))
            (x-times-y (p06a5-r-multiply real-type x y))
            (y-times-z (p06a5-r-multiply real-type y z))
            (minus-x (p06a5-r-negate real-type x))
            (inverse-x (p06a5-r-inverse real-type x)))
       (and
        (p06a5-member-p real-type x-plus-y)
        (p06a5-member-p real-type x-times-y)
        (p06a5-member-p real-type minus-x)
        (p06a5-member-p real-type inverse-x)
        (equal
         (p06a5-r-add real-type x-plus-y z)
         (p06a5-r-add real-type x y-plus-z))
        (equal x-plus-y (p06a5-r-add real-type y x))
        (equal (p06a5-r-add real-type x zero) x)
        (equal (p06a5-r-add real-type x minus-x) zero)
        (equal
         (p06a5-r-multiply real-type x-times-y z)
         (p06a5-r-multiply real-type x y-times-z))
        (equal x-times-y (p06a5-r-multiply real-type y x))
        (equal (p06a5-r-multiply real-type x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (p06a5-r-multiply real-type x inverse-x)
          one))
        (equal
         (p06a5-r-multiply real-type x y-plus-z)
         (p06a5-r-add
          real-type
          (p06a5-r-multiply real-type x y)
          (p06a5-r-multiply real-type x z))))))))

(defun-sk p06a5-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p06a5-member-p real-type x)
      (p06a5-member-p real-type y)
      (p06a5-member-p real-type z))
     (let ((zero (p06a5-zero real-type)))
       (and
        (not (p06a5-less real-type x x))
        (or
         (p06a5-less real-type x y)
         (equal x y)
         (p06a5-less real-type y x))
        (implies
         (and
          (p06a5-less real-type x y)
          (p06a5-less real-type y z))
         (p06a5-less real-type x z))
        (implies
         (p06a5-less real-type x y)
         (p06a5-less
          real-type
          (p06a5-r-add real-type x z)
          (p06a5-r-add real-type y z)))
        (implies
         (and
          (p06a5-less real-type zero x)
          (p06a5-less real-type zero y))
         (p06a5-less
          real-type
          zero
          (p06a5-r-multiply real-type x y))))))))

(defun-sk p06a5-archimedean-bound-exists-p
    (real-type value)
  (exists (n)
    (and
     (natp n)
     (p06a5-less
      real-type
      value
      (p06a5-r-nat real-type n)))))

(defun-sk p06a5-archimedean-p (real-type)
  (forall (value)
    (implies
     (p06a5-member-p real-type value)
     (p06a5-archimedean-bound-exists-p
      real-type value))))

(defun p06a5-real-field-p (real-type)
  (let ((zero (p06a5-zero real-type))
        (one (p06a5-one real-type)))
    (and
     (p06a5-member-p real-type zero)
     (p06a5-member-p real-type one)
     (not (equal zero one))
     (p06a5-field-laws-p real-type)
     (p06a5-order-laws-p real-type)
     (p06a5-less real-type zero one)
     (p06a5-archimedean-p real-type))))

;; Machin's identity fixes the distinguished pi element exactly:
;; pi = 16*arctan(1/5) - 4*arctan(1/239).

(defun p06a5-arctan-prefix (real-type z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (p06a5-zero real-type)
    (let* ((index (1- terms))
           (exponent (+ (* 2 index) 1))
           (unsigned-term
            (p06a5-r-divide
             real-type
             (p06a5-r-power real-type z exponent)
             (p06a5-r-nat real-type exponent)))
           (term
            (if (equal (mod index 2) 0)
                unsigned-term
              (p06a5-r-negate real-type unsigned-term))))
      (p06a5-r-add
       real-type
       (p06a5-arctan-prefix real-type z index)
       term))))

(defun p06a5-pi-prefix (real-type terms)
  (let* ((one (p06a5-one real-type))
         (five (p06a5-r-nat real-type 5))
         (two-hundred-thirty-nine
          (p06a5-r-nat real-type 239))
         (sixteen (p06a5-r-nat real-type 16))
         (four (p06a5-r-nat real-type 4))
         (atan-one-fifth
          (p06a5-arctan-prefix
           real-type
           (p06a5-r-divide real-type one five)
           terms))
         (atan-one-over-two-hundred-thirty-nine
          (p06a5-arctan-prefix
           real-type
           (p06a5-r-divide
            real-type one two-hundred-thirty-nine)
           terms)))
    (p06a5-r-subtract
     real-type
     (p06a5-r-multiply real-type sixteen atan-one-fifth)
     (p06a5-r-multiply
      real-type four atan-one-over-two-hundred-thirty-nine))))

(defun-sk p06a5-pi-tail-p
    (real-type epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (p06a5-less
      real-type
      (p06a5-r-absolute-value
       real-type
       (p06a5-r-subtract
        real-type
        (p06a5-pi-prefix real-type terms)
        (p06a5-pi real-type)))
      epsilon))))

(defun-sk p06a5-pi-cutoff-exists-p
    (real-type epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p06a5-pi-tail-p real-type epsilon cutoff))))

(defun-sk p06a5-pi-converges-p (real-type)
  (forall (epsilon)
    (implies
     (and
      (p06a5-member-p real-type epsilon)
      (p06a5-less
       real-type (p06a5-zero real-type) epsilon))
     (p06a5-pi-cutoff-exists-p
      real-type epsilon))))

(defun p06a5-pi-value-p (real-type)
  (and
   (p06a5-member-p real-type (p06a5-pi real-type))
   (p06a5-less
    real-type
    (p06a5-zero real-type)
    (p06a5-pi real-type))
   (p06a5-pi-converges-p real-type)))

;; Sine and cosine are their full Taylor-series limits.

(defun p06a5-sine-term (real-type x index)
  (let* ((exponent (+ (* 2 index) 1))
         (unsigned
          (p06a5-r-divide
           real-type
           (p06a5-r-power real-type x exponent)
           (p06a5-r-factorial real-type exponent))))
    (if (equal (mod index 2) 0)
        unsigned
      (p06a5-r-negate real-type unsigned))))

(defun p06a5-cosine-term (real-type x index)
  (let* ((exponent (* 2 index))
         (unsigned
          (p06a5-r-divide
           real-type
           (p06a5-r-power real-type x exponent)
           (p06a5-r-factorial real-type exponent))))
    (if (equal (mod index 2) 0)
        unsigned
      (p06a5-r-negate real-type unsigned))))

(defun p06a5-sine-prefix (real-type x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (p06a5-zero real-type)
    (let ((index (1- terms)))
      (p06a5-r-add
       real-type
       (p06a5-sine-prefix real-type x index)
       (p06a5-sine-term real-type x index)))))

(defun p06a5-cosine-prefix (real-type x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (p06a5-zero real-type)
    (let ((index (1- terms)))
      (p06a5-r-add
       real-type
       (p06a5-cosine-prefix real-type x index)
       (p06a5-cosine-term real-type x index)))))

(defun-sk p06a5-sine-tail-p
    (real-type x epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (p06a5-less
      real-type
      (p06a5-r-absolute-value
       real-type
       (p06a5-r-subtract
        real-type
        (p06a5-sine-prefix real-type x terms)
        (p06a5-sine real-type x)))
      epsilon))))

(defun-sk p06a5-sine-cutoff-exists-p
    (real-type x epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p06a5-sine-tail-p
      real-type x epsilon cutoff))))

(defun-sk p06a5-sine-series-p (real-type x)
  (forall (epsilon)
    (implies
     (and
      (p06a5-member-p real-type epsilon)
      (p06a5-less
       real-type (p06a5-zero real-type) epsilon))
     (p06a5-sine-cutoff-exists-p
      real-type x epsilon))))

(defun-sk p06a5-cosine-tail-p
    (real-type x epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (p06a5-less
      real-type
      (p06a5-r-absolute-value
       real-type
       (p06a5-r-subtract
        real-type
        (p06a5-cosine-prefix real-type x terms)
        (p06a5-cosine real-type x)))
      epsilon))))

(defun-sk p06a5-cosine-cutoff-exists-p
    (real-type x epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p06a5-cosine-tail-p
      real-type x epsilon cutoff))))

(defun-sk p06a5-cosine-series-p (real-type x)
  (forall (epsilon)
    (implies
     (and
      (p06a5-member-p real-type epsilon)
      (p06a5-less
       real-type (p06a5-zero real-type) epsilon))
     (p06a5-cosine-cutoff-exists-p
      real-type x epsilon))))

(defun-sk p06a5-trigonometric-laws-p (real-type)
  (forall (x)
    (implies
     (p06a5-member-p real-type x)
     (and
      (p06a5-member-p
       real-type (p06a5-sine real-type x))
      (p06a5-member-p
       real-type (p06a5-cosine real-type x))
      (p06a5-sine-series-p real-type x)
      (p06a5-cosine-series-p real-type x)))))

(defun p06a5-tangent (real-type x)
  (p06a5-r-divide
   real-type
   (p06a5-sine real-type x)
   (p06a5-cosine real-type x)))

;; This is exactly theta/pi not being equal to any integer ratio p/q with
;; q nonzero; the existential witnesses remain internal to the predicate.

(defun-sk p06a5-rational-representation-exists-p
    (real-type value)
  (exists (numerator denominator)
    (and
     (integerp numerator)
     (integerp denominator)
     (not (equal denominator 0))
     (equal
      value
      (p06a5-r-divide
       real-type
       (p06a5-r-int real-type numerator)
       (p06a5-r-int real-type denominator))))))

(defun p06a5-irrational-p (real-type value)
  (not
   (p06a5-rational-representation-exists-p
    real-type value)))

(defun p06a5-angle (real-type n theta k)
  (p06a5-r-add
   real-type
   theta
   (p06a5-r-divide
    real-type
    (p06a5-r-multiply
     real-type
     (p06a5-r-nat real-type k)
     (p06a5-pi real-type))
    (p06a5-r-nat real-type n))))

(defun-sk p06a5-tangent-family-p
    (real-type n theta)
  (forall (k)
    (implies
     (and
      (natp k)
      (<= 1 k)
      (<= k n))
     (and
      (p06a5-member-p
       real-type (p06a5-a real-type k))
      (equal
       (p06a5-a real-type k)
       (p06a5-tangent
        real-type
        (p06a5-angle real-type n theta k)))))))

(defun p06a5-sum (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p06a5-zero real-type)
    (p06a5-r-add
     real-type
     (p06a5-sum real-type (1- n))
     (p06a5-a real-type n))))

(defun p06a5-product (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p06a5-one real-type)
    (p06a5-r-multiply
     real-type
     (p06a5-product real-type (1- n))
     (p06a5-a real-type n))))

(defun p06a5-solution (real-type n)
  (if (equal (mod n 4) 1)
      (p06a5-r-nat real-type n)
    (p06a5-r-negate
     real-type
     (p06a5-r-nat real-type n))))

(defun putnambench-putnam-2006-a5-statement
    (real-type n theta)
  (implies
   (and
    (p06a5-real-field-p real-type)
    (p06a5-pi-value-p real-type)
    (p06a5-trigonometric-laws-p real-type)
    (posp n)
    (oddp n)
    (p06a5-member-p real-type theta)
    (p06a5-irrational-p
     real-type
     (p06a5-r-divide
      real-type theta (p06a5-pi real-type)))
    (p06a5-tangent-family-p real-type n theta))
   (equal
    (p06a5-r-divide
     real-type
     (p06a5-sum real-type n)
     (p06a5-product real-type n))
    (p06a5-solution real-type n))))

(value-triple :itpeval-statement-checked)
:q
