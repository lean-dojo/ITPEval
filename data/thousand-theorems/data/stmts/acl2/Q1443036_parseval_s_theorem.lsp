;; Statement-only formalization of thousand-theorems corpus artifact Q1443036,
;; "Parseval's theorem": for every complex L2 function on a positive-period
;; additive circle with normalized Haar measure, the sum over all integer
;; Fourier modes of the squared coefficient norms equals its L2 energy.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; ACL2 has no primitive complete real field, complex field, or Hilbert-space
;; sort.  The conservative interfaces below present those objects explicitly.
;; The source L2(AddCircle T) space is represented up to its canonical
;; basis-preserving isometric identification by a complex Hilbert space with a
;; complete Z-indexed orthonormal Fourier basis.  Under this identification,
;; the Fourier coefficient is the corresponding inner-product coordinate and
;; the integral of the pointwise squared norm is the squared Hilbert norm.

(defstub q1443036-member-p (type object) t)
(defstub q1443036-zero (type) t)
(defstub q1443036-one (type) t)
(defstub q1443036-add (type left right) t)
(defstub q1443036-multiply (type left right) t)
(defstub q1443036-negate (type object) t)
(defstub q1443036-inverse (type object) t)
(defstub q1443036-less (real-type left right) t)
(defstub q1443036-set-member-p (set object) t)

(defstub q1443036-of-real
  (real-type complex-type value) t)
(defstub q1443036-real-part
  (real-type complex-type value) t)
(defstub q1443036-imag-part
  (real-type complex-type value) t)
(defstub q1443036-imaginary-unit (complex-type) t)
(defstub q1443036-star (complex-type value) t)
(defstub q1443036-complex-norm-square
  (real-type complex-type value) t)

(defstub q1443036-smul
  (complex-type space scalar vector) t)
(defstub q1443036-inner
  (complex-type space left right) t)
(defstub q1443036-sequence-at
  (sequence index) t)
(defstub q1443036-basis-at
  (basis integer-index) t)

(defun q1443036-subtract (type left right)
  (q1443036-add
   type left (q1443036-negate type right)))

(defun q1443036-leq (real-type left right)
  (not (q1443036-less real-type right left)))

(defun q1443036-positive-p (real-type value)
  (and
   (q1443036-member-p real-type value)
   (q1443036-less
    real-type (q1443036-zero real-type) value)))

(defun q1443036-absolute (real-type value)
  (if (q1443036-less
       real-type value (q1443036-zero real-type))
      (q1443036-negate real-type value)
    value))

;; A Dedekind-complete ordered field presents the real numbers.

(defun-sk q1443036-field-laws-p (type)
  (forall (x y z)
    (implies
     (and
      (q1443036-member-p type x)
      (q1443036-member-p type y)
      (q1443036-member-p type z))
     (let* ((zero (q1443036-zero type))
            (one (q1443036-one type))
            (xy-add (q1443036-add type x y))
            (yz-add (q1443036-add type y z))
            (xy-mul (q1443036-multiply type x y))
            (yz-mul (q1443036-multiply type y z))
            (neg-x (q1443036-negate type x))
            (inv-x (q1443036-inverse type x)))
       (and
        (q1443036-member-p type zero)
        (q1443036-member-p type one)
        (q1443036-member-p type xy-add)
        (q1443036-member-p type xy-mul)
        (q1443036-member-p type neg-x)
        (q1443036-member-p type inv-x)
        (not (equal zero one))
        (equal
         (q1443036-add type xy-add z)
         (q1443036-add type x yz-add))
        (equal xy-add (q1443036-add type y x))
        (equal (q1443036-add type x zero) x)
        (equal (q1443036-add type x neg-x) zero)
        (equal
         (q1443036-multiply type xy-mul z)
         (q1443036-multiply type x yz-mul))
        (equal xy-mul (q1443036-multiply type y x))
        (equal (q1443036-multiply type x one) x)
        (equal (q1443036-multiply type x zero) zero)
        (equal (q1443036-inverse type zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q1443036-multiply type x inv-x)
          one))
        (equal
         (q1443036-multiply
          type x (q1443036-add type y z))
         (q1443036-add
          type
          (q1443036-multiply type x y)
          (q1443036-multiply type x z))))))))

(defun-sk q1443036-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q1443036-member-p real-type x)
      (q1443036-member-p real-type y)
      (q1443036-member-p real-type z))
     (let ((zero (q1443036-zero real-type)))
       (and
        (not (q1443036-less real-type x x))
        (or
         (equal x y)
         (q1443036-less real-type x y)
         (q1443036-less real-type y x))
        (implies
         (and
          (q1443036-less real-type x y)
          (q1443036-less real-type y z))
         (q1443036-less real-type x z))
        (implies
         (q1443036-less real-type x y)
         (q1443036-less
          real-type
          (q1443036-add real-type x z)
          (q1443036-add real-type y z)))
        (implies
         (and
          (q1443036-less real-type zero x)
          (q1443036-less real-type zero y))
         (q1443036-less
          real-type zero
          (q1443036-multiply real-type x y))))))))

(defun-sk q1443036-real-set-nonempty-p
    (real-type set)
  (exists (x)
    (and
     (q1443036-member-p real-type x)
     (q1443036-set-member-p set x))))

(defun-sk q1443036-real-upper-bound-p
    (real-type set bound)
  (forall (x)
    (implies
     (and
      (q1443036-member-p real-type x)
      (q1443036-set-member-p set x))
     (q1443036-leq real-type x bound))))

(defun-sk q1443036-real-bounded-above-p
    (real-type set)
  (exists (bound)
    (and
     (q1443036-member-p real-type bound)
     (q1443036-real-upper-bound-p
      real-type set bound))))

(defun-sk q1443036-real-least-upper-bound-p
    (real-type set supremum)
  (forall (bound)
    (and
     (q1443036-member-p real-type supremum)
     (q1443036-real-upper-bound-p
      real-type set supremum)
     (implies
      (and
       (q1443036-member-p real-type bound)
       (q1443036-real-upper-bound-p
        real-type set bound))
      (q1443036-leq real-type supremum bound)))))

(defun-sk q1443036-real-supremum-exists-p
    (real-type set)
  (exists (supremum)
    (q1443036-real-least-upper-bound-p
     real-type set supremum)))

(defun-sk q1443036-dedekind-complete-p (real-type)
  (forall (set)
    (implies
     (and
      (q1443036-real-set-nonempty-p real-type set)
      (q1443036-real-bounded-above-p real-type set))
     (q1443036-real-supremum-exists-p
      real-type set))))

(defun q1443036-real-field-p (real-type)
  (and
   (q1443036-field-laws-p real-type)
   (q1443036-order-laws-p real-type)
   (q1443036-less
    real-type
    (q1443036-zero real-type)
    (q1443036-one real-type))
   (q1443036-dedekind-complete-p real-type)))

;; Real coordinates and conjugation present the usual complex field over the
;; complete real field, rather than ACL2's smaller Gaussian-rational domain.

(defun-sk q1443036-complex-coordinate-laws-p
    (real-type complex-type)
  (forall (a b z)
    (implies
     (and
      (q1443036-member-p real-type a)
      (q1443036-member-p real-type b)
      (q1443036-member-p complex-type z))
     (let* ((zero-r (q1443036-zero real-type))
            (zero-c (q1443036-zero complex-type))
            (one-c (q1443036-one complex-type))
            (imaginary-unit
             (q1443036-imaginary-unit complex-type))
            (of-a
             (q1443036-of-real
              real-type complex-type a))
            (of-b
             (q1443036-of-real
              real-type complex-type b))
            (real-z
             (q1443036-real-part
              real-type complex-type z))
            (imag-z
             (q1443036-imag-part
              real-type complex-type z)))
       (and
        (q1443036-member-p complex-type of-a)
        (q1443036-member-p complex-type imaginary-unit)
        (q1443036-member-p real-type real-z)
        (q1443036-member-p real-type imag-z)
        (equal
         (q1443036-of-real
          real-type complex-type zero-r)
         zero-c)
        (equal
         (q1443036-of-real
          real-type complex-type
          (q1443036-one real-type))
         one-c)
        (equal
         (q1443036-of-real
          real-type complex-type
          (q1443036-add real-type a b))
         (q1443036-add complex-type of-a of-b))
        (equal
         (q1443036-of-real
          real-type complex-type
          (q1443036-multiply real-type a b))
         (q1443036-multiply complex-type of-a of-b))
        (equal
         (q1443036-multiply
          complex-type imaginary-unit imaginary-unit)
         (q1443036-negate complex-type one-c))
        (equal
         z
         (q1443036-add
          complex-type
          (q1443036-of-real
           real-type complex-type real-z)
          (q1443036-multiply
           complex-type imaginary-unit
           (q1443036-of-real
            real-type complex-type imag-z))))
        (equal
         (q1443036-real-part
          real-type complex-type
          (q1443036-add complex-type of-a
           (q1443036-multiply
            complex-type imaginary-unit of-b)))
         a)
        (equal
         (q1443036-imag-part
          real-type complex-type
          (q1443036-add complex-type of-a
           (q1443036-multiply
            complex-type imaginary-unit of-b)))
         b))))))

(defun-sk q1443036-complex-star-laws-p
    (real-type complex-type)
  (forall (x y)
    (implies
     (and
      (q1443036-member-p complex-type x)
      (q1443036-member-p complex-type y))
     (let ((star-x (q1443036-star complex-type x))
           (norm-square
            (q1443036-complex-norm-square
             real-type complex-type x)))
       (and
        (q1443036-member-p complex-type star-x)
        (q1443036-member-p real-type norm-square)
        (equal
         (q1443036-star
          complex-type (q1443036-star complex-type x))
         x)
        (equal
         (q1443036-star
          complex-type (q1443036-add complex-type x y))
         (q1443036-add
          complex-type
          (q1443036-star complex-type x)
          (q1443036-star complex-type y)))
        (equal
         (q1443036-star
          complex-type
          (q1443036-multiply complex-type x y))
         (q1443036-multiply
          complex-type
          (q1443036-star complex-type x)
          (q1443036-star complex-type y)))
        (equal
         (q1443036-star complex-type x)
         (q1443036-add
          complex-type
          (q1443036-of-real
           real-type complex-type
           (q1443036-real-part
            real-type complex-type x))
          (q1443036-negate
           complex-type
           (q1443036-multiply
            complex-type
            (q1443036-imaginary-unit complex-type)
            (q1443036-of-real
             real-type complex-type
             (q1443036-imag-part
              real-type complex-type x))))))
        (equal
         norm-square
         (q1443036-real-part
          real-type complex-type
          (q1443036-multiply
           complex-type star-x x)))
        (q1443036-leq
         real-type (q1443036-zero real-type) norm-square)
        (iff
         (equal norm-square (q1443036-zero real-type))
         (equal x (q1443036-zero complex-type))))))))

(defun q1443036-complex-field-p
    (real-type complex-type)
  (and
   (q1443036-real-field-p real-type)
   (q1443036-field-laws-p complex-type)
   (q1443036-complex-coordinate-laws-p
    real-type complex-type)
   (q1443036-complex-star-laws-p
    real-type complex-type)))

;; Complex Hilbert-space structure and sequential completeness.

(defun q1443036-vector-subtract
    (space left right)
  (q1443036-add
   space left (q1443036-negate space right)))

(defun q1443036-vector-norm-square
    (real-type complex-type space vector)
  (q1443036-real-part
   real-type complex-type
   (q1443036-inner
    complex-type space vector vector)))

(defun-sk q1443036-vector-space-laws-p
    (complex-type space)
  (forall (a b x y z)
    (implies
     (and
      (q1443036-member-p complex-type a)
      (q1443036-member-p complex-type b)
      (q1443036-member-p space x)
      (q1443036-member-p space y)
      (q1443036-member-p space z))
     (let ((zero (q1443036-zero space)))
       (and
        (q1443036-member-p
         space (q1443036-add space x y))
        (q1443036-member-p
         space (q1443036-negate space x))
        (q1443036-member-p
         space
         (q1443036-smul complex-type space a x))
        (equal
         (q1443036-add
          space (q1443036-add space x y) z)
         (q1443036-add
          space x (q1443036-add space y z)))
        (equal
         (q1443036-add space x y)
         (q1443036-add space y x))
        (equal (q1443036-add space x zero) x)
        (equal
         (q1443036-add
          space x (q1443036-negate space x))
         zero)
        (equal
         (q1443036-smul
          complex-type space
          (q1443036-one complex-type) x)
         x)
        (equal
         (q1443036-smul
          complex-type space
          (q1443036-multiply complex-type a b) x)
         (q1443036-smul
          complex-type space a
          (q1443036-smul
           complex-type space b x)))
        (equal
         (q1443036-smul
          complex-type space
          (q1443036-add complex-type a b) x)
         (q1443036-add
          space
          (q1443036-smul complex-type space a x)
          (q1443036-smul complex-type space b x)))
        (equal
         (q1443036-smul
          complex-type space a
          (q1443036-add space x y))
         (q1443036-add
          space
          (q1443036-smul complex-type space a x)
          (q1443036-smul complex-type space a y))))))))

(defun-sk q1443036-inner-product-laws-p
    (real-type complex-type space)
  (forall (a x y z)
    (implies
     (and
      (q1443036-member-p complex-type a)
      (q1443036-member-p space x)
      (q1443036-member-p space y)
      (q1443036-member-p space z))
     (let ((inner-xx
            (q1443036-inner complex-type space x x))
           (norm-square
            (q1443036-vector-norm-square
             real-type complex-type space x)))
       (and
        (q1443036-member-p complex-type inner-xx)
        (q1443036-member-p real-type norm-square)
        (equal
         (q1443036-inner
          complex-type space x
          (q1443036-add space y z))
         (q1443036-add
          complex-type
          (q1443036-inner complex-type space x y)
          (q1443036-inner complex-type space x z)))
        (equal
         (q1443036-inner
          complex-type space x
          (q1443036-smul complex-type space a y))
         (q1443036-multiply
          complex-type a
          (q1443036-inner complex-type space x y)))
        (equal
         (q1443036-inner complex-type space x y)
         (q1443036-star
          complex-type
          (q1443036-inner complex-type space y x)))
        (equal
         inner-xx
         (q1443036-of-real
          real-type complex-type norm-square))
        (q1443036-leq
         real-type (q1443036-zero real-type) norm-square)
        (iff
         (equal norm-square (q1443036-zero real-type))
         (equal x (q1443036-zero space))))))))

(defun q1443036-vector-distance-square
    (real-type complex-type space left right)
  (q1443036-vector-norm-square
   real-type complex-type space
   (q1443036-vector-subtract space left right)))

(defun-sk q1443036-sequence-values-p
    (space sequence)
  (forall (n)
    (implies
     (natp n)
     (q1443036-member-p
      space (q1443036-sequence-at sequence n)))))

(defun-sk q1443036-cauchy-tail-p
    (real-type complex-type space sequence
     epsilon cutoff)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (<= cutoff m)
      (<= cutoff n))
     (q1443036-less
      real-type
      (q1443036-vector-distance-square
       real-type complex-type space
       (q1443036-sequence-at sequence m)
       (q1443036-sequence-at sequence n))
      (q1443036-multiply
       real-type epsilon epsilon)))))

(defun-sk q1443036-cauchy-cutoff-exists-p
    (real-type complex-type space sequence epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q1443036-cauchy-tail-p
      real-type complex-type space sequence
      epsilon cutoff))))

(defun-sk q1443036-cauchy-sequence-p
    (real-type complex-type space sequence)
  (forall (epsilon)
    (implies
     (q1443036-positive-p real-type epsilon)
     (q1443036-cauchy-cutoff-exists-p
      real-type complex-type space
      sequence epsilon))))

(defun-sk q1443036-convergence-tail-p
    (real-type complex-type space sequence
     limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (q1443036-less
      real-type
      (q1443036-vector-distance-square
       real-type complex-type space
       (q1443036-sequence-at sequence n)
       limit)
      (q1443036-multiply
       real-type epsilon epsilon)))))

(defun-sk q1443036-convergence-cutoff-exists-p
    (real-type complex-type space sequence
     limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q1443036-convergence-tail-p
      real-type complex-type space sequence
      limit epsilon cutoff))))

(defun-sk q1443036-sequence-converges-p
    (real-type complex-type space sequence limit)
  (forall (epsilon)
    (implies
     (q1443036-positive-p real-type epsilon)
     (q1443036-convergence-cutoff-exists-p
      real-type complex-type space sequence
      limit epsilon))))

(defun-sk q1443036-sequence-limit-exists-p
    (real-type complex-type space sequence)
  (exists (limit)
    (and
     (q1443036-member-p space limit)
     (q1443036-sequence-converges-p
      real-type complex-type space sequence limit))))

(defun-sk q1443036-complete-p
    (real-type complex-type space)
  (forall (sequence)
    (implies
     (and
      (q1443036-sequence-values-p space sequence)
      (q1443036-cauchy-sequence-p
       real-type complex-type space sequence))
     (q1443036-sequence-limit-exists-p
      real-type complex-type space sequence))))

(defun q1443036-complex-hilbert-space-p
    (real-type complex-type space)
  (and
   (q1443036-member-p
    space (q1443036-zero space))
   (q1443036-vector-space-laws-p
    complex-type space)
   (q1443036-inner-product-laws-p
    real-type complex-type space)
   (q1443036-complete-p
    real-type complex-type space)))

;; The integer-indexed Fourier family is orthonormal and has dense finite
;; complex span, exactly the Hilbert-basis property used by the source.

(defun-sk q1443036-basis-values-p (space basis)
  (forall (index)
    (implies
     (integerp index)
     (q1443036-member-p
      space (q1443036-basis-at basis index)))))

(defun-sk q1443036-orthonormal-p
    (complex-type space basis)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index))
     (equal
      (q1443036-inner
       complex-type space
       (q1443036-basis-at basis left-index)
       (q1443036-basis-at basis right-index))
      (if (equal left-index right-index)
          (q1443036-one complex-type)
        (q1443036-zero complex-type))))))

(defun q1443036-integer-list-p (values)
  (if (consp values)
      (and
       (integerp (car values))
       (q1443036-integer-list-p (cdr values)))
    (equal values nil)))

(defun q1443036-scalar-list-p
    (complex-type values)
  (if (consp values)
      (and
       (q1443036-member-p complex-type (car values))
       (q1443036-scalar-list-p
        complex-type (cdr values)))
    (equal values nil)))

(defun q1443036-linear-combination
    (complex-type space basis
     indexes coefficients count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q1443036-zero space)
    (let ((position (- count 1)))
      (q1443036-add
       space
       (q1443036-linear-combination
        complex-type space basis
        indexes coefficients position)
       (q1443036-smul
        complex-type space
        (nth position coefficients)
        (q1443036-basis-at
         basis (nth position indexes)))))))

(defun-sk q1443036-dense-witness-exists-p
    (real-type complex-type space basis
     vector epsilon)
  (exists (count indexes coefficients)
    (and
     (natp count)
     (true-listp indexes)
     (true-listp coefficients)
     (equal (len indexes) count)
     (equal (len coefficients) count)
     (q1443036-integer-list-p indexes)
     (q1443036-scalar-list-p
      complex-type coefficients)
     (q1443036-less
      real-type
      (q1443036-vector-distance-square
       real-type complex-type space
       (q1443036-linear-combination
        complex-type space basis
        indexes coefficients count)
       vector)
      (q1443036-multiply
       real-type epsilon epsilon)))))

(defun-sk q1443036-dense-span-p
    (real-type complex-type space basis)
  (forall (vector epsilon)
    (implies
     (and
      (q1443036-member-p space vector)
      (q1443036-positive-p real-type epsilon))
     (q1443036-dense-witness-exists-p
      real-type complex-type space basis
      vector epsilon))))

(defun q1443036-fourier-basis-p
    (real-type complex-type space basis)
  (and
   (q1443036-basis-values-p space basis)
   (q1443036-orthonormal-p
    complex-type space basis)
   (q1443036-dense-span-p
    real-type complex-type space basis)))

;; The enumeration 0, 1, -1, 2, -2, ... is a bijection from naturals to
;; integers.  Since all coefficient-square terms are nonnegative, convergence
;; along this enumeration is the target-native rendering of the source tsum
;; over Z and is independent of the chosen bijection.

(defun q1443036-integer-enumeration (n)
  (if (zp n)
      0
    (if (evenp n)
        (- (/ n 2))
      (/ (+ n 1) 2))))

(defun q1443036-fourier-coefficient
    (complex-type space basis vector index)
  (q1443036-inner
   complex-type space
   (q1443036-basis-at basis index)
   vector))

(defun q1443036-coefficient-square
    (real-type complex-type space basis vector index)
  (q1443036-complex-norm-square
   real-type complex-type
   (q1443036-fourier-coefficient
    complex-type space basis vector index)))

(defun q1443036-coefficient-square-partial-sum
    (real-type complex-type space basis vector count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q1443036-zero real-type)
    (let* ((position (- count 1))
           (index
            (q1443036-integer-enumeration position)))
      (q1443036-add
       real-type
       (q1443036-coefficient-square-partial-sum
        real-type complex-type space basis
        vector position)
       (q1443036-coefficient-square
        real-type complex-type space basis
        vector index)))))

(defun-sk q1443036-series-tail-p
    (real-type complex-type space basis vector
     total epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (<= cutoff count))
     (q1443036-less
      real-type
      (q1443036-absolute
       real-type
       (q1443036-subtract
        real-type
        (q1443036-coefficient-square-partial-sum
         real-type complex-type space basis
         vector count)
        total))
      epsilon))))

(defun-sk q1443036-series-cutoff-exists-p
    (real-type complex-type space basis vector
     total epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q1443036-series-tail-p
      real-type complex-type space basis vector
      total epsilon cutoff))))

(defun-sk q1443036-coefficient-square-series-sums-to-p
    (real-type complex-type space basis vector total)
  (forall (epsilon)
    (implies
     (q1443036-positive-p real-type epsilon)
     (q1443036-series-cutoff-exists-p
      real-type complex-type space basis vector
      total epsilon))))

;; Parseval for normalized Haar L2(AddCircle period, C).  Positivity of the
;; period is the source Fact (0 < T); membership of f in the presented Hilbert
;; carrier is the source type f : Lp C 2 haarAddCircle.

(defun thousand-theorems-q1443036-parseval-s-theorem-statement
    (real-type complex-type period
     l2-space fourier-basis f)
  (implies
   (and
    (q1443036-complex-field-p
     real-type complex-type)
    (q1443036-positive-p real-type period)
    (q1443036-complex-hilbert-space-p
     real-type complex-type l2-space)
    (q1443036-fourier-basis-p
     real-type complex-type l2-space fourier-basis)
    (q1443036-member-p l2-space f))
   (q1443036-coefficient-square-series-sums-to-p
    real-type complex-type l2-space fourier-basis f
    (q1443036-vector-norm-square
     real-type complex-type l2-space f))))

(value-triple :itpeval-statement-checked)
:q
