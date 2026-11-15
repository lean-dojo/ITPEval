;; Statement-only formalization of thousand-theorems corpus artifact Q2096184,
;; "Plancherel theorem": the Fourier transform preserves the integral of the
;; pointwise complex inner product of arbitrary Hilbert-valued Schwartz maps
;; on a finite-dimensional real inner-product space. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Mathematical objects are unrestricted ACL2 objects.  The conservative
;; interfaces below only provide application and constructor symbols; every
;; field, space, topology, measure, integral, smoothness, decay, and Fourier
;; law used by the statement is imposed explicitly by predicates below.

(defstub q2096184-member-p (type object) t)
(defstub q2096184-zero (type) t)
(defstub q2096184-one (type) t)
(defstub q2096184-add (type left right) t)
(defstub q2096184-multiply (type left right) t)
(defstub q2096184-negate (type object) t)
(defstub q2096184-inverse (type object) t)
(defstub q2096184-less (type left right) t)
(defstub q2096184-norm (type object) t)
(defstub q2096184-smul (scalar-type space scalar vector) t)
(defstub q2096184-star (scalar-type scalar) t)
(defstub q2096184-real-part (real-type scalar-type scalar) t)
(defstub q2096184-imag-part (real-type scalar-type scalar) t)
(defstub q2096184-of-real (real-type scalar-type real) t)
(defstub q2096184-imaginary-unit (scalar-type) t)
(defstub q2096184-inner (scalar-type space left right) t)
(defstub q2096184-function-at (function argument) t)
(defstub q2096184-sequence-at (sequence index) t)
(defstub q2096184-basis-at (basis index) t)
(defstub q2096184-coordinate (coordinates vector index) t)
(defstub q2096184-derivative-function (derivatives function multiindex) t)
(defstub q2096184-fourier-function (fourier function) t)
(defstub q2096184-character-value (fourier-char real) t)
(defstub q2096184-set-member-p (set object) t)
(defstub q2096184-family-member-p (family set) t)
(defstub q2096184-open-ball-set (space center radius) t)
(defstub q2096184-preimage-set (function set) t)
(defstub q2096184-complement-set (carrier set) t)
(defstub q2096184-countable-union-set (carrier sequence) t)
(defstub q2096184-translate-set (space set shift) t)
(defstub q2096184-unit-cell-set (space basis coordinates dimension) t)
(defstub q2096184-fiber-set (function value) t)
(defstub q2096184-simple-values (function) t)
(defstub q2096184-indicator-function (real-type set) t)
(defstub q2096184-function-add (type left right) t)
(defstub q2096184-function-difference (type left right) t)
(defstub q2096184-function-norm (real-type type function) t)
(defstub q2096184-inner-integrand (scalar-type space left right) t)
(defstub q2096184-fourier-integrand
  (real-type scalar-type domain space fourier-char function frequency) t)
(defstub q2096184-measure-value (measure set) t)
(defstub q2096184-lintegral-value (lintegral function) t)
(defstub q2096184-bochner-integral-value (integral function) t)
(defstub q2096184-full-set (carrier) t)
(defstub q2096184-point-sequence (function-sequence point) t)
(defstub q2096184-simple-integral-sequence
  (real-type domain space measure function-sequence) t)

(defun q2096184-positive-p (real-type x)
  (q2096184-less real-type (q2096184-zero real-type) x))

(defun q2096184-leq (real-type x y)
  (not (q2096184-less real-type y x)))

(defun q2096184-abs (real-type x)
  (if (q2096184-less real-type x (q2096184-zero real-type))
      (q2096184-negate real-type x)
    x))

(defun q2096184-natural-cast (type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q2096184-zero type)
    (q2096184-add
     type
     (q2096184-one type)
     (q2096184-natural-cast type (- n 1)))))

(defun q2096184-integer-cast (type n)
  (if (and (integerp n) (< n 0))
      (q2096184-negate
       type
       (q2096184-natural-cast type (- n)))
    (q2096184-natural-cast type (nfix n))))

(defun q2096184-real-power (real-type x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q2096184-one real-type)
    (q2096184-multiply
     real-type x
     (q2096184-real-power real-type x (- n 1)))))

(defun q2096184-vector-sum
    (real-type space basis coordinates vector n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q2096184-zero space)
    (let ((i (- n 1)))
      (q2096184-add
       space
       (q2096184-vector-sum
        real-type space basis coordinates vector i)
       (q2096184-smul
        real-type space
        (q2096184-coordinate coordinates vector i)
        (q2096184-basis-at basis i))))))

(defun q2096184-zero-multiindex (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (q2096184-zero-multiindex (- n 1)))))

(defun q2096184-natural-list-p (alpha n)
  (if (zp n)
      (equal alpha nil)
    (and
     (consp alpha)
     (natp (car alpha))
     (q2096184-natural-list-p (cdr alpha) (- n 1)))))

(defun q2096184-increment-multiindex (alpha i)
  (if (consp alpha)
      (if (zp i)
          (cons (+ 1 (nfix (car alpha))) (cdr alpha))
        (cons
         (car alpha)
         (q2096184-increment-multiindex (cdr alpha) (- i 1))))
    nil))

(defun q2096184-multiindex-degree (alpha)
  (if (consp alpha)
      (+ (nfix (car alpha))
         (q2096184-multiindex-degree (cdr alpha)))
    0))

;; Complete ordered real field and its canonical complexification.

(defun-sk q2096184-field-laws-p (type)
  (forall (x y z)
    (implies
     (and
      (q2096184-member-p type x)
      (q2096184-member-p type y)
      (q2096184-member-p type z))
     (and
      (q2096184-member-p type (q2096184-add type x y))
      (q2096184-member-p type (q2096184-multiply type x y))
      (q2096184-member-p type (q2096184-negate type x))
      (implies
       (not (equal x (q2096184-zero type)))
       (q2096184-member-p type (q2096184-inverse type x)))
      (equal
       (q2096184-add type (q2096184-add type x y) z)
       (q2096184-add type x (q2096184-add type y z)))
      (equal (q2096184-add type x y) (q2096184-add type y x))
      (equal (q2096184-add type x (q2096184-zero type)) x)
      (equal
       (q2096184-add type x (q2096184-negate type x))
       (q2096184-zero type))
      (equal
       (q2096184-multiply type (q2096184-multiply type x y) z)
       (q2096184-multiply type x (q2096184-multiply type y z)))
      (equal
       (q2096184-multiply type x y)
       (q2096184-multiply type y x))
      (equal (q2096184-multiply type x (q2096184-one type)) x)
      (implies
       (not (equal x (q2096184-zero type)))
       (equal
        (q2096184-multiply type x (q2096184-inverse type x))
        (q2096184-one type)))
      (equal
       (q2096184-multiply type x (q2096184-add type y z))
       (q2096184-add
        type
        (q2096184-multiply type x y)
        (q2096184-multiply type x z)))))))

(defun-sk q2096184-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q2096184-member-p real-type x)
      (q2096184-member-p real-type y)
      (q2096184-member-p real-type z))
     (and
      (not (q2096184-less real-type x x))
      (or
       (q2096184-less real-type x y)
       (equal x y)
       (q2096184-less real-type y x))
      (implies
       (and
        (q2096184-less real-type x y)
        (q2096184-less real-type y z))
       (q2096184-less real-type x z))
      (implies
       (q2096184-less real-type x y)
       (q2096184-less
        real-type
        (q2096184-add real-type x z)
        (q2096184-add real-type y z)))
      (implies
       (and
        (q2096184-positive-p real-type x)
        (q2096184-positive-p real-type y))
       (q2096184-positive-p
        real-type
        (q2096184-multiply real-type x y)))))))

(defun q2096184-distance
    (real-type type x y)
  (declare (ignore real-type))
  (q2096184-norm
   type
   (q2096184-add type x (q2096184-negate type y))))

(defun-sk q2096184-norm-values-p (real-type type)
  (forall (x)
    (implies
     (q2096184-member-p type x)
     (and
      (q2096184-member-p real-type (q2096184-norm type x))
      (q2096184-leq
       real-type
       (q2096184-zero real-type)
       (q2096184-norm type x))
      (iff
       (equal
        (q2096184-norm type x)
        (q2096184-zero real-type))
       (equal x (q2096184-zero type)))))))

(defun-sk q2096184-norm-triangle-p (real-type type)
  (forall (x y)
    (implies
     (and
      (q2096184-member-p type x)
      (q2096184-member-p type y))
     (q2096184-leq
      real-type
      (q2096184-norm type (q2096184-add type x y))
      (q2096184-add
       real-type
       (q2096184-norm type x)
       (q2096184-norm type y))))))

(defun q2096184-norm-laws-p (real-type type)
  (and
   (q2096184-norm-values-p real-type type)
   (q2096184-norm-triangle-p real-type type)))

(defun-sk q2096184-convergence-tail-p
    (real-type type sequence limit epsilon start)
  (forall (n)
    (implies
     (and (natp n) (natp start) (<= start n))
     (q2096184-less
      real-type
      (q2096184-distance
       real-type type
       (q2096184-sequence-at sequence n)
       limit)
      epsilon))))

(defun-sk q2096184-convergence-start-p
    (real-type type sequence limit epsilon)
  (exists (start)
    (and
     (natp start)
     (q2096184-convergence-tail-p
      real-type type sequence limit epsilon start))))

(defun-sk q2096184-converges-p
    (real-type type sequence limit)
  (forall (epsilon)
    (implies
     (and
      (q2096184-member-p real-type epsilon)
      (q2096184-positive-p real-type epsilon))
     (q2096184-convergence-start-p
      real-type type sequence limit epsilon))))

(defun-sk q2096184-cauchy-tail-p
    (real-type type sequence epsilon start)
  (forall (m n)
    (implies
     (and
      (natp m) (natp n) (natp start)
      (<= start m) (<= start n))
     (q2096184-less
      real-type
      (q2096184-distance
       real-type type
       (q2096184-sequence-at sequence m)
       (q2096184-sequence-at sequence n))
      epsilon))))

(defun-sk q2096184-cauchy-start-p
    (real-type type sequence epsilon)
  (exists (start)
    (and
     (natp start)
     (q2096184-cauchy-tail-p
      real-type type sequence epsilon start))))

(defun-sk q2096184-cauchy-p (real-type type sequence)
  (forall (epsilon)
    (implies
     (and
      (q2096184-member-p real-type epsilon)
      (q2096184-positive-p real-type epsilon))
     (q2096184-cauchy-start-p
      real-type type sequence epsilon))))

(defun-sk q2096184-sequence-in-type-p (type sequence)
  (forall (n)
    (implies
     (natp n)
     (q2096184-member-p
      type
      (q2096184-sequence-at sequence n)))))

(defun-sk q2096184-limit-exists-p
    (real-type type sequence)
  (exists (limit)
    (and
     (q2096184-member-p type limit)
     (q2096184-converges-p
      real-type type sequence limit))))

(defun-sk q2096184-complete-p (real-type type)
  (forall (sequence)
    (implies
     (and
      (q2096184-sequence-in-type-p type sequence)
      (q2096184-cauchy-p real-type type sequence))
     (q2096184-limit-exists-p
      real-type type sequence))))

(defun-sk q2096184-archimedean-witness-p (real-type x)
  (exists (n)
    (and
     (natp n)
     (q2096184-less
      real-type x
      (q2096184-natural-cast real-type n)))))

(defun-sk q2096184-archimedean-p (real-type)
  (forall (x)
    (implies
     (q2096184-member-p real-type x)
     (q2096184-archimedean-witness-p real-type x))))

(defun-sk q2096184-real-norm-laws-p (real-type)
  (forall (x)
    (implies
     (q2096184-member-p real-type x)
     (and
      (equal
       (q2096184-norm real-type x)
       (q2096184-abs real-type x))
      (equal (q2096184-star real-type x) x)
      (equal
       (q2096184-real-part real-type real-type x)
       x)
      (equal
       (q2096184-imag-part real-type real-type x)
       (q2096184-zero real-type))
      (equal
       (q2096184-of-real real-type real-type x)
       x)))))

(defun q2096184-real-field-p (real-type)
  (and
   (q2096184-member-p real-type (q2096184-zero real-type))
   (q2096184-member-p real-type (q2096184-one real-type))
   (not
    (equal
     (q2096184-zero real-type)
     (q2096184-one real-type)))
   (q2096184-field-laws-p real-type)
   (q2096184-order-laws-p real-type)
   (q2096184-positive-p real-type (q2096184-one real-type))
   (q2096184-real-norm-laws-p real-type)
   (q2096184-complete-p real-type real-type)
   (q2096184-archimedean-p real-type)))

(defun-sk q2096184-complex-coordinate-laws-p
    (real-type complex-type)
  (forall (z)
    (implies
     (q2096184-member-p complex-type z)
     (let* ((re (q2096184-real-part real-type complex-type z))
            (im (q2096184-imag-part real-type complex-type z))
            (re-z (q2096184-of-real real-type complex-type re))
            (im-z
             (q2096184-multiply
              complex-type
              (q2096184-of-real real-type complex-type im)
              (q2096184-imaginary-unit complex-type))))
       (and
        (q2096184-member-p real-type re)
        (q2096184-member-p real-type im)
        (equal z (q2096184-add complex-type re-z im-z))
        (equal
         (q2096184-star complex-type z)
         (q2096184-add
          complex-type re-z
          (q2096184-negate complex-type im-z)))
        (equal
         (q2096184-multiply
          real-type
          (q2096184-norm complex-type z)
          (q2096184-norm complex-type z))
         (q2096184-add
          real-type
          (q2096184-multiply real-type re re)
          (q2096184-multiply real-type im im))))))))

(defun-sk q2096184-of-real-laws-p
    (real-type complex-type)
  (forall (x y)
    (implies
     (and
      (q2096184-member-p real-type x)
      (q2096184-member-p real-type y))
     (and
      (q2096184-member-p
       complex-type
       (q2096184-of-real real-type complex-type x))
      (equal
       (q2096184-real-part
        real-type complex-type
        (q2096184-of-real real-type complex-type x))
       x)
      (equal
       (q2096184-imag-part
        real-type complex-type
        (q2096184-of-real real-type complex-type x))
       (q2096184-zero real-type))
      (equal
       (q2096184-of-real
        real-type complex-type
        (q2096184-add real-type x y))
       (q2096184-add
        complex-type
        (q2096184-of-real real-type complex-type x)
        (q2096184-of-real real-type complex-type y)))
      (equal
       (q2096184-of-real
        real-type complex-type
        (q2096184-multiply real-type x y))
       (q2096184-multiply
        complex-type
        (q2096184-of-real real-type complex-type x)
        (q2096184-of-real real-type complex-type y)))))))

(defun q2096184-complex-field-p
    (real-type complex-type)
  (and
   (q2096184-real-field-p real-type)
   (q2096184-member-p complex-type (q2096184-zero complex-type))
   (q2096184-member-p complex-type (q2096184-one complex-type))
   (not
    (equal
     (q2096184-zero complex-type)
     (q2096184-one complex-type)))
   (q2096184-field-laws-p complex-type)
   (q2096184-of-real-laws-p real-type complex-type)
   (equal
    (q2096184-of-real
     real-type complex-type (q2096184-zero real-type))
    (q2096184-zero complex-type))
   (equal
    (q2096184-of-real
     real-type complex-type (q2096184-one real-type))
    (q2096184-one complex-type))
   (equal
    (q2096184-multiply
     complex-type
     (q2096184-imaginary-unit complex-type)
     (q2096184-imaginary-unit complex-type))
    (q2096184-negate complex-type (q2096184-one complex-type)))
   (equal
    (q2096184-real-part
     real-type complex-type
     (q2096184-imaginary-unit complex-type))
    (q2096184-zero real-type))
   (equal
    (q2096184-imag-part
     real-type complex-type
     (q2096184-imaginary-unit complex-type))
    (q2096184-one real-type))
   (q2096184-complex-coordinate-laws-p real-type complex-type)
   (q2096184-norm-laws-p real-type complex-type)
   (q2096184-complete-p real-type complex-type)))

;; Real and complex inner-product spaces.

(defun-sk q2096184-vector-space-laws-p
    (scalar-type space)
  (forall (a b x y z)
    (implies
     (and
      (q2096184-member-p scalar-type a)
      (q2096184-member-p scalar-type b)
      (q2096184-member-p space x)
      (q2096184-member-p space y)
      (q2096184-member-p space z))
     (and
      (q2096184-member-p space (q2096184-add space x y))
      (q2096184-member-p space (q2096184-negate space x))
      (q2096184-member-p
       space (q2096184-smul scalar-type space a x))
      (equal
       (q2096184-add space (q2096184-add space x y) z)
       (q2096184-add space x (q2096184-add space y z)))
      (equal (q2096184-add space x y) (q2096184-add space y x))
      (equal (q2096184-add space x (q2096184-zero space)) x)
      (equal
       (q2096184-add space x (q2096184-negate space x))
       (q2096184-zero space))
      (equal
       (q2096184-smul
        scalar-type space (q2096184-one scalar-type) x)
       x)
      (equal
       (q2096184-smul
        scalar-type space
        (q2096184-multiply scalar-type a b) x)
       (q2096184-smul
        scalar-type space a
        (q2096184-smul scalar-type space b x)))
      (equal
       (q2096184-smul
        scalar-type space
        (q2096184-add scalar-type a b) x)
       (q2096184-add
        space
        (q2096184-smul scalar-type space a x)
        (q2096184-smul scalar-type space b x)))
      (equal
       (q2096184-smul
        scalar-type space a (q2096184-add space x y))
       (q2096184-add
        space
        (q2096184-smul scalar-type space a x)
        (q2096184-smul scalar-type space a y)))))))

(defun-sk q2096184-normed-space-laws-p
    (real-type scalar-type space)
  (forall (a x)
    (implies
     (and
      (q2096184-member-p scalar-type a)
      (q2096184-member-p space x))
     (equal
      (q2096184-norm
       space
       (q2096184-smul scalar-type space a x))
      (q2096184-multiply
       real-type
       (q2096184-norm scalar-type a)
       (q2096184-norm space x))))))

(defun-sk q2096184-inner-product-laws-p
    (real-type scalar-type space)
  (forall (a x y z)
    (implies
     (and
      (q2096184-member-p scalar-type a)
      (q2096184-member-p space x)
      (q2096184-member-p space y)
      (q2096184-member-p space z))
     (let ((xy (q2096184-inner scalar-type space x y))
           (xx (q2096184-inner scalar-type space x x)))
       (and
        (q2096184-member-p scalar-type xy)
        (equal
         (q2096184-inner
          scalar-type space x (q2096184-add space y z))
         (q2096184-add
          scalar-type xy
          (q2096184-inner scalar-type space x z)))
        (equal
         (q2096184-inner
          scalar-type space x
          (q2096184-smul scalar-type space a y))
         (q2096184-multiply scalar-type a xy))
        (equal
         (q2096184-inner scalar-type space y x)
         (q2096184-star scalar-type xy))
        (equal
         (q2096184-multiply
          real-type
          (q2096184-norm space x)
          (q2096184-norm space x))
         (q2096184-real-part real-type scalar-type xx))
        (iff
         (equal xx (q2096184-zero scalar-type))
         (equal x (q2096184-zero space))))))))

(defun-sk q2096184-real-smul-compatibility-p
    (real-type complex-type space)
  (forall (r x)
    (implies
     (and
      (q2096184-member-p real-type r)
      (q2096184-member-p space x))
     (equal
      (q2096184-smul real-type space r x)
      (q2096184-smul
       complex-type space
       (q2096184-of-real real-type complex-type r)
       x)))))

(defun-sk q2096184-orthonormal-basis-laws-p
    (real-type space basis coordinates dimension)
  (forall (i j x)
    (and
     (implies
      (and (natp i) (< i dimension))
      (q2096184-member-p space (q2096184-basis-at basis i)))
     (implies
      (and
       (natp i) (natp j)
       (< i dimension) (< j dimension))
      (equal
       (q2096184-inner
        real-type space
        (q2096184-basis-at basis i)
        (q2096184-basis-at basis j))
       (if (equal i j)
           (q2096184-one real-type)
         (q2096184-zero real-type))))
     (implies
      (q2096184-member-p space x)
      (and
       (implies
        (and (natp i) (< i dimension))
        (q2096184-member-p
         real-type
         (q2096184-coordinate coordinates x i)))
       (equal
        x
        (q2096184-vector-sum
         real-type space basis coordinates x dimension)))))))

(defun q2096184-finite-real-inner-product-space-p
    (real-type space basis coordinates dimension)
  (and
   (natp dimension)
   (q2096184-member-p space (q2096184-zero space))
   (q2096184-vector-space-laws-p real-type space)
   (q2096184-norm-laws-p real-type space)
   (q2096184-normed-space-laws-p real-type real-type space)
   (q2096184-inner-product-laws-p real-type real-type space)
   (q2096184-orthonormal-basis-laws-p
    real-type space basis coordinates dimension)))

(defun q2096184-complex-hilbert-space-p
    (real-type complex-type space)
  (and
   (q2096184-member-p space (q2096184-zero space))
   (q2096184-vector-space-laws-p complex-type space)
   (q2096184-vector-space-laws-p real-type space)
   (q2096184-norm-laws-p real-type space)
   (q2096184-normed-space-laws-p
    real-type complex-type space)
   (q2096184-normed-space-laws-p
    real-type real-type space)
   (q2096184-real-smul-compatibility-p
    real-type complex-type space)
   (q2096184-inner-product-laws-p
    real-type complex-type space)
   (q2096184-complete-p real-type space)))

;; Borel sigma algebra and normalized translation-invariant volume.

(defun-sk q2096184-countable-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q2096184-set-member-p
      (q2096184-sequence-at sequence n) x))))

(defun-sk q2096184-valid-set-p (space set)
  (forall (x)
    (implies
     (q2096184-set-member-p set x)
     (q2096184-member-p space x))))

(defun-sk q2096184-sets-equal-on-p (space left right)
  (forall (x)
    (implies
     (q2096184-member-p space x)
     (iff
      (q2096184-set-member-p left x)
      (q2096184-set-member-p right x)))))

(defun-sk q2096184-empty-on-p (space set)
  (forall (x)
    (implies
     (q2096184-member-p space x)
     (not (q2096184-set-member-p set x)))))

(defun-sk q2096184-full-set-law-p (space)
  (forall (x)
    (iff
     (q2096184-set-member-p
      (q2096184-full-set space) x)
     (q2096184-member-p space x))))

(defun-sk q2096184-complement-set-law-p (space)
  (forall (set x)
    (iff
     (q2096184-set-member-p
      (q2096184-complement-set space set) x)
     (and
      (q2096184-member-p space x)
      (not (q2096184-set-member-p set x))))))

(defun-sk q2096184-countable-union-set-law-p (space)
  (forall (sequence x)
    (iff
     (q2096184-set-member-p
      (q2096184-countable-union-set space sequence) x)
     (and
      (q2096184-member-p space x)
      (q2096184-countable-union-member-p sequence x)))))

(defun-sk q2096184-open-ball-set-law-p (real-type space)
  (forall (center radius x)
    (iff
     (q2096184-set-member-p
      (q2096184-open-ball-set space center radius) x)
     (and
      (q2096184-member-p space x)
      (q2096184-member-p space center)
      (q2096184-member-p real-type radius)
      (q2096184-less
       real-type
       (q2096184-distance real-type space x center)
       radius)))))

(defun-sk q2096184-preimage-set-law-p (domain)
  (forall (function set x)
    (iff
     (q2096184-set-member-p
      (q2096184-preimage-set function set) x)
     (and
      (q2096184-member-p domain x)
      (q2096184-set-member-p
       set (q2096184-function-at function x))))))

(defun-sk q2096184-translate-set-law-p (space)
  (forall (set shift x)
    (iff
     (q2096184-set-member-p
      (q2096184-translate-set space set shift) x)
     (and
      (q2096184-member-p space x)
      (q2096184-set-member-p
       set
       (q2096184-add
        space x (q2096184-negate space shift)))))))

(defun q2096184-set-constructor-laws-p
    (real-type space)
  (and
   (q2096184-full-set-law-p space)
   (q2096184-complement-set-law-p space)
   (q2096184-countable-union-set-law-p space)
   (q2096184-open-ball-set-law-p real-type space)
   (q2096184-translate-set-law-p space)))

(defun-sk q2096184-sequence-measurable-p (family sequence)
  (forall (n)
    (implies
     (natp n)
     (q2096184-family-member-p
      family
      (q2096184-sequence-at sequence n)))))

(defun-sk q2096184-family-valid-sets-p (space family)
  (forall (set)
    (implies
     (q2096184-family-member-p family set)
     (q2096184-valid-set-p space set))))

(defun-sk q2096184-family-extensional-p (space family)
  (forall (left right)
    (implies
     (and
      (q2096184-family-member-p family left)
      (q2096184-valid-set-p space right)
      (q2096184-sets-equal-on-p space left right))
     (q2096184-family-member-p family right))))

(defun-sk q2096184-sigma-algebra-closure-p (space family)
  (forall (set sequence)
    (and
     (q2096184-family-member-p family (q2096184-full-set space))
     (implies
      (q2096184-family-member-p family set)
      (q2096184-family-member-p
       family (q2096184-complement-set space set)))
     (implies
      (q2096184-sequence-measurable-p family sequence)
      (q2096184-family-member-p
       family
       (q2096184-countable-union-set space sequence))))))

(defun q2096184-sigma-algebra-p (space family)
  (and
   (q2096184-family-valid-sets-p space family)
   (q2096184-family-extensional-p space family)
   (q2096184-sigma-algebra-closure-p space family)))

(defun-sk q2096184-balls-measurable-p
    (real-type space family)
  (forall (center radius)
    (implies
     (and
      (q2096184-member-p space center)
      (q2096184-member-p real-type radius)
      (q2096184-positive-p real-type radius))
     (q2096184-family-member-p
      family
      (q2096184-open-ball-set space center radius)))))

(defun-sk q2096184-family-subset-p (left right)
  (forall (set)
    (implies
     (q2096184-family-member-p left set)
     (q2096184-family-member-p right set))))

(defun-sk q2096184-borel-minimal-p
    (real-type space borel)
  (forall (candidate)
    (implies
     (and
      (q2096184-sigma-algebra-p space candidate)
      (q2096184-balls-measurable-p
       real-type space candidate))
     (q2096184-family-subset-p borel candidate))))

(defun q2096184-borel-space-p
    (real-type space borel)
  (and
   (q2096184-sigma-algebra-p space borel)
   (q2096184-balls-measurable-p real-type space borel)
   (q2096184-borel-minimal-p real-type space borel)))

(defun q2096184-ennreal-p (real-type x)
  (or
   (equal x :q2096184-top)
   (and
    (consp x)
    (equal (car x) :q2096184-finite)
    (q2096184-member-p real-type (cdr x))
    (q2096184-leq
     real-type (q2096184-zero real-type) (cdr x)))))

(defun q2096184-ennreal-finite (x)
  (cons :q2096184-finite x))

(defun q2096184-ennreal-add (real-type x y)
  (if (or
       (equal x :q2096184-top)
       (equal y :q2096184-top))
      :q2096184-top
    (q2096184-ennreal-finite
     (q2096184-add real-type (cdr x) (cdr y)))))

(defun q2096184-ennreal-leq-p (real-type x y)
  (or
   (equal y :q2096184-top)
   (and
    (not (equal x :q2096184-top))
    (q2096184-leq real-type (cdr x) (cdr y)))))

(defun-sk q2096184-disjoint-sequence-p
    (space sequence)
  (forall (i j x)
    (implies
     (and
      (natp i) (natp j)
      (not (equal i j))
      (q2096184-member-p space x))
     (not
      (and
       (q2096184-set-member-p
        (q2096184-sequence-at sequence i) x)
       (q2096184-set-member-p
        (q2096184-sequence-at sequence j) x))))))

(defun q2096184-ennreal-partial-sum
    (real-type measure sequence n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q2096184-ennreal-finite (q2096184-zero real-type))
    (q2096184-ennreal-add
     real-type
     (q2096184-ennreal-partial-sum
      real-type measure sequence (- n 1))
     (q2096184-measure-value
      measure
      (q2096184-sequence-at sequence (- n 1))))))

(defun-sk q2096184-ennreal-upper-bound-p
    (real-type measure sequence bound)
  (forall (n)
    (implies
     (natp n)
     (q2096184-ennreal-leq-p
      real-type
      (q2096184-ennreal-partial-sum
       real-type measure sequence n)
      bound))))

(defun-sk q2096184-ennreal-series-value-p
    (real-type measure sequence value)
  (forall (bound)
    (iff
     (q2096184-ennreal-upper-bound-p
      real-type measure sequence bound)
     (q2096184-ennreal-leq-p real-type value bound))))

(defun-sk q2096184-countable-additivity-p
    (real-type space measurable measure)
  (forall (sequence)
    (implies
     (and
      (q2096184-sequence-measurable-p measurable sequence)
      (q2096184-disjoint-sequence-p space sequence))
     (q2096184-ennreal-series-value-p
      real-type
      measure
      sequence
      (q2096184-measure-value
       measure
       (q2096184-countable-union-set space sequence))))))

(defun-sk q2096184-measure-values-p (real-type measure)
  (forall (set)
    (q2096184-ennreal-p
     real-type
     (q2096184-measure-value measure set))))

(defun-sk q2096184-measure-extensional-p (space measure)
  (forall (left right)
    (implies
     (and
      (q2096184-valid-set-p space left)
      (q2096184-valid-set-p space right)
      (q2096184-sets-equal-on-p space left right))
     (equal
      (q2096184-measure-value measure left)
      (q2096184-measure-value measure right)))))

(defun-sk q2096184-empty-measurable-zero-p
    (real-type space measurable measure)
  (forall (set)
    (implies
     (and
      (q2096184-family-member-p measurable set)
      (q2096184-empty-on-p space set))
     (equal
      (q2096184-measure-value measure set)
      (q2096184-ennreal-finite
       (q2096184-zero real-type))))))

(defun q2096184-measure-space-p
    (real-type space measurable measure)
  (and
   (q2096184-sigma-algebra-p space measurable)
   (q2096184-measure-values-p real-type measure)
   (q2096184-measure-extensional-p space measure)
   (q2096184-empty-measurable-zero-p
    real-type space measurable measure)
   (equal
    (q2096184-measure-value
     measure
     (q2096184-complement-set
      space (q2096184-full-set space)))
    (q2096184-ennreal-finite (q2096184-zero real-type)))
   (q2096184-countable-additivity-p
    real-type space measurable measure)))

(defun q2096184-unit-coordinates-p
    (real-type coordinates x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (let ((c
           (q2096184-coordinate
            coordinates x (- n 1))))
      (and
       (q2096184-leq
        real-type (q2096184-zero real-type) c)
       (q2096184-less
        real-type c (q2096184-one real-type))
       (q2096184-unit-coordinates-p
        real-type coordinates x (- n 1))))))

(defun-sk q2096184-unit-cell-coordinate-p
    (real-type space basis coordinates dimension)
  (forall (x)
    (iff
     (q2096184-set-member-p
      (q2096184-unit-cell-set
       space basis coordinates dimension)
      x)
     (and
      (q2096184-member-p space x)
      (q2096184-unit-coordinates-p
       real-type coordinates x dimension)))))

(defun-sk q2096184-translation-invariant-p
    (space measurable measure)
  (forall (set shift)
    (implies
     (and
      (q2096184-family-member-p measurable set)
      (q2096184-member-p space shift))
     (equal
      (q2096184-measure-value
       measure
       (q2096184-translate-set space set shift))
      (q2096184-measure-value measure set)))))

(defun q2096184-volume-space-p
    (real-type space basis coordinates dimension measurable measure)
  (and
   (q2096184-borel-space-p real-type space measurable)
   (q2096184-measure-space-p
    real-type space measurable measure)
   (q2096184-unit-cell-coordinate-p
    real-type space basis coordinates dimension)
   (q2096184-family-member-p
    measurable
    (q2096184-unit-cell-set
     space basis coordinates dimension))
   (equal
    (q2096184-measure-value
     measure
     (q2096184-unit-cell-set
      space basis coordinates dimension))
    (q2096184-ennreal-finite
     (q2096184-one real-type)))
   (q2096184-translation-invariant-p
    space measurable measure)))

;; Lebesgue lower integration and Bochner integration.

(defun-sk q2096184-function-into-p
    (domain codomain function)
  (forall (x)
    (implies
     (q2096184-member-p domain x)
     (q2096184-member-p
      codomain
      (q2096184-function-at function x)))))

(defun-sk q2096184-continuous-at-delta-p
    (real-type domain codomain function x epsilon delta)
  (forall (y)
    (implies
     (and
      (q2096184-member-p domain y)
      (q2096184-less
       real-type
       (q2096184-distance real-type domain y x)
       delta))
     (q2096184-less
      real-type
      (q2096184-distance
       real-type codomain
       (q2096184-function-at function y)
       (q2096184-function-at function x))
      epsilon))))

(defun-sk q2096184-continuous-at-epsilon-p
    (real-type domain codomain function x epsilon)
  (exists (delta)
    (and
     (q2096184-member-p real-type delta)
     (q2096184-positive-p real-type delta)
     (q2096184-continuous-at-delta-p
      real-type domain codomain function x epsilon delta))))

(defun-sk q2096184-continuous-function-p
    (real-type domain codomain function)
  (forall (x epsilon)
    (implies
     (and
      (q2096184-member-p domain x)
      (q2096184-member-p real-type epsilon)
      (q2096184-positive-p real-type epsilon))
     (q2096184-continuous-at-epsilon-p
      real-type domain codomain function x epsilon))))

(defun-sk q2096184-function-constructor-laws-p
    (real-type)
  (forall (type f g set value x)
    (and
     (equal
      (q2096184-function-at
       (q2096184-function-add type f g) x)
      (q2096184-add
       type
       (q2096184-function-at f x)
       (q2096184-function-at g x)))
     (equal
      (q2096184-function-at
       (q2096184-function-difference type f g) x)
      (q2096184-add
       type
       (q2096184-function-at f x)
       (q2096184-negate
        type (q2096184-function-at g x))))
     (equal
      (q2096184-function-at
       (q2096184-function-norm real-type type f) x)
      (q2096184-norm type (q2096184-function-at f x)))
     (equal
      (q2096184-function-at
       (q2096184-indicator-function real-type set) x)
      (if (q2096184-set-member-p set x)
          (q2096184-one real-type)
        (q2096184-zero real-type))))))

(defun-sk q2096184-fiber-set-law-p (domain)
  (forall (function value x)
    (iff
     (q2096184-set-member-p
      (q2096184-fiber-set function value)
      x)
     (and
      (q2096184-member-p domain x)
      (equal (q2096184-function-at function x) value)))))

(defun-sk q2096184-measurable-function-p
    (real-type domain measurable codomain function)
  (forall (center radius)
    (implies
     (and
      (q2096184-member-p codomain center)
      (q2096184-member-p real-type radius)
      (q2096184-positive-p real-type radius))
     (q2096184-family-member-p
      measurable
      (q2096184-preimage-set
       function
       (q2096184-open-ball-set
        codomain center radius))))))

(defun-sk q2096184-nonnegative-values-p
    (real-type domain function)
  (forall (x)
    (implies
     (q2096184-member-p domain x)
     (q2096184-leq
      real-type
      (q2096184-zero real-type)
      (q2096184-function-at function x)))))

(defun q2096184-nonnegative-measurable-p
    (real-type domain measurable function)
  (and
   (q2096184-function-into-p
    domain real-type function)
   (q2096184-measurable-function-p
    real-type domain measurable real-type function)
   (q2096184-nonnegative-values-p
    real-type domain function)))

(defun-sk q2096184-pointwise-leq-p
    (real-type domain left right)
  (forall (x)
    (implies
     (q2096184-member-p domain x)
     (q2096184-leq
      real-type
      (q2096184-function-at left x)
      (q2096184-function-at right x)))))

(defun-sk q2096184-functions-equal-on-p
    (domain left right)
  (forall (x)
    (implies
     (q2096184-member-p domain x)
     (equal
      (q2096184-function-at left x)
      (q2096184-function-at right x)))))

(defun-sk q2096184-lintegral-laws-p
    (real-type domain measurable measure lintegral)
  (forall (f g set)
    (and
     (implies
      (q2096184-functions-equal-on-p domain f g)
      (equal
       (q2096184-lintegral-value lintegral f)
       (q2096184-lintegral-value lintegral g)))
     (implies
      (q2096184-nonnegative-measurable-p
       real-type domain measurable f)
      (q2096184-ennreal-p
       real-type
       (q2096184-lintegral-value lintegral f)))
     (implies
      (and
       (q2096184-nonnegative-measurable-p
        real-type domain measurable f)
       (q2096184-nonnegative-measurable-p
        real-type domain measurable g)
       (q2096184-pointwise-leq-p real-type domain f g))
      (q2096184-ennreal-leq-p
       real-type
       (q2096184-lintegral-value lintegral f)
       (q2096184-lintegral-value lintegral g)))
     (implies
      (q2096184-family-member-p measurable set)
      (equal
       (q2096184-lintegral-value
        lintegral
        (q2096184-indicator-function real-type set))
       (q2096184-measure-value measure set)))
     (implies
      (and
       (q2096184-nonnegative-measurable-p
        real-type domain measurable f)
       (q2096184-nonnegative-measurable-p
        real-type domain measurable g))
      (equal
       (q2096184-lintegral-value
        lintegral
        (q2096184-function-add real-type f g))
       (q2096184-ennreal-add
        real-type
        (q2096184-lintegral-value lintegral f)
        (q2096184-lintegral-value lintegral g)))))))

(defun q2096184-simple-values-correct-p
    (domain measurable function values)
  (if (consp values)
      (and
       (q2096184-family-member-p
        measurable
        (q2096184-fiber-set function (car values)))
       (q2096184-simple-values-correct-p
        domain measurable function (cdr values)))
    (equal values nil)))

(defun q2096184-simple-listed-values-in-space-p
    (space values)
  (if (consp values)
      (and
       (q2096184-member-p space (car values))
       (q2096184-simple-listed-values-in-space-p
        space (cdr values)))
    (equal values nil)))

(defun-sk q2096184-simple-range-values-p
    (domain function values)
  (forall (x)
    (implies
     (q2096184-member-p domain x)
     (member-equal
      (q2096184-function-at function x)
      values))))

(defun-sk q2096184-value-attained-p
    (domain function value)
  (exists (x)
    (and
     (q2096184-member-p domain x)
     (equal
      (q2096184-function-at function x)
      value))))

(defun q2096184-simple-function-p
    (domain measurable space function)
  (and
   (q2096184-function-into-p domain space function)
   (true-listp (q2096184-simple-values function))
   (no-duplicatesp-equal (q2096184-simple-values function))
   (q2096184-simple-listed-values-in-space-p
    space (q2096184-simple-values function))
   (q2096184-simple-values-correct-p
    domain measurable function
    (q2096184-simple-values function))
   (q2096184-simple-range-values-p
    domain function
    (q2096184-simple-values function))))

(defun q2096184-simple-integrable-values-p
    (real-type domain measure zero function values)
  (if (consp values)
      (and
       (implies
        (not
         (q2096184-value-attained-p
          domain function (car values)))
        (equal
         (q2096184-measure-value
          measure
          (q2096184-fiber-set function (car values)))
         (q2096184-ennreal-finite
          (q2096184-zero real-type))))
       (or
        (equal (car values) zero)
        (not
         (equal
          (q2096184-measure-value
           measure
           (q2096184-fiber-set function (car values)))
          :q2096184-top)))
       (q2096184-simple-integrable-values-p
        real-type domain measure zero function (cdr values)))
    (equal values nil)))

(defun q2096184-simple-integral
    (real-type domain space measure function values)
  (if (consp values)
      (q2096184-add
       space
       (if (or
            (equal (car values) (q2096184-zero space))
            (not
             (q2096184-value-attained-p
              domain function (car values))))
           (q2096184-zero space)
         (q2096184-smul
          real-type space
          (cdr
           (q2096184-measure-value
            measure
            (q2096184-fiber-set function (car values))))
          (car values)))
       (q2096184-simple-integral
        real-type domain space measure function (cdr values)))
    (q2096184-zero space)))

(defun q2096184-ennreal-scale
    (real-type scalar value)
  (if (equal scalar (q2096184-zero real-type))
      (q2096184-ennreal-finite
       (q2096184-zero real-type))
    (if (equal value :q2096184-top)
        :q2096184-top
      (q2096184-ennreal-finite
       (q2096184-multiply
        real-type scalar (cdr value))))))

(defun q2096184-simple-nonnegative-integral
    (real-type domain measure function values)
  (if (consp values)
      (q2096184-ennreal-add
       real-type
       (if
           (q2096184-value-attained-p
            domain function (car values))
           (q2096184-ennreal-scale
            real-type
            (car values)
            (q2096184-measure-value
             measure
             (q2096184-fiber-set function (car values))))
         (q2096184-ennreal-finite
          (q2096184-zero real-type)))
       (q2096184-simple-nonnegative-integral
        real-type domain measure function (cdr values)))
    (q2096184-ennreal-finite
     (q2096184-zero real-type))))

(defun-sk q2096184-lintegral-upper-bound-p
    (real-type domain measurable measure function bound)
  (forall (simple)
    (implies
     (and
      (q2096184-simple-function-p
       domain measurable real-type simple)
      (q2096184-nonnegative-values-p
       real-type domain simple)
      (q2096184-pointwise-leq-p
       real-type domain simple function))
     (q2096184-ennreal-leq-p
      real-type
      (q2096184-simple-nonnegative-integral
       real-type domain measure simple
       (q2096184-simple-values simple))
      bound))))

(defun-sk q2096184-lintegral-least-upper-bound-p
    (real-type domain measurable measure function value)
  (forall (bound)
    (implies
     (and
      (q2096184-ennreal-p real-type bound)
      (q2096184-lintegral-upper-bound-p
       real-type domain measurable measure function bound))
     (q2096184-ennreal-leq-p real-type value bound))))

(defun-sk q2096184-lintegral-supremum-laws-p
    (real-type domain measurable measure lintegral)
  (forall (function)
    (implies
     (q2096184-nonnegative-measurable-p
      real-type domain measurable function)
     (let ((value
            (q2096184-lintegral-value
             lintegral function)))
       (and
        (q2096184-ennreal-p real-type value)
        (q2096184-lintegral-upper-bound-p
         real-type domain measurable measure function value)
        (q2096184-lintegral-least-upper-bound-p
         real-type domain measurable measure function value))))))

(defun-sk q2096184-simple-sequence-p
    (domain measurable space sequence)
  (forall (n)
    (implies
     (natp n)
     (q2096184-simple-function-p
      domain measurable space
      (q2096184-sequence-at sequence n)))))

(defun-sk q2096184-pointwise-simple-limit-p
    (real-type domain space sequence function)
  (forall (x)
    (implies
     (q2096184-member-p domain x)
     (q2096184-converges-p
      real-type
      space
      (q2096184-point-sequence sequence x)
      (q2096184-function-at function x)))))

(defun-sk q2096184-point-sequence-laws-p ()
  (forall (sequence x n)
    (equal
     (q2096184-sequence-at
      (q2096184-point-sequence sequence x) n)
     (q2096184-function-at
      (q2096184-sequence-at sequence n) x))))

(defun-sk q2096184-strongly-measurable-p
    (real-type domain measurable space function)
  (exists (sequence)
    (and
     (q2096184-simple-sequence-p
      domain measurable space sequence)
     (q2096184-pointwise-simple-limit-p
      real-type domain space sequence function))))

(defun q2096184-integrable-p
    (real-type domain measurable lintegral space function)
  (and
   (q2096184-strongly-measurable-p
    real-type domain measurable space function)
   (not
    (equal
     (q2096184-lintegral-value
      lintegral
      (q2096184-function-norm real-type space function))
     :q2096184-top))))

(defun q2096184-l1-distance
    (real-type space lintegral left right)
  (q2096184-lintegral-value
   lintegral
   (q2096184-function-norm
    real-type space
    (q2096184-function-difference space left right))))

(defun-sk q2096184-l1-tail-p
    (real-type space lintegral sequence function epsilon start)
  (forall (n)
    (implies
     (and (natp n) (natp start) (<= start n))
     (q2096184-ennreal-leq-p
      real-type
      (q2096184-l1-distance
       real-type space lintegral
       (q2096184-sequence-at sequence n)
       function)
      (q2096184-ennreal-finite epsilon)))))

(defun-sk q2096184-l1-start-p
    (real-type space lintegral sequence function epsilon)
  (exists (start)
    (and
     (natp start)
     (q2096184-l1-tail-p
      real-type space lintegral
      sequence function epsilon start))))

(defun-sk q2096184-l1-converges-p
    (real-type space lintegral sequence function)
  (forall (epsilon)
    (implies
     (and
      (q2096184-member-p real-type epsilon)
      (q2096184-positive-p real-type epsilon))
     (q2096184-l1-start-p
      real-type space lintegral sequence function epsilon))))

(defun-sk q2096184-integrable-simple-sequence-p
    (real-type domain measurable measure space sequence)
  (forall (n)
    (implies
     (natp n)
     (let ((f (q2096184-sequence-at sequence n)))
       (and
        (q2096184-simple-function-p
         domain measurable space f)
        (q2096184-simple-integrable-values-p
         real-type domain measure
         (q2096184-zero space) f
         (q2096184-simple-values f)))))))

(defun-sk q2096184-simple-integral-sequence-laws-p ()
  (forall (real-type domain space measure sequence n)
    (equal
     (q2096184-sequence-at
      (q2096184-simple-integral-sequence
       real-type domain space measure sequence)
      n)
     (q2096184-simple-integral
      real-type domain space measure
      (q2096184-sequence-at sequence n)
      (q2096184-simple-values
       (q2096184-sequence-at sequence n))))))

(defun q2096184-bochner-approximation-p
    (real-type domain measurable measure lintegral
     space function value sequence)
  (and
   (q2096184-integrable-simple-sequence-p
    real-type domain measurable measure space sequence)
   (q2096184-l1-converges-p
    real-type space lintegral sequence function)
   (q2096184-converges-p
    real-type space
    (q2096184-simple-integral-sequence
     real-type domain space measure sequence)
    value)))

(defun-sk q2096184-bochner-approximation-exists-p
    (real-type domain measurable measure lintegral
     space function value)
  (exists (sequence)
    (q2096184-bochner-approximation-p
     real-type domain measurable measure lintegral
     space function value sequence)))

(defun-sk q2096184-bochner-integral-operation-p
    (real-type domain measurable measure lintegral space integral)
  (forall (function other)
    (and
     (implies
      (q2096184-functions-equal-on-p
       domain function other)
      (equal
       (q2096184-bochner-integral-value
        integral function)
       (q2096184-bochner-integral-value
        integral other)))
     (implies
      (q2096184-function-into-p domain space function)
      (let ((value
             (q2096184-bochner-integral-value
              integral function)))
        (and
         (q2096184-member-p space value)
         (if
             (and
              (q2096184-complete-p real-type space)
              (q2096184-integrable-p
               real-type domain measurable lintegral
               space function))
             (q2096184-bochner-approximation-exists-p
              real-type domain measurable measure lintegral
              space function value)
           (equal value (q2096184-zero space)))))))))

;; Schwartz maps and the normalized Fourier fourier-char.

(defun q2096184-directional-difference-quotient
    (real-type domain codomain basis function x i h)
  (q2096184-smul
   real-type codomain
   (q2096184-inverse real-type h)
   (q2096184-add
    codomain
    (q2096184-function-at
     function
     (q2096184-add
      domain x
      (q2096184-smul
       real-type domain h
       (q2096184-basis-at basis i))))
    (q2096184-negate
     codomain
     (q2096184-function-at function x)))))

(defun-sk q2096184-derivative-delta-p
    (real-type domain codomain basis
     function derivative x i epsilon delta)
  (forall (h)
    (implies
     (and
      (q2096184-member-p real-type h)
      (q2096184-positive-p
       real-type (q2096184-abs real-type h))
      (q2096184-less
       real-type (q2096184-abs real-type h) delta))
     (q2096184-less
      real-type
      (q2096184-distance
       real-type codomain
       (q2096184-directional-difference-quotient
        real-type domain codomain basis function x i h)
       (q2096184-function-at derivative x))
      epsilon))))

(defun-sk q2096184-derivative-epsilon-p
    (real-type domain codomain basis
     function derivative x i epsilon)
  (exists (delta)
    (and
     (q2096184-member-p real-type delta)
     (q2096184-positive-p real-type delta)
     (q2096184-derivative-delta-p
      real-type domain codomain basis
      function derivative x i epsilon delta))))

(defun-sk q2096184-directional-derivative-p
    (real-type domain codomain basis
     function derivative i)
  (forall (x epsilon)
    (implies
     (and
      (q2096184-member-p domain x)
      (q2096184-member-p real-type epsilon)
      (q2096184-positive-p real-type epsilon))
     (q2096184-derivative-epsilon-p
      real-type domain codomain basis
      function derivative x i epsilon))))

(defun-sk q2096184-derivative-family-p
    (real-type domain codomain basis dimension derivatives function)
  (forall (alpha i)
    (implies
     (and
      (q2096184-natural-list-p alpha dimension)
      (natp i)
      (< i dimension))
     (and
      (q2096184-function-into-p
       domain codomain
       (q2096184-derivative-function
        derivatives function alpha))
      (q2096184-directional-derivative-p
       real-type domain codomain basis
       (q2096184-derivative-function
        derivatives function alpha)
       (q2096184-derivative-function
        derivatives function
        (q2096184-increment-multiindex alpha i))
       i)))))

(defun-sk q2096184-derivative-functions-continuous-p
    (real-type domain codomain dimension derivatives function)
  (forall (alpha)
    (implies
     (q2096184-natural-list-p alpha dimension)
     (let ((derivative
            (q2096184-derivative-function
             derivatives function alpha)))
       (and
        (q2096184-function-into-p
         domain codomain derivative)
        (q2096184-continuous-function-p
         real-type domain codomain derivative))))))

(defun-sk q2096184-decay-bound-p
    (real-type domain codomain derivatives function alpha k bound)
  (forall (x)
    (implies
     (q2096184-member-p domain x)
     (q2096184-leq
      real-type
      (q2096184-multiply
       real-type
       (q2096184-real-power
        real-type
        (q2096184-add
         real-type
         (q2096184-one real-type)
         (q2096184-norm domain x))
        k)
       (q2096184-norm
        codomain
        (q2096184-function-at
         (q2096184-derivative-function
          derivatives function alpha)
         x)))
      bound))))

(defun-sk q2096184-decay-bound-exists-p
    (real-type domain codomain derivatives function alpha k)
  (exists (bound)
    (and
     (q2096184-member-p real-type bound)
     (q2096184-leq
      real-type (q2096184-zero real-type) bound)
     (q2096184-decay-bound-p
      real-type domain codomain derivatives
      function alpha k bound))))

(defun-sk q2096184-rapid-decay-p
    (real-type domain codomain dimension derivatives function)
  (forall (alpha k)
    (implies
     (and
      (q2096184-natural-list-p alpha dimension)
      (natp k))
     (q2096184-decay-bound-exists-p
      real-type domain codomain derivatives
      function alpha k))))

(defun q2096184-schwartz-map-p
    (real-type domain codomain basis dimension derivatives function)
  (and
   (q2096184-function-into-p domain codomain function)
   (equal
    (q2096184-derivative-function
     derivatives function
     (q2096184-zero-multiindex dimension))
    function)
   (q2096184-derivative-family-p
    real-type domain codomain basis dimension
    derivatives function)
   (q2096184-derivative-functions-continuous-p
    real-type domain codomain dimension
    derivatives function)
   (q2096184-rapid-decay-p
    real-type domain codomain dimension
    derivatives function)))

(defun-sk q2096184-character-kernel-witness-p
    (real-type complex-type fourier-char x)
  (exists (n)
    (and
     (integerp n)
     (equal x (q2096184-integer-cast real-type n)))))

(defun-sk q2096184-character-laws-p
    (real-type complex-type fourier-char)
  (forall (x y)
    (implies
     (and
      (q2096184-member-p real-type x)
      (q2096184-member-p real-type y))
     (and
      (q2096184-member-p
       complex-type
       (q2096184-character-value fourier-char x))
      (equal
       (q2096184-character-value
        fourier-char (q2096184-add real-type x y))
       (q2096184-multiply
        complex-type
        (q2096184-character-value fourier-char x)
        (q2096184-character-value fourier-char y)))
      (equal
       (q2096184-norm
        complex-type
        (q2096184-character-value fourier-char x))
       (q2096184-one real-type))
      (iff
       (equal
        (q2096184-character-value fourier-char x)
        (q2096184-one complex-type))
       (q2096184-character-kernel-witness-p
        real-type complex-type fourier-char x))))))

(defun-sk q2096184-character-orientation-delta-p
    (real-type complex-type fourier-char delta)
  (forall (x)
    (implies
     (and
      (q2096184-member-p real-type x)
      (q2096184-positive-p real-type x)
      (q2096184-less real-type x delta))
     (q2096184-less
      real-type
      (q2096184-zero real-type)
      (q2096184-imag-part
       real-type complex-type
       (q2096184-character-value fourier-char x))))))

(defun-sk q2096184-character-orientation-p
    (real-type complex-type fourier-char)
  (exists (delta)
    (and
     (q2096184-member-p real-type delta)
     (q2096184-positive-p real-type delta)
     (q2096184-character-orientation-delta-p
      real-type complex-type fourier-char delta))))

(defun-sk q2096184-character-continuity-delta-p
    (real-type complex-type fourier-char epsilon delta)
  (forall (x)
    (implies
     (and
      (q2096184-member-p real-type x)
      (q2096184-less
       real-type
       (q2096184-abs real-type x)
       delta))
     (q2096184-less
      real-type
      (q2096184-distance
       real-type complex-type
       (q2096184-character-value fourier-char x)
       (q2096184-one complex-type))
      epsilon))))

(defun-sk q2096184-character-continuity-epsilon-p
    (real-type complex-type fourier-char epsilon)
  (exists (delta)
    (and
     (q2096184-member-p real-type delta)
     (q2096184-positive-p real-type delta)
     (q2096184-character-continuity-delta-p
      real-type complex-type fourier-char epsilon delta))))

(defun-sk q2096184-character-continuity-p
    (real-type complex-type fourier-char)
  (forall (epsilon)
    (implies
     (and
      (q2096184-member-p real-type epsilon)
      (q2096184-positive-p real-type epsilon))
     (q2096184-character-continuity-epsilon-p
      real-type complex-type fourier-char epsilon))))

(defun q2096184-fourier-character-p
    (real-type complex-type fourier-char)
  (and
   (equal
    (q2096184-character-value
     fourier-char (q2096184-zero real-type))
    (q2096184-one complex-type))
   (q2096184-character-laws-p
    real-type complex-type fourier-char)
   (q2096184-character-continuity-p
    real-type complex-type fourier-char)
   (q2096184-character-orientation-p
    real-type complex-type fourier-char)))

(defun-sk q2096184-inner-integrand-laws-p
    (complex-type space)
  (forall (f g x)
    (equal
     (q2096184-function-at
      (q2096184-inner-integrand
       complex-type space f g)
      x)
     (q2096184-inner
      complex-type space
      (q2096184-function-at f x)
      (q2096184-function-at g x)))))

(defun-sk q2096184-fourier-integrand-laws-p
    (real-type complex-type domain space fourier-char)
  (forall (f frequency x)
    (equal
     (q2096184-function-at
      (q2096184-fourier-integrand
       real-type complex-type domain space
       fourier-char f frequency)
      x)
     (q2096184-smul
      complex-type space
      (q2096184-character-value
       fourier-char
       (q2096184-negate
        real-type
        (q2096184-inner
         real-type domain x frequency)))
      (q2096184-function-at f x)))))

(defun-sk q2096184-fourier-transform-correct-p
    (real-type complex-type domain space
     fourier-char integral fourier function)
  (forall (frequency)
    (implies
     (q2096184-member-p domain frequency)
     (equal
      (q2096184-function-at
       (q2096184-fourier-function fourier function)
       frequency)
      (q2096184-bochner-integral-value
       integral
       (q2096184-fourier-integrand
        real-type complex-type domain space
        fourier-char function frequency))))))

;; The source theorem, with every implicit typeclass and analytic construction
;; represented by the explicit hypotheses above.

(defun thousand-theorems-q2096184-plancherel-theorem-statement
    (real-type complex-type domain space
     basis coordinates dimension derivatives
     measurable measure lintegral
     complex-integral space-integral
     fourier-char fourier f g)
  (implies
   (and
    (q2096184-complex-field-p real-type complex-type)
    (q2096184-finite-real-inner-product-space-p
     real-type domain basis coordinates dimension)
    (q2096184-complex-hilbert-space-p
     real-type complex-type space)
    (q2096184-set-constructor-laws-p real-type domain)
    (q2096184-set-constructor-laws-p real-type real-type)
    (q2096184-set-constructor-laws-p real-type complex-type)
    (q2096184-set-constructor-laws-p real-type space)
    (q2096184-preimage-set-law-p domain)
    (q2096184-fiber-set-law-p domain)
    (q2096184-function-constructor-laws-p real-type)
    (q2096184-point-sequence-laws-p)
    (q2096184-simple-integral-sequence-laws-p)
    (q2096184-volume-space-p
     real-type domain basis coordinates dimension
     measurable measure)
    (q2096184-lintegral-laws-p
     real-type domain measurable measure lintegral)
    (q2096184-lintegral-supremum-laws-p
     real-type domain measurable measure lintegral)
    (q2096184-bochner-integral-operation-p
     real-type domain measurable measure lintegral
     complex-type complex-integral)
    (q2096184-bochner-integral-operation-p
     real-type domain measurable measure lintegral
     space space-integral)
    (q2096184-fourier-character-p
     real-type complex-type fourier-char)
    (q2096184-inner-integrand-laws-p complex-type space)
    (q2096184-fourier-integrand-laws-p
     real-type complex-type domain space fourier-char)
    (q2096184-schwartz-map-p
     real-type domain space basis dimension derivatives f)
    (q2096184-schwartz-map-p
     real-type domain space basis dimension derivatives g)
    (q2096184-fourier-transform-correct-p
     real-type complex-type domain space
     fourier-char space-integral fourier f)
    (q2096184-fourier-transform-correct-p
     real-type complex-type domain space
     fourier-char space-integral fourier g))
   (equal
    (q2096184-bochner-integral-value
     complex-integral
     (q2096184-inner-integrand
      complex-type space
      (q2096184-fourier-function fourier f)
      (q2096184-fourier-function fourier g)))
    (q2096184-bochner-integral-value
     complex-integral
     (q2096184-inner-integrand
      complex-type space f g)))))

(value-triple :itpeval-statement-checked)
:q
