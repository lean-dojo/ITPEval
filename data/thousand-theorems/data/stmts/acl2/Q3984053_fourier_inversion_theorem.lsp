;; Statement-only formalization of thousand-theorems corpus artifact Q3984053,
;; "Fourier inversion theorem": for a continuous integrable Banach-valued
;; function on a finite-dimensional real inner-product space whose Fourier
;; transform is integrable, inverse Fourier transformation recovers the
;; original function everywhere. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Mathematical objects are unrestricted ACL2 objects.  The conservative
;; interfaces below only provide application and constructor symbols; every
;; field, space, topology, measure, integral, and Fourier law used by the
;; statement is imposed explicitly by predicates below.

(defstub q3984053-member-p (type object) t)
(defstub q3984053-zero (type) t)
(defstub q3984053-one (type) t)
(defstub q3984053-add (type left right) t)
(defstub q3984053-multiply (type left right) t)
(defstub q3984053-negate (type object) t)
(defstub q3984053-inverse (type object) t)
(defstub q3984053-less (type left right) t)
(defstub q3984053-norm (type object) t)
(defstub q3984053-smul (scalar-type space scalar vector) t)
(defstub q3984053-star (scalar-type scalar) t)
(defstub q3984053-real-part (real-type scalar-type scalar) t)
(defstub q3984053-imag-part (real-type scalar-type scalar) t)
(defstub q3984053-of-real (real-type scalar-type real) t)
(defstub q3984053-imaginary-unit (scalar-type) t)
(defstub q3984053-inner (scalar-type space left right) t)
(defstub q3984053-function-at (function argument) t)
(defstub q3984053-sequence-at (sequence index) t)
(defstub q3984053-basis-at (basis index) t)
(defstub q3984053-coordinate (coordinates vector index) t)
(defstub q3984053-fourier-function (fourier function) t)
(defstub q3984053-fourier-inverse-function (fourier-inverse function) t)
(defstub q3984053-character-value (fourier-char real) t)
(defstub q3984053-set-member-p (set object) t)
(defstub q3984053-family-member-p (family set) t)
(defstub q3984053-open-ball-set (space center radius) t)
(defstub q3984053-preimage-set (function set) t)
(defstub q3984053-complement-set (carrier set) t)
(defstub q3984053-countable-union-set (carrier sequence) t)
(defstub q3984053-translate-set (space set shift) t)
(defstub q3984053-unit-cell-set (space basis coordinates dimension) t)
(defstub q3984053-fiber-set (function value) t)
(defstub q3984053-simple-values (function) t)
(defstub q3984053-indicator-function (real-type set) t)
(defstub q3984053-function-add (type left right) t)
(defstub q3984053-function-difference (type left right) t)
(defstub q3984053-function-norm (real-type type function) t)
(defstub q3984053-fourier-integrand
  (real-type scalar-type domain space fourier-char function frequency) t)
(defstub q3984053-inverse-fourier-integrand
  (real-type scalar-type domain space fourier-char function frequency) t)
(defstub q3984053-measure-value (measure set) t)
(defstub q3984053-lintegral-value (lintegral function) t)
(defstub q3984053-bochner-integral-value (integral function) t)
(defstub q3984053-full-set (carrier) t)
(defstub q3984053-point-sequence (function-sequence point) t)
(defstub q3984053-simple-integral-sequence
  (real-type domain space measure function-sequence) t)

(defun q3984053-positive-p (real-type x)
  (q3984053-less real-type (q3984053-zero real-type) x))

(defun q3984053-leq (real-type x y)
  (not (q3984053-less real-type y x)))

(defun q3984053-abs (real-type x)
  (if (q3984053-less real-type x (q3984053-zero real-type))
      (q3984053-negate real-type x)
    x))

(defun q3984053-natural-cast (type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q3984053-zero type)
    (q3984053-add
     type
     (q3984053-one type)
     (q3984053-natural-cast type (- n 1)))))

(defun q3984053-integer-cast (type n)
  (if (and (integerp n) (< n 0))
      (q3984053-negate
       type
       (q3984053-natural-cast type (- n)))
    (q3984053-natural-cast type (nfix n))))


(defun q3984053-vector-sum
    (real-type space basis coordinates vector n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q3984053-zero space)
    (let ((i (- n 1)))
      (q3984053-add
       space
       (q3984053-vector-sum
        real-type space basis coordinates vector i)
       (q3984053-smul
        real-type space
        (q3984053-coordinate coordinates vector i)
        (q3984053-basis-at basis i))))))


;; Complete ordered real field and its canonical complexification.

(defun-sk q3984053-field-laws-p (type)
  (forall (x y z)
    (implies
     (and
      (q3984053-member-p type x)
      (q3984053-member-p type y)
      (q3984053-member-p type z))
     (and
      (q3984053-member-p type (q3984053-add type x y))
      (q3984053-member-p type (q3984053-multiply type x y))
      (q3984053-member-p type (q3984053-negate type x))
      (implies
       (not (equal x (q3984053-zero type)))
       (q3984053-member-p type (q3984053-inverse type x)))
      (equal
       (q3984053-add type (q3984053-add type x y) z)
       (q3984053-add type x (q3984053-add type y z)))
      (equal (q3984053-add type x y) (q3984053-add type y x))
      (equal (q3984053-add type x (q3984053-zero type)) x)
      (equal
       (q3984053-add type x (q3984053-negate type x))
       (q3984053-zero type))
      (equal
       (q3984053-multiply type (q3984053-multiply type x y) z)
       (q3984053-multiply type x (q3984053-multiply type y z)))
      (equal
       (q3984053-multiply type x y)
       (q3984053-multiply type y x))
      (equal (q3984053-multiply type x (q3984053-one type)) x)
      (implies
       (not (equal x (q3984053-zero type)))
       (equal
        (q3984053-multiply type x (q3984053-inverse type x))
        (q3984053-one type)))
      (equal
       (q3984053-multiply type x (q3984053-add type y z))
       (q3984053-add
        type
        (q3984053-multiply type x y)
        (q3984053-multiply type x z)))))))

(defun-sk q3984053-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q3984053-member-p real-type x)
      (q3984053-member-p real-type y)
      (q3984053-member-p real-type z))
     (and
      (not (q3984053-less real-type x x))
      (or
       (q3984053-less real-type x y)
       (equal x y)
       (q3984053-less real-type y x))
      (implies
       (and
        (q3984053-less real-type x y)
        (q3984053-less real-type y z))
       (q3984053-less real-type x z))
      (implies
       (q3984053-less real-type x y)
       (q3984053-less
        real-type
        (q3984053-add real-type x z)
        (q3984053-add real-type y z)))
      (implies
       (and
        (q3984053-positive-p real-type x)
        (q3984053-positive-p real-type y))
       (q3984053-positive-p
        real-type
        (q3984053-multiply real-type x y)))))))

(defun q3984053-distance
    (real-type type x y)
  (declare (ignore real-type))
  (q3984053-norm
   type
   (q3984053-add type x (q3984053-negate type y))))

(defun-sk q3984053-norm-values-p (real-type type)
  (forall (x)
    (implies
     (q3984053-member-p type x)
     (and
      (q3984053-member-p real-type (q3984053-norm type x))
      (q3984053-leq
       real-type
       (q3984053-zero real-type)
       (q3984053-norm type x))
      (iff
       (equal
        (q3984053-norm type x)
        (q3984053-zero real-type))
       (equal x (q3984053-zero type)))))))

(defun-sk q3984053-norm-triangle-p (real-type type)
  (forall (x y)
    (implies
     (and
      (q3984053-member-p type x)
      (q3984053-member-p type y))
     (q3984053-leq
      real-type
      (q3984053-norm type (q3984053-add type x y))
      (q3984053-add
       real-type
       (q3984053-norm type x)
       (q3984053-norm type y))))))

(defun q3984053-norm-laws-p (real-type type)
  (and
   (q3984053-norm-values-p real-type type)
   (q3984053-norm-triangle-p real-type type)))

(defun-sk q3984053-convergence-tail-p
    (real-type type sequence limit epsilon start)
  (forall (n)
    (implies
     (and (natp n) (natp start) (<= start n))
     (q3984053-less
      real-type
      (q3984053-distance
       real-type type
       (q3984053-sequence-at sequence n)
       limit)
      epsilon))))

(defun-sk q3984053-convergence-start-p
    (real-type type sequence limit epsilon)
  (exists (start)
    (and
     (natp start)
     (q3984053-convergence-tail-p
      real-type type sequence limit epsilon start))))

(defun-sk q3984053-converges-p
    (real-type type sequence limit)
  (forall (epsilon)
    (implies
     (and
      (q3984053-member-p real-type epsilon)
      (q3984053-positive-p real-type epsilon))
     (q3984053-convergence-start-p
      real-type type sequence limit epsilon))))

(defun-sk q3984053-cauchy-tail-p
    (real-type type sequence epsilon start)
  (forall (m n)
    (implies
     (and
      (natp m) (natp n) (natp start)
      (<= start m) (<= start n))
     (q3984053-less
      real-type
      (q3984053-distance
       real-type type
       (q3984053-sequence-at sequence m)
       (q3984053-sequence-at sequence n))
      epsilon))))

(defun-sk q3984053-cauchy-start-p
    (real-type type sequence epsilon)
  (exists (start)
    (and
     (natp start)
     (q3984053-cauchy-tail-p
      real-type type sequence epsilon start))))

(defun-sk q3984053-cauchy-p (real-type type sequence)
  (forall (epsilon)
    (implies
     (and
      (q3984053-member-p real-type epsilon)
      (q3984053-positive-p real-type epsilon))
     (q3984053-cauchy-start-p
      real-type type sequence epsilon))))

(defun-sk q3984053-sequence-in-type-p (type sequence)
  (forall (n)
    (implies
     (natp n)
     (q3984053-member-p
      type
      (q3984053-sequence-at sequence n)))))

(defun-sk q3984053-limit-exists-p
    (real-type type sequence)
  (exists (limit)
    (and
     (q3984053-member-p type limit)
     (q3984053-converges-p
      real-type type sequence limit))))

(defun-sk q3984053-complete-p (real-type type)
  (forall (sequence)
    (implies
     (and
      (q3984053-sequence-in-type-p type sequence)
      (q3984053-cauchy-p real-type type sequence))
     (q3984053-limit-exists-p
      real-type type sequence))))

(defun-sk q3984053-archimedean-witness-p (real-type x)
  (exists (n)
    (and
     (natp n)
     (q3984053-less
      real-type x
      (q3984053-natural-cast real-type n)))))

(defun-sk q3984053-archimedean-p (real-type)
  (forall (x)
    (implies
     (q3984053-member-p real-type x)
     (q3984053-archimedean-witness-p real-type x))))

(defun-sk q3984053-real-norm-laws-p (real-type)
  (forall (x)
    (implies
     (q3984053-member-p real-type x)
     (and
      (equal
       (q3984053-norm real-type x)
       (q3984053-abs real-type x))
      (equal (q3984053-star real-type x) x)
      (equal
       (q3984053-real-part real-type real-type x)
       x)
      (equal
       (q3984053-imag-part real-type real-type x)
       (q3984053-zero real-type))
      (equal
       (q3984053-of-real real-type real-type x)
       x)))))

(defun q3984053-real-field-p (real-type)
  (and
   (q3984053-member-p real-type (q3984053-zero real-type))
   (q3984053-member-p real-type (q3984053-one real-type))
   (not
    (equal
     (q3984053-zero real-type)
     (q3984053-one real-type)))
   (q3984053-field-laws-p real-type)
   (q3984053-order-laws-p real-type)
   (q3984053-positive-p real-type (q3984053-one real-type))
   (q3984053-real-norm-laws-p real-type)
   (q3984053-complete-p real-type real-type)
   (q3984053-archimedean-p real-type)))

(defun-sk q3984053-complex-coordinate-laws-p
    (real-type complex-type)
  (forall (z)
    (implies
     (q3984053-member-p complex-type z)
     (let* ((re (q3984053-real-part real-type complex-type z))
            (im (q3984053-imag-part real-type complex-type z))
            (re-z (q3984053-of-real real-type complex-type re))
            (im-z
             (q3984053-multiply
              complex-type
              (q3984053-of-real real-type complex-type im)
              (q3984053-imaginary-unit complex-type))))
       (and
        (q3984053-member-p real-type re)
        (q3984053-member-p real-type im)
        (equal z (q3984053-add complex-type re-z im-z))
        (equal
         (q3984053-star complex-type z)
         (q3984053-add
          complex-type re-z
          (q3984053-negate complex-type im-z)))
        (equal
         (q3984053-multiply
          real-type
          (q3984053-norm complex-type z)
          (q3984053-norm complex-type z))
         (q3984053-add
          real-type
          (q3984053-multiply real-type re re)
          (q3984053-multiply real-type im im))))))))

(defun-sk q3984053-of-real-laws-p
    (real-type complex-type)
  (forall (x y)
    (implies
     (and
      (q3984053-member-p real-type x)
      (q3984053-member-p real-type y))
     (and
      (q3984053-member-p
       complex-type
       (q3984053-of-real real-type complex-type x))
      (equal
       (q3984053-real-part
        real-type complex-type
        (q3984053-of-real real-type complex-type x))
       x)
      (equal
       (q3984053-imag-part
        real-type complex-type
        (q3984053-of-real real-type complex-type x))
       (q3984053-zero real-type))
      (equal
       (q3984053-of-real
        real-type complex-type
        (q3984053-add real-type x y))
       (q3984053-add
        complex-type
        (q3984053-of-real real-type complex-type x)
        (q3984053-of-real real-type complex-type y)))
      (equal
       (q3984053-of-real
        real-type complex-type
        (q3984053-multiply real-type x y))
       (q3984053-multiply
        complex-type
        (q3984053-of-real real-type complex-type x)
        (q3984053-of-real real-type complex-type y)))))))

(defun q3984053-complex-field-p
    (real-type complex-type)
  (and
   (q3984053-real-field-p real-type)
   (q3984053-member-p complex-type (q3984053-zero complex-type))
   (q3984053-member-p complex-type (q3984053-one complex-type))
   (not
    (equal
     (q3984053-zero complex-type)
     (q3984053-one complex-type)))
   (q3984053-field-laws-p complex-type)
   (q3984053-of-real-laws-p real-type complex-type)
   (equal
    (q3984053-of-real
     real-type complex-type (q3984053-zero real-type))
    (q3984053-zero complex-type))
   (equal
    (q3984053-of-real
     real-type complex-type (q3984053-one real-type))
    (q3984053-one complex-type))
   (equal
    (q3984053-multiply
     complex-type
     (q3984053-imaginary-unit complex-type)
     (q3984053-imaginary-unit complex-type))
    (q3984053-negate complex-type (q3984053-one complex-type)))
   (equal
    (q3984053-real-part
     real-type complex-type
     (q3984053-imaginary-unit complex-type))
    (q3984053-zero real-type))
   (equal
    (q3984053-imag-part
     real-type complex-type
     (q3984053-imaginary-unit complex-type))
    (q3984053-one real-type))
   (q3984053-complex-coordinate-laws-p real-type complex-type)
   (q3984053-norm-laws-p real-type complex-type)
   (q3984053-complete-p real-type complex-type)))

;; Real inner-product domains and complex Banach codomains.

(defun-sk q3984053-vector-space-laws-p
    (scalar-type space)
  (forall (a b x y z)
    (implies
     (and
      (q3984053-member-p scalar-type a)
      (q3984053-member-p scalar-type b)
      (q3984053-member-p space x)
      (q3984053-member-p space y)
      (q3984053-member-p space z))
     (and
      (q3984053-member-p space (q3984053-add space x y))
      (q3984053-member-p space (q3984053-negate space x))
      (q3984053-member-p
       space (q3984053-smul scalar-type space a x))
      (equal
       (q3984053-add space (q3984053-add space x y) z)
       (q3984053-add space x (q3984053-add space y z)))
      (equal (q3984053-add space x y) (q3984053-add space y x))
      (equal (q3984053-add space x (q3984053-zero space)) x)
      (equal
       (q3984053-add space x (q3984053-negate space x))
       (q3984053-zero space))
      (equal
       (q3984053-smul
        scalar-type space (q3984053-one scalar-type) x)
       x)
      (equal
       (q3984053-smul
        scalar-type space
        (q3984053-multiply scalar-type a b) x)
       (q3984053-smul
        scalar-type space a
        (q3984053-smul scalar-type space b x)))
      (equal
       (q3984053-smul
        scalar-type space
        (q3984053-add scalar-type a b) x)
       (q3984053-add
        space
        (q3984053-smul scalar-type space a x)
        (q3984053-smul scalar-type space b x)))
      (equal
       (q3984053-smul
        scalar-type space a (q3984053-add space x y))
       (q3984053-add
        space
        (q3984053-smul scalar-type space a x)
        (q3984053-smul scalar-type space a y)))))))

(defun-sk q3984053-normed-space-laws-p
    (real-type scalar-type space)
  (forall (a x)
    (implies
     (and
      (q3984053-member-p scalar-type a)
      (q3984053-member-p space x))
     (equal
      (q3984053-norm
       space
       (q3984053-smul scalar-type space a x))
      (q3984053-multiply
       real-type
       (q3984053-norm scalar-type a)
       (q3984053-norm space x))))))

(defun-sk q3984053-inner-product-laws-p
    (real-type scalar-type space)
  (forall (a x y z)
    (implies
     (and
      (q3984053-member-p scalar-type a)
      (q3984053-member-p space x)
      (q3984053-member-p space y)
      (q3984053-member-p space z))
     (let ((xy (q3984053-inner scalar-type space x y))
           (xx (q3984053-inner scalar-type space x x)))
       (and
        (q3984053-member-p scalar-type xy)
        (equal
         (q3984053-inner
          scalar-type space x (q3984053-add space y z))
         (q3984053-add
          scalar-type xy
          (q3984053-inner scalar-type space x z)))
        (equal
         (q3984053-inner
          scalar-type space x
          (q3984053-smul scalar-type space a y))
         (q3984053-multiply scalar-type a xy))
        (equal
         (q3984053-inner scalar-type space y x)
         (q3984053-star scalar-type xy))
        (equal
         (q3984053-multiply
          real-type
          (q3984053-norm space x)
          (q3984053-norm space x))
         (q3984053-real-part real-type scalar-type xx))
        (iff
         (equal xx (q3984053-zero scalar-type))
         (equal x (q3984053-zero space))))))))

(defun-sk q3984053-real-smul-compatibility-p
    (real-type complex-type space)
  (forall (r x)
    (implies
     (and
      (q3984053-member-p real-type r)
      (q3984053-member-p space x))
     (equal
      (q3984053-smul real-type space r x)
      (q3984053-smul
       complex-type space
       (q3984053-of-real real-type complex-type r)
       x)))))

(defun-sk q3984053-orthonormal-basis-laws-p
    (real-type space basis coordinates dimension)
  (forall (i j x)
    (and
     (implies
      (and (natp i) (< i dimension))
      (q3984053-member-p space (q3984053-basis-at basis i)))
     (implies
      (and
       (natp i) (natp j)
       (< i dimension) (< j dimension))
      (equal
       (q3984053-inner
        real-type space
        (q3984053-basis-at basis i)
        (q3984053-basis-at basis j))
       (if (equal i j)
           (q3984053-one real-type)
         (q3984053-zero real-type))))
     (implies
      (q3984053-member-p space x)
      (and
       (implies
        (and (natp i) (< i dimension))
        (q3984053-member-p
         real-type
         (q3984053-coordinate coordinates x i)))
       (equal
        x
        (q3984053-vector-sum
         real-type space basis coordinates x dimension)))))))

(defun q3984053-finite-real-inner-product-space-p
    (real-type space basis coordinates dimension)
  (and
   (natp dimension)
   (q3984053-member-p space (q3984053-zero space))
   (q3984053-vector-space-laws-p real-type space)
   (q3984053-norm-laws-p real-type space)
   (q3984053-normed-space-laws-p real-type real-type space)
   (q3984053-inner-product-laws-p real-type real-type space)
   (q3984053-orthonormal-basis-laws-p
    real-type space basis coordinates dimension)))

(defun q3984053-complex-banach-space-p
    (real-type complex-type space)
  (and
   (q3984053-member-p space (q3984053-zero space))
   (q3984053-vector-space-laws-p complex-type space)
   (q3984053-vector-space-laws-p real-type space)
   (q3984053-norm-laws-p real-type space)
   (q3984053-normed-space-laws-p
    real-type complex-type space)
   (q3984053-normed-space-laws-p
    real-type real-type space)
   (q3984053-real-smul-compatibility-p
    real-type complex-type space)
   (q3984053-complete-p real-type space)))

;; Borel sigma algebra and normalized translation-invariant volume.

(defun-sk q3984053-countable-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q3984053-set-member-p
      (q3984053-sequence-at sequence n) x))))

(defun-sk q3984053-valid-set-p (space set)
  (forall (x)
    (implies
     (q3984053-set-member-p set x)
     (q3984053-member-p space x))))

(defun-sk q3984053-sets-equal-on-p (space left right)
  (forall (x)
    (implies
     (q3984053-member-p space x)
     (iff
      (q3984053-set-member-p left x)
      (q3984053-set-member-p right x)))))

(defun-sk q3984053-empty-on-p (space set)
  (forall (x)
    (implies
     (q3984053-member-p space x)
     (not (q3984053-set-member-p set x)))))

(defun-sk q3984053-full-set-law-p (space)
  (forall (x)
    (iff
     (q3984053-set-member-p
      (q3984053-full-set space) x)
     (q3984053-member-p space x))))

(defun-sk q3984053-complement-set-law-p (space)
  (forall (set x)
    (iff
     (q3984053-set-member-p
      (q3984053-complement-set space set) x)
     (and
      (q3984053-member-p space x)
      (not (q3984053-set-member-p set x))))))

(defun-sk q3984053-countable-union-set-law-p (space)
  (forall (sequence x)
    (iff
     (q3984053-set-member-p
      (q3984053-countable-union-set space sequence) x)
     (and
      (q3984053-member-p space x)
      (q3984053-countable-union-member-p sequence x)))))

(defun-sk q3984053-open-ball-set-law-p (real-type space)
  (forall (center radius x)
    (iff
     (q3984053-set-member-p
      (q3984053-open-ball-set space center radius) x)
     (and
      (q3984053-member-p space x)
      (q3984053-member-p space center)
      (q3984053-member-p real-type radius)
      (q3984053-less
       real-type
       (q3984053-distance real-type space x center)
       radius)))))

(defun-sk q3984053-preimage-set-law-p (domain)
  (forall (function set x)
    (iff
     (q3984053-set-member-p
      (q3984053-preimage-set function set) x)
     (and
      (q3984053-member-p domain x)
      (q3984053-set-member-p
       set (q3984053-function-at function x))))))

(defun-sk q3984053-translate-set-law-p (space)
  (forall (set shift x)
    (iff
     (q3984053-set-member-p
      (q3984053-translate-set space set shift) x)
     (and
      (q3984053-member-p space x)
      (q3984053-set-member-p
       set
       (q3984053-add
        space x (q3984053-negate space shift)))))))

(defun q3984053-set-constructor-laws-p
    (real-type space)
  (and
   (q3984053-full-set-law-p space)
   (q3984053-complement-set-law-p space)
   (q3984053-countable-union-set-law-p space)
   (q3984053-open-ball-set-law-p real-type space)
   (q3984053-translate-set-law-p space)))

(defun-sk q3984053-sequence-measurable-p (family sequence)
  (forall (n)
    (implies
     (natp n)
     (q3984053-family-member-p
      family
      (q3984053-sequence-at sequence n)))))

(defun-sk q3984053-family-valid-sets-p (space family)
  (forall (set)
    (implies
     (q3984053-family-member-p family set)
     (q3984053-valid-set-p space set))))

(defun-sk q3984053-family-extensional-p (space family)
  (forall (left right)
    (implies
     (and
      (q3984053-family-member-p family left)
      (q3984053-valid-set-p space right)
      (q3984053-sets-equal-on-p space left right))
     (q3984053-family-member-p family right))))

(defun-sk q3984053-sigma-algebra-closure-p (space family)
  (forall (set sequence)
    (and
     (q3984053-family-member-p family (q3984053-full-set space))
     (implies
      (q3984053-family-member-p family set)
      (q3984053-family-member-p
       family (q3984053-complement-set space set)))
     (implies
      (q3984053-sequence-measurable-p family sequence)
      (q3984053-family-member-p
       family
       (q3984053-countable-union-set space sequence))))))

(defun q3984053-sigma-algebra-p (space family)
  (and
   (q3984053-family-valid-sets-p space family)
   (q3984053-family-extensional-p space family)
   (q3984053-sigma-algebra-closure-p space family)))

(defun-sk q3984053-balls-measurable-p
    (real-type space family)
  (forall (center radius)
    (implies
     (and
      (q3984053-member-p space center)
      (q3984053-member-p real-type radius)
      (q3984053-positive-p real-type radius))
     (q3984053-family-member-p
      family
      (q3984053-open-ball-set space center radius)))))

(defun-sk q3984053-family-subset-p (left right)
  (forall (set)
    (implies
     (q3984053-family-member-p left set)
     (q3984053-family-member-p right set))))

(defun-sk q3984053-borel-minimal-p
    (real-type space borel)
  (forall (candidate)
    (implies
     (and
      (q3984053-sigma-algebra-p space candidate)
      (q3984053-balls-measurable-p
       real-type space candidate))
     (q3984053-family-subset-p borel candidate))))

(defun q3984053-borel-space-p
    (real-type space borel)
  (and
   (q3984053-sigma-algebra-p space borel)
   (q3984053-balls-measurable-p real-type space borel)
   (q3984053-borel-minimal-p real-type space borel)))

(defun q3984053-ennreal-p (real-type x)
  (or
   (equal x :q3984053-top)
   (and
    (consp x)
    (equal (car x) :q3984053-finite)
    (q3984053-member-p real-type (cdr x))
    (q3984053-leq
     real-type (q3984053-zero real-type) (cdr x)))))

(defun q3984053-ennreal-finite (x)
  (cons :q3984053-finite x))

(defun q3984053-ennreal-add (real-type x y)
  (if (or
       (equal x :q3984053-top)
       (equal y :q3984053-top))
      :q3984053-top
    (q3984053-ennreal-finite
     (q3984053-add real-type (cdr x) (cdr y)))))

(defun q3984053-ennreal-leq-p (real-type x y)
  (or
   (equal y :q3984053-top)
   (and
    (not (equal x :q3984053-top))
    (q3984053-leq real-type (cdr x) (cdr y)))))

(defun-sk q3984053-disjoint-sequence-p
    (space sequence)
  (forall (i j x)
    (implies
     (and
      (natp i) (natp j)
      (not (equal i j))
      (q3984053-member-p space x))
     (not
      (and
       (q3984053-set-member-p
        (q3984053-sequence-at sequence i) x)
       (q3984053-set-member-p
        (q3984053-sequence-at sequence j) x))))))

(defun q3984053-ennreal-partial-sum
    (real-type measure sequence n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q3984053-ennreal-finite (q3984053-zero real-type))
    (q3984053-ennreal-add
     real-type
     (q3984053-ennreal-partial-sum
      real-type measure sequence (- n 1))
     (q3984053-measure-value
      measure
      (q3984053-sequence-at sequence (- n 1))))))

(defun-sk q3984053-ennreal-upper-bound-p
    (real-type measure sequence bound)
  (forall (n)
    (implies
     (natp n)
     (q3984053-ennreal-leq-p
      real-type
      (q3984053-ennreal-partial-sum
       real-type measure sequence n)
      bound))))

(defun-sk q3984053-ennreal-series-value-p
    (real-type measure sequence value)
  (forall (bound)
    (iff
     (q3984053-ennreal-upper-bound-p
      real-type measure sequence bound)
     (q3984053-ennreal-leq-p real-type value bound))))

(defun-sk q3984053-countable-additivity-p
    (real-type space measurable measure)
  (forall (sequence)
    (implies
     (and
      (q3984053-sequence-measurable-p measurable sequence)
      (q3984053-disjoint-sequence-p space sequence))
     (q3984053-ennreal-series-value-p
      real-type
      measure
      sequence
      (q3984053-measure-value
       measure
       (q3984053-countable-union-set space sequence))))))

(defun-sk q3984053-measure-values-p (real-type measure)
  (forall (set)
    (q3984053-ennreal-p
     real-type
     (q3984053-measure-value measure set))))

(defun-sk q3984053-measure-extensional-p (space measure)
  (forall (left right)
    (implies
     (and
      (q3984053-valid-set-p space left)
      (q3984053-valid-set-p space right)
      (q3984053-sets-equal-on-p space left right))
     (equal
      (q3984053-measure-value measure left)
      (q3984053-measure-value measure right)))))

(defun-sk q3984053-empty-measurable-zero-p
    (real-type space measurable measure)
  (forall (set)
    (implies
     (and
      (q3984053-family-member-p measurable set)
      (q3984053-empty-on-p space set))
     (equal
      (q3984053-measure-value measure set)
      (q3984053-ennreal-finite
       (q3984053-zero real-type))))))

(defun q3984053-measure-space-p
    (real-type space measurable measure)
  (and
   (q3984053-sigma-algebra-p space measurable)
   (q3984053-measure-values-p real-type measure)
   (q3984053-measure-extensional-p space measure)
   (q3984053-empty-measurable-zero-p
    real-type space measurable measure)
   (equal
    (q3984053-measure-value
     measure
     (q3984053-complement-set
      space (q3984053-full-set space)))
    (q3984053-ennreal-finite (q3984053-zero real-type)))
   (q3984053-countable-additivity-p
    real-type space measurable measure)))

(defun q3984053-unit-coordinates-p
    (real-type coordinates x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (let ((c
           (q3984053-coordinate
            coordinates x (- n 1))))
      (and
       (q3984053-leq
        real-type (q3984053-zero real-type) c)
       (q3984053-less
        real-type c (q3984053-one real-type))
       (q3984053-unit-coordinates-p
        real-type coordinates x (- n 1))))))

(defun-sk q3984053-unit-cell-coordinate-p
    (real-type space basis coordinates dimension)
  (forall (x)
    (iff
     (q3984053-set-member-p
      (q3984053-unit-cell-set
       space basis coordinates dimension)
      x)
     (and
      (q3984053-member-p space x)
      (q3984053-unit-coordinates-p
       real-type coordinates x dimension)))))

(defun-sk q3984053-translation-invariant-p
    (space measurable measure)
  (forall (set shift)
    (implies
     (and
      (q3984053-family-member-p measurable set)
      (q3984053-member-p space shift))
     (equal
      (q3984053-measure-value
       measure
       (q3984053-translate-set space set shift))
      (q3984053-measure-value measure set)))))

(defun q3984053-volume-space-p
    (real-type space basis coordinates dimension measurable measure)
  (and
   (q3984053-borel-space-p real-type space measurable)
   (q3984053-measure-space-p
    real-type space measurable measure)
   (q3984053-unit-cell-coordinate-p
    real-type space basis coordinates dimension)
   (q3984053-family-member-p
    measurable
    (q3984053-unit-cell-set
     space basis coordinates dimension))
   (equal
    (q3984053-measure-value
     measure
     (q3984053-unit-cell-set
      space basis coordinates dimension))
    (q3984053-ennreal-finite
     (q3984053-one real-type)))
   (q3984053-translation-invariant-p
    space measurable measure)))

;; Lebesgue lower integration and Bochner integration.

(defun-sk q3984053-function-into-p
    (domain codomain function)
  (forall (x)
    (implies
     (q3984053-member-p domain x)
     (q3984053-member-p
      codomain
      (q3984053-function-at function x)))))

(defun-sk q3984053-continuous-at-delta-p
    (real-type domain codomain function x epsilon delta)
  (forall (y)
    (implies
     (and
      (q3984053-member-p domain y)
      (q3984053-less
       real-type
       (q3984053-distance real-type domain y x)
       delta))
     (q3984053-less
      real-type
      (q3984053-distance
       real-type codomain
       (q3984053-function-at function y)
       (q3984053-function-at function x))
      epsilon))))

(defun-sk q3984053-continuous-at-epsilon-p
    (real-type domain codomain function x epsilon)
  (exists (delta)
    (and
     (q3984053-member-p real-type delta)
     (q3984053-positive-p real-type delta)
     (q3984053-continuous-at-delta-p
      real-type domain codomain function x epsilon delta))))

(defun-sk q3984053-continuous-at-p
    (real-type domain codomain function x)
  (forall (epsilon)
    (implies
     (and
      (q3984053-member-p real-type epsilon)
      (q3984053-positive-p real-type epsilon))
     (q3984053-continuous-at-epsilon-p
      real-type domain codomain function x epsilon))))

(defun-sk q3984053-continuous-function-p
    (real-type domain codomain function)
  (forall (x epsilon)
    (implies
     (and
      (q3984053-member-p domain x)
      (q3984053-member-p real-type epsilon)
      (q3984053-positive-p real-type epsilon))
     (q3984053-continuous-at-epsilon-p
      real-type domain codomain function x epsilon))))

(defun-sk q3984053-function-constructor-laws-p
    (real-type)
  (forall (type f g set value x)
    (and
     (equal
      (q3984053-function-at
       (q3984053-function-add type f g) x)
      (q3984053-add
       type
       (q3984053-function-at f x)
       (q3984053-function-at g x)))
     (equal
      (q3984053-function-at
       (q3984053-function-difference type f g) x)
      (q3984053-add
       type
       (q3984053-function-at f x)
       (q3984053-negate
        type (q3984053-function-at g x))))
     (equal
      (q3984053-function-at
       (q3984053-function-norm real-type type f) x)
      (q3984053-norm type (q3984053-function-at f x)))
     (equal
      (q3984053-function-at
       (q3984053-indicator-function real-type set) x)
      (if (q3984053-set-member-p set x)
          (q3984053-one real-type)
        (q3984053-zero real-type))))))

(defun-sk q3984053-fiber-set-law-p (domain)
  (forall (function value x)
    (iff
     (q3984053-set-member-p
      (q3984053-fiber-set function value)
      x)
     (and
      (q3984053-member-p domain x)
      (equal (q3984053-function-at function x) value)))))

(defun-sk q3984053-measurable-function-p
    (real-type domain measurable codomain function)
  (forall (center radius)
    (implies
     (and
      (q3984053-member-p codomain center)
      (q3984053-member-p real-type radius)
      (q3984053-positive-p real-type radius))
     (q3984053-family-member-p
      measurable
      (q3984053-preimage-set
       function
       (q3984053-open-ball-set
        codomain center radius))))))

(defun-sk q3984053-nonnegative-values-p
    (real-type domain function)
  (forall (x)
    (implies
     (q3984053-member-p domain x)
     (q3984053-leq
      real-type
      (q3984053-zero real-type)
      (q3984053-function-at function x)))))

(defun q3984053-nonnegative-measurable-p
    (real-type domain measurable function)
  (and
   (q3984053-function-into-p
    domain real-type function)
   (q3984053-measurable-function-p
    real-type domain measurable real-type function)
   (q3984053-nonnegative-values-p
    real-type domain function)))

(defun-sk q3984053-pointwise-leq-p
    (real-type domain left right)
  (forall (x)
    (implies
     (q3984053-member-p domain x)
     (q3984053-leq
      real-type
      (q3984053-function-at left x)
      (q3984053-function-at right x)))))

(defun-sk q3984053-functions-equal-on-p
    (domain left right)
  (forall (x)
    (implies
     (q3984053-member-p domain x)
     (equal
      (q3984053-function-at left x)
      (q3984053-function-at right x)))))

(defun-sk q3984053-lintegral-laws-p
    (real-type domain measurable measure lintegral)
  (forall (f g set)
    (and
     (implies
      (q3984053-functions-equal-on-p domain f g)
      (equal
       (q3984053-lintegral-value lintegral f)
       (q3984053-lintegral-value lintegral g)))
     (implies
      (q3984053-nonnegative-measurable-p
       real-type domain measurable f)
      (q3984053-ennreal-p
       real-type
       (q3984053-lintegral-value lintegral f)))
     (implies
      (and
       (q3984053-nonnegative-measurable-p
        real-type domain measurable f)
       (q3984053-nonnegative-measurable-p
        real-type domain measurable g)
       (q3984053-pointwise-leq-p real-type domain f g))
      (q3984053-ennreal-leq-p
       real-type
       (q3984053-lintegral-value lintegral f)
       (q3984053-lintegral-value lintegral g)))
     (implies
      (q3984053-family-member-p measurable set)
      (equal
       (q3984053-lintegral-value
        lintegral
        (q3984053-indicator-function real-type set))
       (q3984053-measure-value measure set)))
     (implies
      (and
       (q3984053-nonnegative-measurable-p
        real-type domain measurable f)
       (q3984053-nonnegative-measurable-p
        real-type domain measurable g))
      (equal
       (q3984053-lintegral-value
        lintegral
        (q3984053-function-add real-type f g))
       (q3984053-ennreal-add
        real-type
        (q3984053-lintegral-value lintegral f)
        (q3984053-lintegral-value lintegral g)))))))

(defun q3984053-simple-values-correct-p
    (domain measurable function values)
  (if (consp values)
      (and
       (q3984053-family-member-p
        measurable
        (q3984053-fiber-set function (car values)))
       (q3984053-simple-values-correct-p
        domain measurable function (cdr values)))
    (equal values nil)))

(defun q3984053-simple-listed-values-in-space-p
    (space values)
  (if (consp values)
      (and
       (q3984053-member-p space (car values))
       (q3984053-simple-listed-values-in-space-p
        space (cdr values)))
    (equal values nil)))

(defun-sk q3984053-simple-range-values-p
    (domain function values)
  (forall (x)
    (implies
     (q3984053-member-p domain x)
     (member-equal
      (q3984053-function-at function x)
      values))))

(defun-sk q3984053-value-attained-p
    (domain function value)
  (exists (x)
    (and
     (q3984053-member-p domain x)
     (equal
      (q3984053-function-at function x)
      value))))

(defun q3984053-simple-function-p
    (domain measurable space function)
  (and
   (q3984053-function-into-p domain space function)
   (true-listp (q3984053-simple-values function))
   (no-duplicatesp-equal (q3984053-simple-values function))
   (q3984053-simple-listed-values-in-space-p
    space (q3984053-simple-values function))
   (q3984053-simple-values-correct-p
    domain measurable function
    (q3984053-simple-values function))
   (q3984053-simple-range-values-p
    domain function
    (q3984053-simple-values function))))

(defun q3984053-simple-integrable-values-p
    (real-type domain measure zero function values)
  (if (consp values)
      (and
       (implies
        (not
         (q3984053-value-attained-p
          domain function (car values)))
        (equal
         (q3984053-measure-value
          measure
          (q3984053-fiber-set function (car values)))
         (q3984053-ennreal-finite
          (q3984053-zero real-type))))
       (or
        (equal (car values) zero)
        (not
         (equal
          (q3984053-measure-value
           measure
           (q3984053-fiber-set function (car values)))
          :q3984053-top)))
       (q3984053-simple-integrable-values-p
        real-type domain measure zero function (cdr values)))
    (equal values nil)))

(defun q3984053-simple-integral
    (real-type domain space measure function values)
  (if (consp values)
      (q3984053-add
       space
       (if (or
            (equal (car values) (q3984053-zero space))
            (not
             (q3984053-value-attained-p
              domain function (car values))))
           (q3984053-zero space)
         (q3984053-smul
          real-type space
          (cdr
           (q3984053-measure-value
            measure
            (q3984053-fiber-set function (car values))))
          (car values)))
       (q3984053-simple-integral
        real-type domain space measure function (cdr values)))
    (q3984053-zero space)))

(defun q3984053-ennreal-scale
    (real-type scalar value)
  (if (equal scalar (q3984053-zero real-type))
      (q3984053-ennreal-finite
       (q3984053-zero real-type))
    (if (equal value :q3984053-top)
        :q3984053-top
      (q3984053-ennreal-finite
       (q3984053-multiply
        real-type scalar (cdr value))))))

(defun q3984053-simple-nonnegative-integral
    (real-type domain measure function values)
  (if (consp values)
      (q3984053-ennreal-add
       real-type
       (if
           (q3984053-value-attained-p
            domain function (car values))
           (q3984053-ennreal-scale
            real-type
            (car values)
            (q3984053-measure-value
             measure
             (q3984053-fiber-set function (car values))))
         (q3984053-ennreal-finite
          (q3984053-zero real-type)))
       (q3984053-simple-nonnegative-integral
        real-type domain measure function (cdr values)))
    (q3984053-ennreal-finite
     (q3984053-zero real-type))))

(defun-sk q3984053-lintegral-upper-bound-p
    (real-type domain measurable measure function bound)
  (forall (simple)
    (implies
     (and
      (q3984053-simple-function-p
       domain measurable real-type simple)
      (q3984053-nonnegative-values-p
       real-type domain simple)
      (q3984053-pointwise-leq-p
       real-type domain simple function))
     (q3984053-ennreal-leq-p
      real-type
      (q3984053-simple-nonnegative-integral
       real-type domain measure simple
       (q3984053-simple-values simple))
      bound))))

(defun-sk q3984053-lintegral-least-upper-bound-p
    (real-type domain measurable measure function value)
  (forall (bound)
    (implies
     (and
      (q3984053-ennreal-p real-type bound)
      (q3984053-lintegral-upper-bound-p
       real-type domain measurable measure function bound))
     (q3984053-ennreal-leq-p real-type value bound))))

(defun-sk q3984053-lintegral-supremum-laws-p
    (real-type domain measurable measure lintegral)
  (forall (function)
    (implies
     (q3984053-nonnegative-measurable-p
      real-type domain measurable function)
     (let ((value
            (q3984053-lintegral-value
             lintegral function)))
       (and
        (q3984053-ennreal-p real-type value)
        (q3984053-lintegral-upper-bound-p
         real-type domain measurable measure function value)
        (q3984053-lintegral-least-upper-bound-p
         real-type domain measurable measure function value))))))

(defun-sk q3984053-simple-sequence-p
    (domain measurable space sequence)
  (forall (n)
    (implies
     (natp n)
     (q3984053-simple-function-p
      domain measurable space
      (q3984053-sequence-at sequence n)))))

(defun-sk q3984053-pointwise-simple-limit-p
    (real-type domain space sequence function)
  (forall (x)
    (implies
     (q3984053-member-p domain x)
     (q3984053-converges-p
      real-type
      space
      (q3984053-point-sequence sequence x)
      (q3984053-function-at function x)))))

(defun-sk q3984053-point-sequence-laws-p ()
  (forall (sequence x n)
    (equal
     (q3984053-sequence-at
      (q3984053-point-sequence sequence x) n)
     (q3984053-function-at
      (q3984053-sequence-at sequence n) x))))

(defun-sk q3984053-strongly-measurable-p
    (real-type domain measurable space function)
  (exists (sequence)
    (and
     (q3984053-simple-sequence-p
      domain measurable space sequence)
     (q3984053-pointwise-simple-limit-p
      real-type domain space sequence function))))

(defun-sk q3984053-equal-outside-p
    (domain exceptional left right)
  (forall (x)
    (implies
     (and
      (q3984053-member-p domain x)
      (not (q3984053-set-member-p exceptional x)))
     (equal
      (q3984053-function-at left x)
      (q3984053-function-at right x)))))

(defun-sk q3984053-almost-everywhere-equal-p
    (real-type domain measurable measure left right)
  (exists (exceptional)
    (and
     (q3984053-family-member-p measurable exceptional)
     (equal
      (q3984053-measure-value measure exceptional)
      (q3984053-ennreal-finite
       (q3984053-zero real-type)))
     (q3984053-equal-outside-p
      domain exceptional left right))))

(defun-sk q3984053-aestrongly-measurable-p
    (real-type domain measurable measure space function)
  (exists (representative)
    (and
     (q3984053-strongly-measurable-p
      real-type domain measurable space representative)
     (q3984053-almost-everywhere-equal-p
      real-type domain measurable measure
      function representative))))

(defun q3984053-integrable-p
    (real-type domain measurable measure lintegral space function)
  (and
   (q3984053-aestrongly-measurable-p
    real-type domain measurable measure space function)
   (not
    (equal
     (q3984053-lintegral-value
      lintegral
      (q3984053-function-norm real-type space function))
     :q3984053-top))))

(defun q3984053-l1-distance
    (real-type space lintegral left right)
  (q3984053-lintegral-value
   lintegral
   (q3984053-function-norm
    real-type space
    (q3984053-function-difference space left right))))

(defun-sk q3984053-l1-tail-p
    (real-type space lintegral sequence function epsilon start)
  (forall (n)
    (implies
     (and (natp n) (natp start) (<= start n))
     (q3984053-ennreal-leq-p
      real-type
      (q3984053-l1-distance
       real-type space lintegral
       (q3984053-sequence-at sequence n)
       function)
      (q3984053-ennreal-finite epsilon)))))

(defun-sk q3984053-l1-start-p
    (real-type space lintegral sequence function epsilon)
  (exists (start)
    (and
     (natp start)
     (q3984053-l1-tail-p
      real-type space lintegral
      sequence function epsilon start))))

(defun-sk q3984053-l1-converges-p
    (real-type space lintegral sequence function)
  (forall (epsilon)
    (implies
     (and
      (q3984053-member-p real-type epsilon)
      (q3984053-positive-p real-type epsilon))
     (q3984053-l1-start-p
      real-type space lintegral sequence function epsilon))))

(defun-sk q3984053-integrable-simple-sequence-p
    (real-type domain measurable measure space sequence)
  (forall (n)
    (implies
     (natp n)
     (let ((f (q3984053-sequence-at sequence n)))
       (and
        (q3984053-simple-function-p
         domain measurable space f)
        (q3984053-simple-integrable-values-p
         real-type domain measure
         (q3984053-zero space) f
         (q3984053-simple-values f)))))))

(defun-sk q3984053-simple-integral-sequence-laws-p ()
  (forall (real-type domain space measure sequence n)
    (equal
     (q3984053-sequence-at
      (q3984053-simple-integral-sequence
       real-type domain space measure sequence)
      n)
     (q3984053-simple-integral
      real-type domain space measure
      (q3984053-sequence-at sequence n)
      (q3984053-simple-values
       (q3984053-sequence-at sequence n))))))

(defun q3984053-bochner-approximation-p
    (real-type domain measurable measure lintegral
     space function value sequence)
  (and
   (q3984053-integrable-simple-sequence-p
    real-type domain measurable measure space sequence)
   (q3984053-l1-converges-p
    real-type space lintegral sequence function)
   (q3984053-converges-p
    real-type space
    (q3984053-simple-integral-sequence
     real-type domain space measure sequence)
    value)))

(defun-sk q3984053-bochner-approximation-exists-p
    (real-type domain measurable measure lintegral
     space function value)
  (exists (sequence)
    (q3984053-bochner-approximation-p
     real-type domain measurable measure lintegral
     space function value sequence)))

(defun-sk q3984053-bochner-integral-operation-p
    (real-type domain measurable measure lintegral space integral)
  (forall (function other)
    (and
     (implies
      (q3984053-functions-equal-on-p
       domain function other)
      (equal
       (q3984053-bochner-integral-value
        integral function)
       (q3984053-bochner-integral-value
        integral other)))
     (implies
      (q3984053-function-into-p domain space function)
      (let ((value
             (q3984053-bochner-integral-value
              integral function)))
        (and
         (q3984053-member-p space value)
         (if
             (and
              (q3984053-complete-p real-type space)
              (q3984053-integrable-p
               real-type domain measurable measure lintegral
               space function))
             (q3984053-bochner-approximation-exists-p
              real-type domain measurable measure lintegral
              space function value)
           (equal value (q3984053-zero space)))))))))

;; The normalized Fourier character.

(defun-sk q3984053-character-kernel-witness-p
    (real-type complex-type fourier-char x)
  (exists (n)
    (and
     (integerp n)
     (equal x (q3984053-integer-cast real-type n)))))

(defun-sk q3984053-character-laws-p
    (real-type complex-type fourier-char)
  (forall (x y)
    (implies
     (and
      (q3984053-member-p real-type x)
      (q3984053-member-p real-type y))
     (and
      (q3984053-member-p
       complex-type
       (q3984053-character-value fourier-char x))
      (equal
       (q3984053-character-value
        fourier-char (q3984053-add real-type x y))
       (q3984053-multiply
        complex-type
        (q3984053-character-value fourier-char x)
        (q3984053-character-value fourier-char y)))
      (equal
       (q3984053-norm
        complex-type
        (q3984053-character-value fourier-char x))
       (q3984053-one real-type))
      (iff
       (equal
        (q3984053-character-value fourier-char x)
        (q3984053-one complex-type))
       (q3984053-character-kernel-witness-p
        real-type complex-type fourier-char x))))))

(defun-sk q3984053-character-orientation-delta-p
    (real-type complex-type fourier-char delta)
  (forall (x)
    (implies
     (and
      (q3984053-member-p real-type x)
      (q3984053-positive-p real-type x)
      (q3984053-less real-type x delta))
     (q3984053-less
      real-type
      (q3984053-zero real-type)
      (q3984053-imag-part
       real-type complex-type
       (q3984053-character-value fourier-char x))))))

(defun-sk q3984053-character-orientation-p
    (real-type complex-type fourier-char)
  (exists (delta)
    (and
     (q3984053-member-p real-type delta)
     (q3984053-positive-p real-type delta)
     (q3984053-character-orientation-delta-p
      real-type complex-type fourier-char delta))))

(defun-sk q3984053-character-continuity-delta-p
    (real-type complex-type fourier-char epsilon delta)
  (forall (x)
    (implies
     (and
      (q3984053-member-p real-type x)
      (q3984053-less
       real-type
       (q3984053-abs real-type x)
       delta))
     (q3984053-less
      real-type
      (q3984053-distance
       real-type complex-type
       (q3984053-character-value fourier-char x)
       (q3984053-one complex-type))
      epsilon))))

(defun-sk q3984053-character-continuity-epsilon-p
    (real-type complex-type fourier-char epsilon)
  (exists (delta)
    (and
     (q3984053-member-p real-type delta)
     (q3984053-positive-p real-type delta)
     (q3984053-character-continuity-delta-p
      real-type complex-type fourier-char epsilon delta))))

(defun-sk q3984053-character-continuity-p
    (real-type complex-type fourier-char)
  (forall (epsilon)
    (implies
     (and
      (q3984053-member-p real-type epsilon)
      (q3984053-positive-p real-type epsilon))
     (q3984053-character-continuity-epsilon-p
      real-type complex-type fourier-char epsilon))))

(defun q3984053-fourier-character-p
    (real-type complex-type fourier-char)
  (and
   (equal
    (q3984053-character-value
     fourier-char (q3984053-zero real-type))
    (q3984053-one complex-type))
   (q3984053-character-laws-p
    real-type complex-type fourier-char)
   (q3984053-character-continuity-p
    real-type complex-type fourier-char)
   (q3984053-character-orientation-p
    real-type complex-type fourier-char)))


(defun-sk q3984053-fourier-integrand-laws-p
    (real-type complex-type domain space fourier-char)
  (forall (f frequency x)
    (equal
     (q3984053-function-at
      (q3984053-fourier-integrand
       real-type complex-type domain space
       fourier-char f frequency)
      x)
     (q3984053-smul
      complex-type space
      (q3984053-character-value
       fourier-char
       (q3984053-negate
        real-type
        (q3984053-inner
         real-type domain x frequency)))
      (q3984053-function-at f x)))))

(defun-sk q3984053-inverse-fourier-integrand-laws-p
    (real-type complex-type domain space fourier-char)
  (forall (f frequency x)
    (equal
     (q3984053-function-at
      (q3984053-inverse-fourier-integrand
       real-type complex-type domain space
       fourier-char f frequency)
      x)
     (q3984053-smul
      complex-type space
      (q3984053-character-value
       fourier-char
       (q3984053-inner
        real-type domain x frequency))
      (q3984053-function-at f x)))))

(defun-sk q3984053-fourier-transform-correct-p
    (real-type complex-type domain space
     fourier-char integral fourier function)
  (forall (frequency)
    (implies
     (q3984053-member-p domain frequency)
     (and
      (q3984053-member-p
       space
       (q3984053-function-at
        (q3984053-fourier-function fourier function)
        frequency))
      (equal
       (q3984053-function-at
        (q3984053-fourier-function fourier function)
        frequency)
       (q3984053-bochner-integral-value
        integral
        (q3984053-fourier-integrand
         real-type complex-type domain space
         fourier-char function frequency)))))))

(defun-sk q3984053-fourier-inverse-correct-p
    (real-type complex-type domain space
     fourier-char integral fourier-inverse function)
  (forall (frequency)
    (implies
     (q3984053-member-p domain frequency)
     (and
      (q3984053-member-p
       space
       (q3984053-function-at
        (q3984053-fourier-inverse-function
         fourier-inverse function)
        frequency))
      (equal
       (q3984053-function-at
        (q3984053-fourier-inverse-function
         fourier-inverse function)
        frequency)
       (q3984053-bochner-integral-value
        integral
        (q3984053-inverse-fourier-integrand
         real-type complex-type domain space
         fourier-char function frequency)))))))

;; The source theorem, with every implicit typeclass and analytic construction
;; represented by the explicit hypotheses above.

(defun q3984053-fourier-inversion-context-p
    (real-type complex-type domain space
     basis coordinates dimension
     measurable measure lintegral
     space-integral fourier-char
     fourier fourier-inverse f)
  (and
   (q3984053-complex-field-p real-type complex-type)
   (q3984053-finite-real-inner-product-space-p
    real-type domain basis coordinates dimension)
   (q3984053-complex-banach-space-p
    real-type complex-type space)
   (q3984053-set-constructor-laws-p real-type domain)
   (q3984053-set-constructor-laws-p real-type real-type)
   (q3984053-set-constructor-laws-p real-type space)
   (q3984053-preimage-set-law-p domain)
   (q3984053-fiber-set-law-p domain)
   (q3984053-function-constructor-laws-p real-type)
   (q3984053-point-sequence-laws-p)
   (q3984053-simple-integral-sequence-laws-p)
   (q3984053-volume-space-p
    real-type domain basis coordinates dimension
    measurable measure)
   (q3984053-lintegral-laws-p
    real-type domain measurable measure lintegral)
   (q3984053-lintegral-supremum-laws-p
    real-type domain measurable measure lintegral)
   (q3984053-bochner-integral-operation-p
    real-type domain measurable measure lintegral
    space space-integral)
   (q3984053-fourier-character-p
    real-type complex-type fourier-char)
   (q3984053-fourier-integrand-laws-p
    real-type complex-type domain space fourier-char)
   (q3984053-inverse-fourier-integrand-laws-p
    real-type complex-type domain space fourier-char)
   (q3984053-function-into-p domain space f)
   (q3984053-fourier-transform-correct-p
    real-type complex-type domain space
    fourier-char space-integral fourier f)
   (q3984053-fourier-inverse-correct-p
    real-type complex-type domain space
    fourier-char space-integral fourier-inverse
    (q3984053-fourier-function fourier f))))

(defun q3984053-fourier-inversion-assumptions-p
    (real-type complex-type domain space
     basis coordinates dimension
     measurable measure lintegral
     space-integral fourier-char
     fourier fourier-inverse f)
  (and
   (q3984053-fourier-inversion-context-p
    real-type complex-type domain space
    basis coordinates dimension
    measurable measure lintegral
    space-integral fourier-char
    fourier fourier-inverse f)
   (q3984053-integrable-p
    real-type domain measurable measure lintegral
    space f)
   (q3984053-integrable-p
    real-type domain measurable measure lintegral
    space
    (q3984053-fourier-function fourier f))))

(defun thousand-theorems-q3984053-fourier-inversion-theorem-statement
    (real-type complex-type domain space
     basis coordinates dimension
     measurable measure lintegral
     space-integral fourier-char
     fourier fourier-inverse f)
  (implies
   (and
    (q3984053-fourier-inversion-assumptions-p
     real-type complex-type domain space
     basis coordinates dimension
     measurable measure lintegral
     space-integral fourier-char
     fourier fourier-inverse f)
    (q3984053-continuous-function-p
     real-type domain space f))
   (q3984053-functions-equal-on-p
    domain
    (q3984053-fourier-inverse-function
     fourier-inverse
     (q3984053-fourier-function fourier f))
    f)))

(value-triple :itpeval-statement-checked)
:q
