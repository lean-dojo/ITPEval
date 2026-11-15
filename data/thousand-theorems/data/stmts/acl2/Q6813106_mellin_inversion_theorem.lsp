;; Statement-only formalization of thousand-theorems corpus artifact Q6813106,
;; "Mellin inversion theorem": for a complex Banach-valued function with a
;; convergent Mellin transform on a vertical line, integrable transform along
;; that line, and continuity at a positive point, inverse Mellin transformation
;; recovers the function there. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Mathematical objects are unrestricted ACL2 objects.  The conservative
;; interfaces below only provide application and constructor symbols; every
;; field, space, topology, measure, integral, and Fourier law used by the
;; statement is imposed explicitly by predicates below.

(defstub q6813106-member-p (type object) t)
(defstub q6813106-zero (type) t)
(defstub q6813106-one (type) t)
(defstub q6813106-add (type left right) t)
(defstub q6813106-multiply (type left right) t)
(defstub q6813106-negate (type object) t)
(defstub q6813106-inverse (type object) t)
(defstub q6813106-less (type left right) t)
(defstub q6813106-norm (type object) t)
(defstub q6813106-smul (scalar-type space scalar vector) t)
(defstub q6813106-star (scalar-type scalar) t)
(defstub q6813106-real-part (real-type scalar-type scalar) t)
(defstub q6813106-imag-part (real-type scalar-type scalar) t)
(defstub q6813106-of-real (real-type scalar-type real) t)
(defstub q6813106-imaginary-unit (scalar-type) t)
(defstub q6813106-inner (scalar-type space left right) t)
(defstub q6813106-function-at (function argument) t)
(defstub q6813106-sequence-at (sequence index) t)
(defstub q6813106-basis-at (basis index) t)
(defstub q6813106-coordinate (coordinates vector index) t)
(defstub q6813106-fourier-function (fourier function) t)
(defstub q6813106-fourier-inverse-function (fourier-inverse function) t)
(defstub q6813106-character-value (fourier-char real) t)
(defstub q6813106-set-member-p (set object) t)
(defstub q6813106-family-member-p (family set) t)
(defstub q6813106-open-ball-set (space center radius) t)
(defstub q6813106-preimage-set (function set) t)
(defstub q6813106-complement-set (carrier set) t)
(defstub q6813106-countable-union-set (carrier sequence) t)
(defstub q6813106-translate-set (space set shift) t)
(defstub q6813106-unit-cell-set (space basis coordinates dimension) t)
(defstub q6813106-fiber-set (function value) t)
(defstub q6813106-simple-values (function) t)
(defstub q6813106-indicator-function (real-type set) t)
(defstub q6813106-function-add (type left right) t)
(defstub q6813106-function-difference (type left right) t)
(defstub q6813106-function-norm (real-type type function) t)
(defstub q6813106-fourier-integrand
  (real-type scalar-type domain space fourier-char function frequency) t)
(defstub q6813106-inverse-fourier-integrand
  (real-type scalar-type domain space fourier-char function frequency) t)
(defstub q6813106-measure-value (measure set) t)
(defstub q6813106-lintegral-value (lintegral function) t)
(defstub q6813106-bochner-integral-value (integral function) t)
(defstub q6813106-full-set (carrier) t)
(defstub q6813106-point-sequence (function-sequence point) t)
(defstub q6813106-simple-integral-sequence
  (real-type domain space measure function-sequence) t)
(defstub q6813106-exponential-sequence (real-type x) t)
(defstub q6813106-real-exponential (real-type x) t)
(defstub q6813106-real-logarithm (real-type x) t)
(defstub q6813106-mellin-coordinate-function
  (real-type complex-type space sigma function) t)

(defun q6813106-positive-p (real-type x)
  (q6813106-less real-type (q6813106-zero real-type) x))

(defun q6813106-leq (real-type x y)
  (not (q6813106-less real-type y x)))

(defun q6813106-abs (real-type x)
  (if (q6813106-less real-type x (q6813106-zero real-type))
      (q6813106-negate real-type x)
    x))

(defun q6813106-natural-cast (type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q6813106-zero type)
    (q6813106-add
     type
     (q6813106-one type)
     (q6813106-natural-cast type (- n 1)))))

(defun q6813106-integer-cast (type n)
  (if (and (integerp n) (< n 0))
      (q6813106-negate
       type
       (q6813106-natural-cast type (- n)))
    (q6813106-natural-cast type (nfix n))))


(defun q6813106-vector-sum
    (real-type space basis coordinates vector n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q6813106-zero space)
    (let ((i (- n 1)))
      (q6813106-add
       space
       (q6813106-vector-sum
        real-type space basis coordinates vector i)
       (q6813106-smul
        real-type space
        (q6813106-coordinate coordinates vector i)
        (q6813106-basis-at basis i))))))


;; Complete ordered real field and its canonical complexification.

(defun-sk q6813106-field-laws-p (type)
  (forall (x y z)
    (implies
     (and
      (q6813106-member-p type x)
      (q6813106-member-p type y)
      (q6813106-member-p type z))
     (and
      (q6813106-member-p type (q6813106-add type x y))
      (q6813106-member-p type (q6813106-multiply type x y))
      (q6813106-member-p type (q6813106-negate type x))
      (implies
       (not (equal x (q6813106-zero type)))
       (q6813106-member-p type (q6813106-inverse type x)))
      (equal
       (q6813106-add type (q6813106-add type x y) z)
       (q6813106-add type x (q6813106-add type y z)))
      (equal (q6813106-add type x y) (q6813106-add type y x))
      (equal (q6813106-add type x (q6813106-zero type)) x)
      (equal
       (q6813106-add type x (q6813106-negate type x))
       (q6813106-zero type))
      (equal
       (q6813106-multiply type (q6813106-multiply type x y) z)
       (q6813106-multiply type x (q6813106-multiply type y z)))
      (equal
       (q6813106-multiply type x y)
       (q6813106-multiply type y x))
      (equal (q6813106-multiply type x (q6813106-one type)) x)
      (implies
       (not (equal x (q6813106-zero type)))
       (equal
        (q6813106-multiply type x (q6813106-inverse type x))
        (q6813106-one type)))
      (equal
       (q6813106-multiply type x (q6813106-add type y z))
       (q6813106-add
        type
        (q6813106-multiply type x y)
        (q6813106-multiply type x z)))))))

(defun-sk q6813106-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q6813106-member-p real-type x)
      (q6813106-member-p real-type y)
      (q6813106-member-p real-type z))
     (and
      (not (q6813106-less real-type x x))
      (or
       (q6813106-less real-type x y)
       (equal x y)
       (q6813106-less real-type y x))
      (implies
       (and
        (q6813106-less real-type x y)
        (q6813106-less real-type y z))
       (q6813106-less real-type x z))
      (implies
       (q6813106-less real-type x y)
       (q6813106-less
        real-type
        (q6813106-add real-type x z)
        (q6813106-add real-type y z)))
      (implies
       (and
        (q6813106-positive-p real-type x)
        (q6813106-positive-p real-type y))
       (q6813106-positive-p
        real-type
        (q6813106-multiply real-type x y)))))))

(defun q6813106-distance
    (real-type type x y)
  (declare (ignore real-type))
  (q6813106-norm
   type
   (q6813106-add type x (q6813106-negate type y))))

(defun-sk q6813106-norm-values-p (real-type type)
  (forall (x)
    (implies
     (q6813106-member-p type x)
     (and
      (q6813106-member-p real-type (q6813106-norm type x))
      (q6813106-leq
       real-type
       (q6813106-zero real-type)
       (q6813106-norm type x))
      (iff
       (equal
        (q6813106-norm type x)
        (q6813106-zero real-type))
       (equal x (q6813106-zero type)))))))

(defun-sk q6813106-norm-triangle-p (real-type type)
  (forall (x y)
    (implies
     (and
      (q6813106-member-p type x)
      (q6813106-member-p type y))
     (q6813106-leq
      real-type
      (q6813106-norm type (q6813106-add type x y))
      (q6813106-add
       real-type
       (q6813106-norm type x)
       (q6813106-norm type y))))))

(defun q6813106-norm-laws-p (real-type type)
  (and
   (q6813106-norm-values-p real-type type)
   (q6813106-norm-triangle-p real-type type)))

(defun-sk q6813106-convergence-tail-p
    (real-type type sequence limit epsilon start)
  (forall (n)
    (implies
     (and (natp n) (natp start) (<= start n))
     (q6813106-less
      real-type
      (q6813106-distance
       real-type type
       (q6813106-sequence-at sequence n)
       limit)
      epsilon))))

(defun-sk q6813106-convergence-start-p
    (real-type type sequence limit epsilon)
  (exists (start)
    (and
     (natp start)
     (q6813106-convergence-tail-p
      real-type type sequence limit epsilon start))))

(defun-sk q6813106-converges-p
    (real-type type sequence limit)
  (forall (epsilon)
    (implies
     (and
      (q6813106-member-p real-type epsilon)
      (q6813106-positive-p real-type epsilon))
     (q6813106-convergence-start-p
      real-type type sequence limit epsilon))))

(defun-sk q6813106-cauchy-tail-p
    (real-type type sequence epsilon start)
  (forall (m n)
    (implies
     (and
      (natp m) (natp n) (natp start)
      (<= start m) (<= start n))
     (q6813106-less
      real-type
      (q6813106-distance
       real-type type
       (q6813106-sequence-at sequence m)
       (q6813106-sequence-at sequence n))
      epsilon))))

(defun-sk q6813106-cauchy-start-p
    (real-type type sequence epsilon)
  (exists (start)
    (and
     (natp start)
     (q6813106-cauchy-tail-p
      real-type type sequence epsilon start))))

(defun-sk q6813106-cauchy-p (real-type type sequence)
  (forall (epsilon)
    (implies
     (and
      (q6813106-member-p real-type epsilon)
      (q6813106-positive-p real-type epsilon))
     (q6813106-cauchy-start-p
      real-type type sequence epsilon))))

(defun-sk q6813106-sequence-in-type-p (type sequence)
  (forall (n)
    (implies
     (natp n)
     (q6813106-member-p
      type
      (q6813106-sequence-at sequence n)))))

(defun-sk q6813106-limit-exists-p
    (real-type type sequence)
  (exists (limit)
    (and
     (q6813106-member-p type limit)
     (q6813106-converges-p
      real-type type sequence limit))))

(defun-sk q6813106-complete-p (real-type type)
  (forall (sequence)
    (implies
     (and
      (q6813106-sequence-in-type-p type sequence)
      (q6813106-cauchy-p real-type type sequence))
     (q6813106-limit-exists-p
      real-type type sequence))))

(defun-sk q6813106-archimedean-witness-p (real-type x)
  (exists (n)
    (and
     (natp n)
     (q6813106-less
      real-type x
      (q6813106-natural-cast real-type n)))))

(defun-sk q6813106-archimedean-p (real-type)
  (forall (x)
    (implies
     (q6813106-member-p real-type x)
     (q6813106-archimedean-witness-p real-type x))))

(defun-sk q6813106-real-norm-laws-p (real-type)
  (forall (x)
    (implies
     (q6813106-member-p real-type x)
     (and
      (equal
       (q6813106-norm real-type x)
       (q6813106-abs real-type x))
      (equal (q6813106-star real-type x) x)
      (equal
       (q6813106-real-part real-type real-type x)
       x)
      (equal
       (q6813106-imag-part real-type real-type x)
       (q6813106-zero real-type))
      (equal
       (q6813106-of-real real-type real-type x)
       x)))))

(defun q6813106-real-field-p (real-type)
  (and
   (q6813106-member-p real-type (q6813106-zero real-type))
   (q6813106-member-p real-type (q6813106-one real-type))
   (not
    (equal
     (q6813106-zero real-type)
     (q6813106-one real-type)))
   (q6813106-field-laws-p real-type)
   (q6813106-order-laws-p real-type)
   (q6813106-positive-p real-type (q6813106-one real-type))
   (q6813106-real-norm-laws-p real-type)
   (q6813106-complete-p real-type real-type)
   (q6813106-archimedean-p real-type)))

(defun-sk q6813106-complex-coordinate-laws-p
    (real-type complex-type)
  (forall (z)
    (implies
     (q6813106-member-p complex-type z)
     (let* ((re (q6813106-real-part real-type complex-type z))
            (im (q6813106-imag-part real-type complex-type z))
            (re-z (q6813106-of-real real-type complex-type re))
            (im-z
             (q6813106-multiply
              complex-type
              (q6813106-of-real real-type complex-type im)
              (q6813106-imaginary-unit complex-type))))
       (and
        (q6813106-member-p real-type re)
        (q6813106-member-p real-type im)
        (equal z (q6813106-add complex-type re-z im-z))
        (equal
         (q6813106-star complex-type z)
         (q6813106-add
          complex-type re-z
          (q6813106-negate complex-type im-z)))
        (equal
         (q6813106-multiply
          real-type
          (q6813106-norm complex-type z)
          (q6813106-norm complex-type z))
         (q6813106-add
          real-type
          (q6813106-multiply real-type re re)
          (q6813106-multiply real-type im im))))))))

(defun-sk q6813106-of-real-laws-p
    (real-type complex-type)
  (forall (x y)
    (implies
     (and
      (q6813106-member-p real-type x)
      (q6813106-member-p real-type y))
     (and
      (q6813106-member-p
       complex-type
       (q6813106-of-real real-type complex-type x))
      (equal
       (q6813106-real-part
        real-type complex-type
        (q6813106-of-real real-type complex-type x))
       x)
      (equal
       (q6813106-imag-part
        real-type complex-type
        (q6813106-of-real real-type complex-type x))
       (q6813106-zero real-type))
      (equal
       (q6813106-of-real
        real-type complex-type
        (q6813106-add real-type x y))
       (q6813106-add
        complex-type
        (q6813106-of-real real-type complex-type x)
        (q6813106-of-real real-type complex-type y)))
      (equal
       (q6813106-of-real
        real-type complex-type
        (q6813106-multiply real-type x y))
       (q6813106-multiply
        complex-type
        (q6813106-of-real real-type complex-type x)
        (q6813106-of-real real-type complex-type y)))))))

(defun q6813106-complex-field-p
    (real-type complex-type)
  (and
   (q6813106-real-field-p real-type)
   (q6813106-member-p complex-type (q6813106-zero complex-type))
   (q6813106-member-p complex-type (q6813106-one complex-type))
   (not
    (equal
     (q6813106-zero complex-type)
     (q6813106-one complex-type)))
   (q6813106-field-laws-p complex-type)
   (q6813106-of-real-laws-p real-type complex-type)
   (equal
    (q6813106-of-real
     real-type complex-type (q6813106-zero real-type))
    (q6813106-zero complex-type))
   (equal
    (q6813106-of-real
     real-type complex-type (q6813106-one real-type))
    (q6813106-one complex-type))
   (equal
    (q6813106-multiply
     complex-type
     (q6813106-imaginary-unit complex-type)
     (q6813106-imaginary-unit complex-type))
    (q6813106-negate complex-type (q6813106-one complex-type)))
   (equal
    (q6813106-real-part
     real-type complex-type
     (q6813106-imaginary-unit complex-type))
    (q6813106-zero real-type))
   (equal
    (q6813106-imag-part
     real-type complex-type
     (q6813106-imaginary-unit complex-type))
    (q6813106-one real-type))
   (q6813106-complex-coordinate-laws-p real-type complex-type)
   (q6813106-norm-laws-p real-type complex-type)
   (q6813106-complete-p real-type complex-type)))

;; Real inner-product domains and complex Banach codomains.

(defun-sk q6813106-vector-space-laws-p
    (scalar-type space)
  (forall (a b x y z)
    (implies
     (and
      (q6813106-member-p scalar-type a)
      (q6813106-member-p scalar-type b)
      (q6813106-member-p space x)
      (q6813106-member-p space y)
      (q6813106-member-p space z))
     (and
      (q6813106-member-p space (q6813106-add space x y))
      (q6813106-member-p space (q6813106-negate space x))
      (q6813106-member-p
       space (q6813106-smul scalar-type space a x))
      (equal
       (q6813106-add space (q6813106-add space x y) z)
       (q6813106-add space x (q6813106-add space y z)))
      (equal (q6813106-add space x y) (q6813106-add space y x))
      (equal (q6813106-add space x (q6813106-zero space)) x)
      (equal
       (q6813106-add space x (q6813106-negate space x))
       (q6813106-zero space))
      (equal
       (q6813106-smul
        scalar-type space (q6813106-one scalar-type) x)
       x)
      (equal
       (q6813106-smul
        scalar-type space
        (q6813106-multiply scalar-type a b) x)
       (q6813106-smul
        scalar-type space a
        (q6813106-smul scalar-type space b x)))
      (equal
       (q6813106-smul
        scalar-type space
        (q6813106-add scalar-type a b) x)
       (q6813106-add
        space
        (q6813106-smul scalar-type space a x)
        (q6813106-smul scalar-type space b x)))
      (equal
       (q6813106-smul
        scalar-type space a (q6813106-add space x y))
       (q6813106-add
        space
        (q6813106-smul scalar-type space a x)
        (q6813106-smul scalar-type space a y)))))))

(defun-sk q6813106-normed-space-laws-p
    (real-type scalar-type space)
  (forall (a x)
    (implies
     (and
      (q6813106-member-p scalar-type a)
      (q6813106-member-p space x))
     (equal
      (q6813106-norm
       space
       (q6813106-smul scalar-type space a x))
      (q6813106-multiply
       real-type
       (q6813106-norm scalar-type a)
       (q6813106-norm space x))))))

(defun-sk q6813106-inner-product-laws-p
    (real-type scalar-type space)
  (forall (a x y z)
    (implies
     (and
      (q6813106-member-p scalar-type a)
      (q6813106-member-p space x)
      (q6813106-member-p space y)
      (q6813106-member-p space z))
     (let ((xy (q6813106-inner scalar-type space x y))
           (xx (q6813106-inner scalar-type space x x)))
       (and
        (q6813106-member-p scalar-type xy)
        (equal
         (q6813106-inner
          scalar-type space x (q6813106-add space y z))
         (q6813106-add
          scalar-type xy
          (q6813106-inner scalar-type space x z)))
        (equal
         (q6813106-inner
          scalar-type space x
          (q6813106-smul scalar-type space a y))
         (q6813106-multiply scalar-type a xy))
        (equal
         (q6813106-inner scalar-type space y x)
         (q6813106-star scalar-type xy))
        (equal
         (q6813106-multiply
          real-type
          (q6813106-norm space x)
          (q6813106-norm space x))
         (q6813106-real-part real-type scalar-type xx))
        (iff
         (equal xx (q6813106-zero scalar-type))
         (equal x (q6813106-zero space))))))))

(defun-sk q6813106-real-smul-compatibility-p
    (real-type complex-type space)
  (forall (r x)
    (implies
     (and
      (q6813106-member-p real-type r)
      (q6813106-member-p space x))
     (equal
      (q6813106-smul real-type space r x)
      (q6813106-smul
       complex-type space
       (q6813106-of-real real-type complex-type r)
       x)))))

(defun-sk q6813106-orthonormal-basis-laws-p
    (real-type space basis coordinates dimension)
  (forall (i j x)
    (and
     (implies
      (and (natp i) (< i dimension))
      (q6813106-member-p space (q6813106-basis-at basis i)))
     (implies
      (and
       (natp i) (natp j)
       (< i dimension) (< j dimension))
      (equal
       (q6813106-inner
        real-type space
        (q6813106-basis-at basis i)
        (q6813106-basis-at basis j))
       (if (equal i j)
           (q6813106-one real-type)
         (q6813106-zero real-type))))
     (implies
      (q6813106-member-p space x)
      (and
       (implies
        (and (natp i) (< i dimension))
        (q6813106-member-p
         real-type
         (q6813106-coordinate coordinates x i)))
       (equal
        x
        (q6813106-vector-sum
         real-type space basis coordinates x dimension)))))))

(defun q6813106-finite-real-inner-product-space-p
    (real-type space basis coordinates dimension)
  (and
   (natp dimension)
   (q6813106-member-p space (q6813106-zero space))
   (q6813106-vector-space-laws-p real-type space)
   (q6813106-norm-laws-p real-type space)
   (q6813106-normed-space-laws-p real-type real-type space)
   (q6813106-inner-product-laws-p real-type real-type space)
   (q6813106-orthonormal-basis-laws-p
    real-type space basis coordinates dimension)))

(defun q6813106-complex-banach-space-p
    (real-type complex-type space)
  (and
   (q6813106-member-p space (q6813106-zero space))
   (q6813106-vector-space-laws-p complex-type space)
   (q6813106-vector-space-laws-p real-type space)
   (q6813106-norm-laws-p real-type space)
   (q6813106-normed-space-laws-p
    real-type complex-type space)
   (q6813106-normed-space-laws-p
    real-type real-type space)
   (q6813106-real-smul-compatibility-p
    real-type complex-type space)
   (q6813106-complete-p real-type space)))

;; Borel sigma algebra and normalized translation-invariant volume.

(defun-sk q6813106-countable-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q6813106-set-member-p
      (q6813106-sequence-at sequence n) x))))

(defun-sk q6813106-valid-set-p (space set)
  (forall (x)
    (implies
     (q6813106-set-member-p set x)
     (q6813106-member-p space x))))

(defun-sk q6813106-sets-equal-on-p (space left right)
  (forall (x)
    (implies
     (q6813106-member-p space x)
     (iff
      (q6813106-set-member-p left x)
      (q6813106-set-member-p right x)))))

(defun-sk q6813106-empty-on-p (space set)
  (forall (x)
    (implies
     (q6813106-member-p space x)
     (not (q6813106-set-member-p set x)))))

(defun-sk q6813106-full-set-law-p (space)
  (forall (x)
    (iff
     (q6813106-set-member-p
      (q6813106-full-set space) x)
     (q6813106-member-p space x))))

(defun-sk q6813106-complement-set-law-p (space)
  (forall (set x)
    (iff
     (q6813106-set-member-p
      (q6813106-complement-set space set) x)
     (and
      (q6813106-member-p space x)
      (not (q6813106-set-member-p set x))))))

(defun-sk q6813106-countable-union-set-law-p (space)
  (forall (sequence x)
    (iff
     (q6813106-set-member-p
      (q6813106-countable-union-set space sequence) x)
     (and
      (q6813106-member-p space x)
      (q6813106-countable-union-member-p sequence x)))))

(defun-sk q6813106-open-ball-set-law-p (real-type space)
  (forall (center radius x)
    (iff
     (q6813106-set-member-p
      (q6813106-open-ball-set space center radius) x)
     (and
      (q6813106-member-p space x)
      (q6813106-member-p space center)
      (q6813106-member-p real-type radius)
      (q6813106-less
       real-type
       (q6813106-distance real-type space x center)
       radius)))))

(defun-sk q6813106-preimage-set-law-p (domain)
  (forall (function set x)
    (iff
     (q6813106-set-member-p
      (q6813106-preimage-set function set) x)
     (and
      (q6813106-member-p domain x)
      (q6813106-set-member-p
       set (q6813106-function-at function x))))))

(defun-sk q6813106-translate-set-law-p (space)
  (forall (set shift x)
    (iff
     (q6813106-set-member-p
      (q6813106-translate-set space set shift) x)
     (and
      (q6813106-member-p space x)
      (q6813106-set-member-p
       set
       (q6813106-add
        space x (q6813106-negate space shift)))))))

(defun q6813106-set-constructor-laws-p
    (real-type space)
  (and
   (q6813106-full-set-law-p space)
   (q6813106-complement-set-law-p space)
   (q6813106-countable-union-set-law-p space)
   (q6813106-open-ball-set-law-p real-type space)
   (q6813106-translate-set-law-p space)))

(defun-sk q6813106-sequence-measurable-p (family sequence)
  (forall (n)
    (implies
     (natp n)
     (q6813106-family-member-p
      family
      (q6813106-sequence-at sequence n)))))

(defun-sk q6813106-family-valid-sets-p (space family)
  (forall (set)
    (implies
     (q6813106-family-member-p family set)
     (q6813106-valid-set-p space set))))

(defun-sk q6813106-family-extensional-p (space family)
  (forall (left right)
    (implies
     (and
      (q6813106-family-member-p family left)
      (q6813106-valid-set-p space right)
      (q6813106-sets-equal-on-p space left right))
     (q6813106-family-member-p family right))))

(defun-sk q6813106-sigma-algebra-closure-p (space family)
  (forall (set sequence)
    (and
     (q6813106-family-member-p family (q6813106-full-set space))
     (implies
      (q6813106-family-member-p family set)
      (q6813106-family-member-p
       family (q6813106-complement-set space set)))
     (implies
      (q6813106-sequence-measurable-p family sequence)
      (q6813106-family-member-p
       family
       (q6813106-countable-union-set space sequence))))))

(defun q6813106-sigma-algebra-p (space family)
  (and
   (q6813106-family-valid-sets-p space family)
   (q6813106-family-extensional-p space family)
   (q6813106-sigma-algebra-closure-p space family)))

(defun-sk q6813106-balls-measurable-p
    (real-type space family)
  (forall (center radius)
    (implies
     (and
      (q6813106-member-p space center)
      (q6813106-member-p real-type radius)
      (q6813106-positive-p real-type radius))
     (q6813106-family-member-p
      family
      (q6813106-open-ball-set space center radius)))))

(defun-sk q6813106-family-subset-p (left right)
  (forall (set)
    (implies
     (q6813106-family-member-p left set)
     (q6813106-family-member-p right set))))

(defun-sk q6813106-borel-minimal-p
    (real-type space borel)
  (forall (candidate)
    (implies
     (and
      (q6813106-sigma-algebra-p space candidate)
      (q6813106-balls-measurable-p
       real-type space candidate))
     (q6813106-family-subset-p borel candidate))))

(defun q6813106-borel-space-p
    (real-type space borel)
  (and
   (q6813106-sigma-algebra-p space borel)
   (q6813106-balls-measurable-p real-type space borel)
   (q6813106-borel-minimal-p real-type space borel)))

(defun q6813106-ennreal-p (real-type x)
  (or
   (equal x :q6813106-top)
   (and
    (consp x)
    (equal (car x) :q6813106-finite)
    (q6813106-member-p real-type (cdr x))
    (q6813106-leq
     real-type (q6813106-zero real-type) (cdr x)))))

(defun q6813106-ennreal-finite (x)
  (cons :q6813106-finite x))

(defun q6813106-ennreal-add (real-type x y)
  (if (or
       (equal x :q6813106-top)
       (equal y :q6813106-top))
      :q6813106-top
    (q6813106-ennreal-finite
     (q6813106-add real-type (cdr x) (cdr y)))))

(defun q6813106-ennreal-leq-p (real-type x y)
  (or
   (equal y :q6813106-top)
   (and
    (not (equal x :q6813106-top))
    (q6813106-leq real-type (cdr x) (cdr y)))))

(defun-sk q6813106-disjoint-sequence-p
    (space sequence)
  (forall (i j x)
    (implies
     (and
      (natp i) (natp j)
      (not (equal i j))
      (q6813106-member-p space x))
     (not
      (and
       (q6813106-set-member-p
        (q6813106-sequence-at sequence i) x)
       (q6813106-set-member-p
        (q6813106-sequence-at sequence j) x))))))

(defun q6813106-ennreal-partial-sum
    (real-type measure sequence n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q6813106-ennreal-finite (q6813106-zero real-type))
    (q6813106-ennreal-add
     real-type
     (q6813106-ennreal-partial-sum
      real-type measure sequence (- n 1))
     (q6813106-measure-value
      measure
      (q6813106-sequence-at sequence (- n 1))))))

(defun-sk q6813106-ennreal-upper-bound-p
    (real-type measure sequence bound)
  (forall (n)
    (implies
     (natp n)
     (q6813106-ennreal-leq-p
      real-type
      (q6813106-ennreal-partial-sum
       real-type measure sequence n)
      bound))))

(defun-sk q6813106-ennreal-series-value-p
    (real-type measure sequence value)
  (forall (bound)
    (iff
     (q6813106-ennreal-upper-bound-p
      real-type measure sequence bound)
     (q6813106-ennreal-leq-p real-type value bound))))

(defun-sk q6813106-countable-additivity-p
    (real-type space measurable measure)
  (forall (sequence)
    (implies
     (and
      (q6813106-sequence-measurable-p measurable sequence)
      (q6813106-disjoint-sequence-p space sequence))
     (q6813106-ennreal-series-value-p
      real-type
      measure
      sequence
      (q6813106-measure-value
       measure
       (q6813106-countable-union-set space sequence))))))

(defun-sk q6813106-measure-values-p (real-type measure)
  (forall (set)
    (q6813106-ennreal-p
     real-type
     (q6813106-measure-value measure set))))

(defun-sk q6813106-measure-extensional-p (space measure)
  (forall (left right)
    (implies
     (and
      (q6813106-valid-set-p space left)
      (q6813106-valid-set-p space right)
      (q6813106-sets-equal-on-p space left right))
     (equal
      (q6813106-measure-value measure left)
      (q6813106-measure-value measure right)))))

(defun-sk q6813106-empty-measurable-zero-p
    (real-type space measurable measure)
  (forall (set)
    (implies
     (and
      (q6813106-family-member-p measurable set)
      (q6813106-empty-on-p space set))
     (equal
      (q6813106-measure-value measure set)
      (q6813106-ennreal-finite
       (q6813106-zero real-type))))))

(defun q6813106-measure-space-p
    (real-type space measurable measure)
  (and
   (q6813106-sigma-algebra-p space measurable)
   (q6813106-measure-values-p real-type measure)
   (q6813106-measure-extensional-p space measure)
   (q6813106-empty-measurable-zero-p
    real-type space measurable measure)
   (equal
    (q6813106-measure-value
     measure
     (q6813106-complement-set
      space (q6813106-full-set space)))
    (q6813106-ennreal-finite (q6813106-zero real-type)))
   (q6813106-countable-additivity-p
    real-type space measurable measure)))

(defun q6813106-unit-coordinates-p
    (real-type coordinates x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (let ((c
           (q6813106-coordinate
            coordinates x (- n 1))))
      (and
       (q6813106-leq
        real-type (q6813106-zero real-type) c)
       (q6813106-less
        real-type c (q6813106-one real-type))
       (q6813106-unit-coordinates-p
        real-type coordinates x (- n 1))))))

(defun-sk q6813106-unit-cell-coordinate-p
    (real-type space basis coordinates dimension)
  (forall (x)
    (iff
     (q6813106-set-member-p
      (q6813106-unit-cell-set
       space basis coordinates dimension)
      x)
     (and
      (q6813106-member-p space x)
      (q6813106-unit-coordinates-p
       real-type coordinates x dimension)))))

(defun-sk q6813106-translation-invariant-p
    (space measurable measure)
  (forall (set shift)
    (implies
     (and
      (q6813106-family-member-p measurable set)
      (q6813106-member-p space shift))
     (equal
      (q6813106-measure-value
       measure
       (q6813106-translate-set space set shift))
      (q6813106-measure-value measure set)))))

(defun q6813106-volume-space-p
    (real-type space basis coordinates dimension measurable measure)
  (and
   (q6813106-borel-space-p real-type space measurable)
   (q6813106-measure-space-p
    real-type space measurable measure)
   (q6813106-unit-cell-coordinate-p
    real-type space basis coordinates dimension)
   (q6813106-family-member-p
    measurable
    (q6813106-unit-cell-set
     space basis coordinates dimension))
   (equal
    (q6813106-measure-value
     measure
     (q6813106-unit-cell-set
      space basis coordinates dimension))
    (q6813106-ennreal-finite
     (q6813106-one real-type)))
   (q6813106-translation-invariant-p
    space measurable measure)))

;; Lebesgue lower integration and Bochner integration.

(defun-sk q6813106-function-into-p
    (domain codomain function)
  (forall (x)
    (implies
     (q6813106-member-p domain x)
     (q6813106-member-p
      codomain
      (q6813106-function-at function x)))))

(defun-sk q6813106-continuous-at-delta-p
    (real-type domain codomain function x epsilon delta)
  (forall (y)
    (implies
     (and
      (q6813106-member-p domain y)
      (q6813106-less
       real-type
       (q6813106-distance real-type domain y x)
       delta))
     (q6813106-less
      real-type
      (q6813106-distance
       real-type codomain
       (q6813106-function-at function y)
       (q6813106-function-at function x))
      epsilon))))

(defun-sk q6813106-continuous-at-epsilon-p
    (real-type domain codomain function x epsilon)
  (exists (delta)
    (and
     (q6813106-member-p real-type delta)
     (q6813106-positive-p real-type delta)
     (q6813106-continuous-at-delta-p
      real-type domain codomain function x epsilon delta))))

(defun-sk q6813106-continuous-at-p
    (real-type domain codomain function x)
  (forall (epsilon)
    (implies
     (and
      (q6813106-member-p real-type epsilon)
      (q6813106-positive-p real-type epsilon))
     (q6813106-continuous-at-epsilon-p
      real-type domain codomain function x epsilon))))

(defun-sk q6813106-continuous-function-p
    (real-type domain codomain function)
  (forall (x epsilon)
    (implies
     (and
      (q6813106-member-p domain x)
      (q6813106-member-p real-type epsilon)
      (q6813106-positive-p real-type epsilon))
     (q6813106-continuous-at-epsilon-p
      real-type domain codomain function x epsilon))))

(defun-sk q6813106-function-constructor-laws-p
    (real-type)
  (forall (type f g set value x)
    (and
     (equal
      (q6813106-function-at
       (q6813106-function-add type f g) x)
      (q6813106-add
       type
       (q6813106-function-at f x)
       (q6813106-function-at g x)))
     (equal
      (q6813106-function-at
       (q6813106-function-difference type f g) x)
      (q6813106-add
       type
       (q6813106-function-at f x)
       (q6813106-negate
        type (q6813106-function-at g x))))
     (equal
      (q6813106-function-at
       (q6813106-function-norm real-type type f) x)
      (q6813106-norm type (q6813106-function-at f x)))
     (equal
      (q6813106-function-at
       (q6813106-indicator-function real-type set) x)
      (if (q6813106-set-member-p set x)
          (q6813106-one real-type)
        (q6813106-zero real-type))))))

(defun-sk q6813106-fiber-set-law-p (domain)
  (forall (function value x)
    (iff
     (q6813106-set-member-p
      (q6813106-fiber-set function value)
      x)
     (and
      (q6813106-member-p domain x)
      (equal (q6813106-function-at function x) value)))))

(defun-sk q6813106-measurable-function-p
    (real-type domain measurable codomain function)
  (forall (center radius)
    (implies
     (and
      (q6813106-member-p codomain center)
      (q6813106-member-p real-type radius)
      (q6813106-positive-p real-type radius))
     (q6813106-family-member-p
      measurable
      (q6813106-preimage-set
       function
       (q6813106-open-ball-set
        codomain center radius))))))

(defun-sk q6813106-nonnegative-values-p
    (real-type domain function)
  (forall (x)
    (implies
     (q6813106-member-p domain x)
     (q6813106-leq
      real-type
      (q6813106-zero real-type)
      (q6813106-function-at function x)))))

(defun q6813106-nonnegative-measurable-p
    (real-type domain measurable function)
  (and
   (q6813106-function-into-p
    domain real-type function)
   (q6813106-measurable-function-p
    real-type domain measurable real-type function)
   (q6813106-nonnegative-values-p
    real-type domain function)))

(defun-sk q6813106-pointwise-leq-p
    (real-type domain left right)
  (forall (x)
    (implies
     (q6813106-member-p domain x)
     (q6813106-leq
      real-type
      (q6813106-function-at left x)
      (q6813106-function-at right x)))))

(defun-sk q6813106-functions-equal-on-p
    (domain left right)
  (forall (x)
    (implies
     (q6813106-member-p domain x)
     (equal
      (q6813106-function-at left x)
      (q6813106-function-at right x)))))

(defun-sk q6813106-lintegral-laws-p
    (real-type domain measurable measure lintegral)
  (forall (f g set)
    (and
     (implies
      (q6813106-functions-equal-on-p domain f g)
      (equal
       (q6813106-lintegral-value lintegral f)
       (q6813106-lintegral-value lintegral g)))
     (implies
      (q6813106-nonnegative-measurable-p
       real-type domain measurable f)
      (q6813106-ennreal-p
       real-type
       (q6813106-lintegral-value lintegral f)))
     (implies
      (and
       (q6813106-nonnegative-measurable-p
        real-type domain measurable f)
       (q6813106-nonnegative-measurable-p
        real-type domain measurable g)
       (q6813106-pointwise-leq-p real-type domain f g))
      (q6813106-ennreal-leq-p
       real-type
       (q6813106-lintegral-value lintegral f)
       (q6813106-lintegral-value lintegral g)))
     (implies
      (q6813106-family-member-p measurable set)
      (equal
       (q6813106-lintegral-value
        lintegral
        (q6813106-indicator-function real-type set))
       (q6813106-measure-value measure set)))
     (implies
      (and
       (q6813106-nonnegative-measurable-p
        real-type domain measurable f)
       (q6813106-nonnegative-measurable-p
        real-type domain measurable g))
      (equal
       (q6813106-lintegral-value
        lintegral
        (q6813106-function-add real-type f g))
       (q6813106-ennreal-add
        real-type
        (q6813106-lintegral-value lintegral f)
        (q6813106-lintegral-value lintegral g)))))))

(defun q6813106-simple-values-correct-p
    (domain measurable function values)
  (if (consp values)
      (and
       (q6813106-family-member-p
        measurable
        (q6813106-fiber-set function (car values)))
       (q6813106-simple-values-correct-p
        domain measurable function (cdr values)))
    (equal values nil)))

(defun q6813106-simple-listed-values-in-space-p
    (space values)
  (if (consp values)
      (and
       (q6813106-member-p space (car values))
       (q6813106-simple-listed-values-in-space-p
        space (cdr values)))
    (equal values nil)))

(defun-sk q6813106-simple-range-values-p
    (domain function values)
  (forall (x)
    (implies
     (q6813106-member-p domain x)
     (member-equal
      (q6813106-function-at function x)
      values))))

(defun-sk q6813106-value-attained-p
    (domain function value)
  (exists (x)
    (and
     (q6813106-member-p domain x)
     (equal
      (q6813106-function-at function x)
      value))))

(defun q6813106-simple-function-p
    (domain measurable space function)
  (and
   (q6813106-function-into-p domain space function)
   (true-listp (q6813106-simple-values function))
   (no-duplicatesp-equal (q6813106-simple-values function))
   (q6813106-simple-listed-values-in-space-p
    space (q6813106-simple-values function))
   (q6813106-simple-values-correct-p
    domain measurable function
    (q6813106-simple-values function))
   (q6813106-simple-range-values-p
    domain function
    (q6813106-simple-values function))))

(defun q6813106-simple-integrable-values-p
    (real-type domain measure zero function values)
  (if (consp values)
      (and
       (implies
        (not
         (q6813106-value-attained-p
          domain function (car values)))
        (equal
         (q6813106-measure-value
          measure
          (q6813106-fiber-set function (car values)))
         (q6813106-ennreal-finite
          (q6813106-zero real-type))))
       (or
        (equal (car values) zero)
        (not
         (equal
          (q6813106-measure-value
           measure
           (q6813106-fiber-set function (car values)))
          :q6813106-top)))
       (q6813106-simple-integrable-values-p
        real-type domain measure zero function (cdr values)))
    (equal values nil)))

(defun q6813106-simple-integral
    (real-type domain space measure function values)
  (if (consp values)
      (q6813106-add
       space
       (if (or
            (equal (car values) (q6813106-zero space))
            (not
             (q6813106-value-attained-p
              domain function (car values))))
           (q6813106-zero space)
         (q6813106-smul
          real-type space
          (cdr
           (q6813106-measure-value
            measure
            (q6813106-fiber-set function (car values))))
          (car values)))
       (q6813106-simple-integral
        real-type domain space measure function (cdr values)))
    (q6813106-zero space)))

(defun q6813106-ennreal-scale
    (real-type scalar value)
  (if (equal scalar (q6813106-zero real-type))
      (q6813106-ennreal-finite
       (q6813106-zero real-type))
    (if (equal value :q6813106-top)
        :q6813106-top
      (q6813106-ennreal-finite
       (q6813106-multiply
        real-type scalar (cdr value))))))

(defun q6813106-simple-nonnegative-integral
    (real-type domain measure function values)
  (if (consp values)
      (q6813106-ennreal-add
       real-type
       (if
           (q6813106-value-attained-p
            domain function (car values))
           (q6813106-ennreal-scale
            real-type
            (car values)
            (q6813106-measure-value
             measure
             (q6813106-fiber-set function (car values))))
         (q6813106-ennreal-finite
          (q6813106-zero real-type)))
       (q6813106-simple-nonnegative-integral
        real-type domain measure function (cdr values)))
    (q6813106-ennreal-finite
     (q6813106-zero real-type))))

(defun-sk q6813106-lintegral-upper-bound-p
    (real-type domain measurable measure function bound)
  (forall (simple)
    (implies
     (and
      (q6813106-simple-function-p
       domain measurable real-type simple)
      (q6813106-nonnegative-values-p
       real-type domain simple)
      (q6813106-pointwise-leq-p
       real-type domain simple function))
     (q6813106-ennreal-leq-p
      real-type
      (q6813106-simple-nonnegative-integral
       real-type domain measure simple
       (q6813106-simple-values simple))
      bound))))

(defun-sk q6813106-lintegral-least-upper-bound-p
    (real-type domain measurable measure function value)
  (forall (bound)
    (implies
     (and
      (q6813106-ennreal-p real-type bound)
      (q6813106-lintegral-upper-bound-p
       real-type domain measurable measure function bound))
     (q6813106-ennreal-leq-p real-type value bound))))

(defun-sk q6813106-lintegral-supremum-laws-p
    (real-type domain measurable measure lintegral)
  (forall (function)
    (implies
     (and
      (q6813106-function-into-p
       domain real-type function)
      (q6813106-nonnegative-values-p
       real-type domain function))
     (let ((value
            (q6813106-lintegral-value
             lintegral function)))
       (and
        (q6813106-ennreal-p real-type value)
        (q6813106-lintegral-upper-bound-p
         real-type domain measurable measure function value)
        (q6813106-lintegral-least-upper-bound-p
         real-type domain measurable measure function value))))))

(defun-sk q6813106-simple-sequence-p
    (domain measurable space sequence)
  (forall (n)
    (implies
     (natp n)
     (q6813106-simple-function-p
      domain measurable space
      (q6813106-sequence-at sequence n)))))

(defun-sk q6813106-pointwise-simple-limit-p
    (real-type domain space sequence function)
  (forall (x)
    (implies
     (q6813106-member-p domain x)
     (q6813106-converges-p
      real-type
      space
      (q6813106-point-sequence sequence x)
      (q6813106-function-at function x)))))

(defun-sk q6813106-point-sequence-laws-p ()
  (forall (sequence x n)
    (equal
     (q6813106-sequence-at
      (q6813106-point-sequence sequence x) n)
     (q6813106-function-at
      (q6813106-sequence-at sequence n) x))))

(defun-sk q6813106-strongly-measurable-p
    (real-type domain measurable space function)
  (exists (sequence)
    (and
     (q6813106-simple-sequence-p
      domain measurable space sequence)
     (q6813106-pointwise-simple-limit-p
      real-type domain space sequence function))))

(defun-sk q6813106-equal-outside-p
    (domain exceptional left right)
  (forall (x)
    (implies
     (and
      (q6813106-member-p domain x)
      (not (q6813106-set-member-p exceptional x)))
     (equal
      (q6813106-function-at left x)
      (q6813106-function-at right x)))))

(defun-sk q6813106-almost-everywhere-equal-p
    (real-type domain measurable measure left right)
  (exists (exceptional)
    (and
     (q6813106-family-member-p measurable exceptional)
     (equal
      (q6813106-measure-value measure exceptional)
      (q6813106-ennreal-finite
       (q6813106-zero real-type)))
     (q6813106-equal-outside-p
      domain exceptional left right))))

(defun-sk q6813106-aestrongly-measurable-p
    (real-type domain measurable measure space function)
  (exists (representative)
    (and
     (q6813106-strongly-measurable-p
      real-type domain measurable space representative)
     (q6813106-almost-everywhere-equal-p
      real-type domain measurable measure
      function representative))))

(defun q6813106-integrable-p
    (real-type domain measurable measure lintegral space function)
  (and
   (q6813106-aestrongly-measurable-p
    real-type domain measurable measure space function)
   (not
    (equal
     (q6813106-lintegral-value
      lintegral
      (q6813106-function-norm real-type space function))
     :q6813106-top))))

(defun q6813106-l1-distance
    (real-type space lintegral left right)
  (q6813106-lintegral-value
   lintegral
   (q6813106-function-norm
    real-type space
    (q6813106-function-difference space left right))))

(defun-sk q6813106-l1-tail-p
    (real-type space lintegral sequence function epsilon start)
  (forall (n)
    (implies
     (and (natp n) (natp start) (<= start n))
     (q6813106-ennreal-leq-p
      real-type
      (q6813106-l1-distance
       real-type space lintegral
       (q6813106-sequence-at sequence n)
       function)
      (q6813106-ennreal-finite epsilon)))))

(defun-sk q6813106-l1-start-p
    (real-type space lintegral sequence function epsilon)
  (exists (start)
    (and
     (natp start)
     (q6813106-l1-tail-p
      real-type space lintegral
      sequence function epsilon start))))

(defun-sk q6813106-l1-converges-p
    (real-type space lintegral sequence function)
  (forall (epsilon)
    (implies
     (and
      (q6813106-member-p real-type epsilon)
      (q6813106-positive-p real-type epsilon))
     (q6813106-l1-start-p
      real-type space lintegral sequence function epsilon))))

(defun-sk q6813106-integrable-simple-sequence-p
    (real-type domain measurable measure space sequence)
  (forall (n)
    (implies
     (natp n)
     (let ((f (q6813106-sequence-at sequence n)))
       (and
        (q6813106-simple-function-p
         domain measurable space f)
        (q6813106-simple-integrable-values-p
         real-type domain measure
         (q6813106-zero space) f
         (q6813106-simple-values f)))))))

(defun-sk q6813106-simple-integral-sequence-laws-p ()
  (forall (real-type domain space measure sequence n)
    (equal
     (q6813106-sequence-at
      (q6813106-simple-integral-sequence
       real-type domain space measure sequence)
      n)
     (q6813106-simple-integral
      real-type domain space measure
      (q6813106-sequence-at sequence n)
      (q6813106-simple-values
       (q6813106-sequence-at sequence n))))))

(defun q6813106-bochner-approximation-p
    (real-type domain measurable measure lintegral
     space function value sequence)
  (and
   (q6813106-integrable-simple-sequence-p
    real-type domain measurable measure space sequence)
   (q6813106-l1-converges-p
    real-type space lintegral sequence function)
   (q6813106-converges-p
    real-type space
    (q6813106-simple-integral-sequence
     real-type domain space measure sequence)
    value)))

(defun-sk q6813106-bochner-approximation-exists-p
    (real-type domain measurable measure lintegral
     space function value)
  (exists (sequence)
    (q6813106-bochner-approximation-p
     real-type domain measurable measure lintegral
     space function value sequence)))

(defun-sk q6813106-bochner-integral-operation-p
    (real-type domain measurable measure lintegral space integral)
  (forall (function other)
    (and
     (implies
      (q6813106-functions-equal-on-p
       domain function other)
      (equal
       (q6813106-bochner-integral-value
        integral function)
       (q6813106-bochner-integral-value
        integral other)))
     (implies
      (q6813106-function-into-p domain space function)
      (let ((value
             (q6813106-bochner-integral-value
              integral function)))
        (and
         (q6813106-member-p space value)
         (if
             (and
              (q6813106-complete-p real-type space)
              (q6813106-integrable-p
               real-type domain measurable measure lintegral
               space function))
             (q6813106-bochner-approximation-exists-p
              real-type domain measurable measure lintegral
              space function value)
           (equal value (q6813106-zero space)))))))))

;; The normalized Fourier character.

(defun-sk q6813106-character-kernel-witness-p
    (real-type complex-type fourier-char x)
  (exists (n)
    (and
     (integerp n)
     (equal x (q6813106-integer-cast real-type n)))))

(defun-sk q6813106-character-laws-p
    (real-type complex-type fourier-char)
  (forall (x y)
    (implies
     (and
      (q6813106-member-p real-type x)
      (q6813106-member-p real-type y))
     (and
      (q6813106-member-p
       complex-type
       (q6813106-character-value fourier-char x))
      (equal
       (q6813106-character-value
        fourier-char (q6813106-add real-type x y))
       (q6813106-multiply
        complex-type
        (q6813106-character-value fourier-char x)
        (q6813106-character-value fourier-char y)))
      (equal
       (q6813106-norm
        complex-type
        (q6813106-character-value fourier-char x))
       (q6813106-one real-type))
      (iff
       (equal
        (q6813106-character-value fourier-char x)
        (q6813106-one complex-type))
       (q6813106-character-kernel-witness-p
        real-type complex-type fourier-char x))))))

(defun-sk q6813106-character-orientation-delta-p
    (real-type complex-type fourier-char delta)
  (forall (x)
    (implies
     (and
      (q6813106-member-p real-type x)
      (q6813106-positive-p real-type x)
      (q6813106-less real-type x delta))
     (q6813106-less
      real-type
      (q6813106-zero real-type)
      (q6813106-imag-part
       real-type complex-type
       (q6813106-character-value fourier-char x))))))

(defun-sk q6813106-character-orientation-p
    (real-type complex-type fourier-char)
  (exists (delta)
    (and
     (q6813106-member-p real-type delta)
     (q6813106-positive-p real-type delta)
     (q6813106-character-orientation-delta-p
      real-type complex-type fourier-char delta))))

(defun-sk q6813106-character-continuity-delta-p
    (real-type complex-type fourier-char epsilon delta)
  (forall (x)
    (implies
     (and
      (q6813106-member-p real-type x)
      (q6813106-less
       real-type
       (q6813106-abs real-type x)
       delta))
     (q6813106-less
      real-type
      (q6813106-distance
       real-type complex-type
       (q6813106-character-value fourier-char x)
       (q6813106-one complex-type))
      epsilon))))

(defun-sk q6813106-character-continuity-epsilon-p
    (real-type complex-type fourier-char epsilon)
  (exists (delta)
    (and
     (q6813106-member-p real-type delta)
     (q6813106-positive-p real-type delta)
     (q6813106-character-continuity-delta-p
      real-type complex-type fourier-char epsilon delta))))

(defun-sk q6813106-character-continuity-p
    (real-type complex-type fourier-char)
  (forall (epsilon)
    (implies
     (and
      (q6813106-member-p real-type epsilon)
      (q6813106-positive-p real-type epsilon))
     (q6813106-character-continuity-epsilon-p
      real-type complex-type fourier-char epsilon))))

(defun q6813106-fourier-character-p
    (real-type complex-type fourier-char)
  (and
   (equal
    (q6813106-character-value
     fourier-char (q6813106-zero real-type))
    (q6813106-one complex-type))
   (q6813106-character-laws-p
    real-type complex-type fourier-char)
   (q6813106-character-continuity-p
    real-type complex-type fourier-char)
   (q6813106-character-orientation-p
    real-type complex-type fourier-char)))


(defun-sk q6813106-fourier-integrand-laws-p
    (real-type complex-type domain space fourier-char)
  (forall (f frequency x)
    (equal
     (q6813106-function-at
      (q6813106-fourier-integrand
       real-type complex-type domain space
       fourier-char f frequency)
      x)
     (q6813106-smul
      complex-type space
      (q6813106-character-value
       fourier-char
       (q6813106-negate
        real-type
        (q6813106-inner
         real-type domain x frequency)))
      (q6813106-function-at f x)))))

(defun-sk q6813106-inverse-fourier-integrand-laws-p
    (real-type complex-type domain space fourier-char)
  (forall (f frequency x)
    (equal
     (q6813106-function-at
      (q6813106-inverse-fourier-integrand
       real-type complex-type domain space
       fourier-char f frequency)
      x)
     (q6813106-smul
      complex-type space
      (q6813106-character-value
       fourier-char
       (q6813106-inner
        real-type domain x frequency))
      (q6813106-function-at f x)))))

(defun-sk q6813106-fourier-transform-correct-p
    (real-type complex-type domain space
     fourier-char integral fourier function)
  (forall (frequency)
    (implies
     (q6813106-member-p domain frequency)
     (and
      (q6813106-member-p
       space
       (q6813106-function-at
        (q6813106-fourier-function fourier function)
        frequency))
      (equal
       (q6813106-function-at
        (q6813106-fourier-function fourier function)
        frequency)
       (q6813106-bochner-integral-value
        integral
        (q6813106-fourier-integrand
         real-type complex-type domain space
         fourier-char function frequency)))))))

(defun-sk q6813106-fourier-inverse-correct-p
    (real-type complex-type domain space
     fourier-char integral fourier-inverse function)
  (forall (frequency)
    (implies
     (q6813106-member-p domain frequency)
     (and
      (q6813106-member-p
       space
       (q6813106-function-at
        (q6813106-fourier-inverse-function
         fourier-inverse function)
        frequency))
      (equal
       (q6813106-function-at
        (q6813106-fourier-inverse-function
         fourier-inverse function)
        frequency)
       (q6813106-bochner-integral-value
        integral
        (q6813106-inverse-fourier-integrand
         real-type complex-type domain space
         fourier-char function frequency)))))))

;; The real exponential is characterized by its everywhere-convergent power
;; series, rather than left as an uninterpreted operation.

(defun q6813106-natural-factorial (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q6813106-one real-type)
    (q6813106-multiply
     real-type
     (q6813106-natural-cast real-type n)
     (q6813106-natural-factorial real-type (- n 1)))))

(defun q6813106-real-power (real-type x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q6813106-one real-type)
    (q6813106-multiply
     real-type x
     (q6813106-real-power real-type x (- n 1)))))

(defun q6813106-exponential-partial-sum (real-type x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q6813106-one real-type)
    (q6813106-add
     real-type
     (q6813106-exponential-partial-sum real-type x (- n 1))
     (q6813106-multiply
      real-type
      (q6813106-real-power real-type x n)
      (q6813106-inverse
       real-type
       (q6813106-natural-factorial real-type n))))))

(defun-sk q6813106-exponential-sequence-laws-p (real-type)
  (forall (x n)
    (implies
     (and
      (q6813106-member-p real-type x)
      (natp n))
     (equal
      (q6813106-sequence-at
       (q6813106-exponential-sequence real-type x) n)
      (q6813106-exponential-partial-sum real-type x n)))))

(defun-sk q6813106-exponential-limit-laws-p (real-type)
  (forall (x)
    (implies
     (q6813106-member-p real-type x)
     (and
      (q6813106-member-p
       real-type
       (q6813106-real-exponential real-type x))
      (q6813106-converges-p
       real-type real-type
       (q6813106-exponential-sequence real-type x)
       (q6813106-real-exponential real-type x))))))

(defun-sk q6813106-exponential-positive-p (real-type)
  (forall (x)
    (implies
     (q6813106-member-p real-type x)
     (q6813106-positive-p
      real-type
      (q6813106-real-exponential real-type x)))))

(defun-sk q6813106-logarithm-inverse-laws-p (real-type)
  (forall (x y)
    (and
     (implies
      (and
       (q6813106-member-p real-type x)
       (q6813106-positive-p real-type x))
      (and
       (q6813106-member-p
        real-type
        (q6813106-real-logarithm real-type x))
       (equal
        (q6813106-real-exponential
         real-type
         (q6813106-real-logarithm real-type x))
        x)))
     (implies
      (q6813106-member-p real-type y)
      (equal
       (q6813106-real-logarithm
        real-type
        (q6813106-real-exponential real-type y))
       y)))))

(defun q6813106-standard-exponential-p (real-type)
  (and
   (q6813106-exponential-sequence-laws-p real-type)
   (q6813106-exponential-limit-laws-p real-type)
   (q6813106-exponential-positive-p real-type)
   (q6813106-logarithm-inverse-laws-p real-type)))

;; Under t = exp(-u), Mellin convergence on Re(s) = sigma is exactly
;; integrability of g(u) = exp(-sigma*u) * f(exp(-u)).  On that same line,
;; the Mellin transform is the Fourier transform of g after the nonzero
;; 2*pi reparameterization used by the source theorem.

(defun-sk q6813106-mellin-coordinate-laws-p
    (real-type complex-type space)
  (forall (sigma function u)
    (implies
     (and
      (q6813106-member-p real-type sigma)
      (q6813106-member-p real-type u))
     (equal
      (q6813106-function-at
       (q6813106-mellin-coordinate-function
        real-type complex-type space sigma function)
       u)
      (q6813106-smul
       complex-type space
       (q6813106-of-real
        real-type complex-type
        (q6813106-real-exponential
         real-type
         (q6813106-negate
          real-type
          (q6813106-multiply real-type sigma u))))
       (q6813106-function-at
        function
        (q6813106-real-exponential
         real-type
         (q6813106-negate real-type u))))))))

(defun q6813106-mellin-coordinate
    (real-type complex-type space sigma function)
  (q6813106-mellin-coordinate-function
   real-type complex-type space sigma function))

(defun q6813106-mellin-inversion-context-p
    (real-type complex-type space
     basis coordinates
     measurable measure lintegral
     space-integral fourier-char
     fourier fourier-inverse sigma f)
  (let ((g
         (q6813106-mellin-coordinate
          real-type complex-type space sigma f)))
    (and
     (q6813106-complex-field-p real-type complex-type)
     (q6813106-finite-real-inner-product-space-p
      real-type real-type basis coordinates 1)
     (q6813106-complex-banach-space-p
      real-type complex-type space)
     (q6813106-standard-exponential-p real-type)
     (q6813106-set-constructor-laws-p real-type real-type)
     (q6813106-set-constructor-laws-p real-type space)
     (q6813106-preimage-set-law-p real-type)
     (q6813106-fiber-set-law-p real-type)
     (q6813106-function-constructor-laws-p real-type)
     (q6813106-point-sequence-laws-p)
     (q6813106-simple-integral-sequence-laws-p)
     (q6813106-volume-space-p
      real-type real-type basis coordinates 1
      measurable measure)
     (q6813106-lintegral-laws-p
      real-type real-type measurable measure lintegral)
     (q6813106-lintegral-supremum-laws-p
      real-type real-type measurable measure lintegral)
     (q6813106-bochner-integral-operation-p
      real-type real-type measurable measure lintegral
      space space-integral)
     (q6813106-fourier-character-p
      real-type complex-type fourier-char)
     (q6813106-fourier-integrand-laws-p
      real-type complex-type real-type space fourier-char)
     (q6813106-inverse-fourier-integrand-laws-p
      real-type complex-type real-type space fourier-char)
     (q6813106-member-p real-type sigma)
     (q6813106-function-into-p real-type space f)
     (q6813106-mellin-coordinate-laws-p
      real-type complex-type space)
     (q6813106-function-into-p real-type space g)
     (q6813106-fourier-transform-correct-p
      real-type complex-type real-type space
      fourier-char space-integral fourier g)
     (q6813106-fourier-inverse-correct-p
      real-type complex-type real-type space
      fourier-char space-integral fourier-inverse
      (q6813106-fourier-function fourier g)))))

(defun q6813106-mellin-convergent-p
    (real-type complex-type space
     measurable measure lintegral sigma f)
  (q6813106-integrable-p
   real-type real-type measurable measure lintegral space
   (q6813106-mellin-coordinate
    real-type complex-type space sigma f)))

(defun q6813106-vertical-mellin-integrable-p
    (real-type complex-type space
     measurable measure lintegral fourier sigma f)
  (q6813106-integrable-p
   real-type real-type measurable measure lintegral space
   (q6813106-fourier-function
    fourier
    (q6813106-mellin-coordinate
     real-type complex-type space sigma f))))

;; This is the source's inverse-Mellin expression after the exact Fourier
;; coordinate change: x^(-sigma) times FourierInv(Fourier(g))(-log x).

(defun q6813106-inverse-mellin-of-mellin-at
    (real-type complex-type space
     fourier fourier-inverse sigma f x)
  (let* ((u
          (q6813106-negate
           real-type
           (q6813106-real-logarithm real-type x)))
         (scale
          (q6813106-of-real
           real-type complex-type
           (q6813106-real-exponential
            real-type
            (q6813106-multiply real-type sigma u))))
         (g
          (q6813106-mellin-coordinate
           real-type complex-type space sigma f)))
    (q6813106-smul
     complex-type space scale
     (q6813106-function-at
      (q6813106-fourier-inverse-function
       fourier-inverse
       (q6813106-fourier-function fourier g))
      u))))

(defun-sk thousand-theorems-q6813106-mellin-inversion-theorem-statement
    (real-type complex-type space
     basis coordinates
     measurable measure lintegral
     space-integral fourier-char
     fourier fourier-inverse sigma f)
  (forall (x)
    (implies
     (and
      (q6813106-mellin-inversion-context-p
       real-type complex-type space
       basis coordinates
       measurable measure lintegral
       space-integral fourier-char
       fourier fourier-inverse sigma f)
      (q6813106-member-p real-type x)
      (q6813106-positive-p real-type x)
      (q6813106-mellin-convergent-p
       real-type complex-type space
       measurable measure lintegral sigma f)
      (q6813106-vertical-mellin-integrable-p
       real-type complex-type space
       measurable measure lintegral fourier sigma f)
      (q6813106-continuous-at-p
       real-type real-type space f x))
     (equal
      (q6813106-inverse-mellin-of-mellin-at
       real-type complex-type space
       fourier fourier-inverse sigma f x)
      (q6813106-function-at f x)))))

(value-triple :itpeval-statement-checked)
:q
