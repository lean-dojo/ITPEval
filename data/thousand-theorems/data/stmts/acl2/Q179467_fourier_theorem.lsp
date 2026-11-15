;; Statement-only formalization of thousand-theorems corpus artifact Q179467,
;; "Fourier theorem": for an integrable Banach-valued function on a
;; finite-dimensional real inner-product space whose Fourier transform is
;; integrable, Fourier inversion recovers the function at every continuity
;; point, and everywhere when the function is continuous. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Mathematical objects are unrestricted ACL2 objects.  The conservative
;; interfaces below only provide application and constructor symbols; every
;; field, space, topology, measure, integral, and Fourier law used by the
;; statement is imposed explicitly by predicates below.

(defstub q179467-member-p (type object) t)
(defstub q179467-zero (type) t)
(defstub q179467-one (type) t)
(defstub q179467-add (type left right) t)
(defstub q179467-multiply (type left right) t)
(defstub q179467-negate (type object) t)
(defstub q179467-inverse (type object) t)
(defstub q179467-less (type left right) t)
(defstub q179467-norm (type object) t)
(defstub q179467-smul (scalar-type space scalar vector) t)
(defstub q179467-star (scalar-type scalar) t)
(defstub q179467-real-part (real-type scalar-type scalar) t)
(defstub q179467-imag-part (real-type scalar-type scalar) t)
(defstub q179467-of-real (real-type scalar-type real) t)
(defstub q179467-imaginary-unit (scalar-type) t)
(defstub q179467-inner (scalar-type space left right) t)
(defstub q179467-function-at (function argument) t)
(defstub q179467-sequence-at (sequence index) t)
(defstub q179467-basis-at (basis index) t)
(defstub q179467-coordinate (coordinates vector index) t)
(defstub q179467-fourier-function (fourier function) t)
(defstub q179467-fourier-inverse-function (fourier-inverse function) t)
(defstub q179467-character-value (fourier-char real) t)
(defstub q179467-set-member-p (set object) t)
(defstub q179467-family-member-p (family set) t)
(defstub q179467-open-ball-set (space center radius) t)
(defstub q179467-preimage-set (function set) t)
(defstub q179467-complement-set (carrier set) t)
(defstub q179467-countable-union-set (carrier sequence) t)
(defstub q179467-translate-set (space set shift) t)
(defstub q179467-unit-cell-set (space basis coordinates dimension) t)
(defstub q179467-fiber-set (function value) t)
(defstub q179467-simple-values (function) t)
(defstub q179467-indicator-function (real-type set) t)
(defstub q179467-function-add (type left right) t)
(defstub q179467-function-difference (type left right) t)
(defstub q179467-function-norm (real-type type function) t)
(defstub q179467-fourier-integrand
  (real-type scalar-type domain space fourier-char function frequency) t)
(defstub q179467-inverse-fourier-integrand
  (real-type scalar-type domain space fourier-char function frequency) t)
(defstub q179467-measure-value (measure set) t)
(defstub q179467-lintegral-value (lintegral function) t)
(defstub q179467-bochner-integral-value (integral function) t)
(defstub q179467-full-set (carrier) t)
(defstub q179467-point-sequence (function-sequence point) t)
(defstub q179467-simple-integral-sequence
  (real-type domain space measure function-sequence) t)

(defun q179467-positive-p (real-type x)
  (q179467-less real-type (q179467-zero real-type) x))

(defun q179467-leq (real-type x y)
  (not (q179467-less real-type y x)))

(defun q179467-abs (real-type x)
  (if (q179467-less real-type x (q179467-zero real-type))
      (q179467-negate real-type x)
    x))

(defun q179467-natural-cast (type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q179467-zero type)
    (q179467-add
     type
     (q179467-one type)
     (q179467-natural-cast type (- n 1)))))

(defun q179467-integer-cast (type n)
  (if (and (integerp n) (< n 0))
      (q179467-negate
       type
       (q179467-natural-cast type (- n)))
    (q179467-natural-cast type (nfix n))))


(defun q179467-vector-sum
    (real-type space basis coordinates vector n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q179467-zero space)
    (let ((i (- n 1)))
      (q179467-add
       space
       (q179467-vector-sum
        real-type space basis coordinates vector i)
       (q179467-smul
        real-type space
        (q179467-coordinate coordinates vector i)
        (q179467-basis-at basis i))))))


;; Complete ordered real field and its canonical complexification.

(defun-sk q179467-field-laws-p (type)
  (forall (x y z)
    (implies
     (and
      (q179467-member-p type x)
      (q179467-member-p type y)
      (q179467-member-p type z))
     (and
      (q179467-member-p type (q179467-add type x y))
      (q179467-member-p type (q179467-multiply type x y))
      (q179467-member-p type (q179467-negate type x))
      (implies
       (not (equal x (q179467-zero type)))
       (q179467-member-p type (q179467-inverse type x)))
      (equal
       (q179467-add type (q179467-add type x y) z)
       (q179467-add type x (q179467-add type y z)))
      (equal (q179467-add type x y) (q179467-add type y x))
      (equal (q179467-add type x (q179467-zero type)) x)
      (equal
       (q179467-add type x (q179467-negate type x))
       (q179467-zero type))
      (equal
       (q179467-multiply type (q179467-multiply type x y) z)
       (q179467-multiply type x (q179467-multiply type y z)))
      (equal
       (q179467-multiply type x y)
       (q179467-multiply type y x))
      (equal (q179467-multiply type x (q179467-one type)) x)
      (implies
       (not (equal x (q179467-zero type)))
       (equal
        (q179467-multiply type x (q179467-inverse type x))
        (q179467-one type)))
      (equal
       (q179467-multiply type x (q179467-add type y z))
       (q179467-add
        type
        (q179467-multiply type x y)
        (q179467-multiply type x z)))))))

(defun-sk q179467-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q179467-member-p real-type x)
      (q179467-member-p real-type y)
      (q179467-member-p real-type z))
     (and
      (not (q179467-less real-type x x))
      (or
       (q179467-less real-type x y)
       (equal x y)
       (q179467-less real-type y x))
      (implies
       (and
        (q179467-less real-type x y)
        (q179467-less real-type y z))
       (q179467-less real-type x z))
      (implies
       (q179467-less real-type x y)
       (q179467-less
        real-type
        (q179467-add real-type x z)
        (q179467-add real-type y z)))
      (implies
       (and
        (q179467-positive-p real-type x)
        (q179467-positive-p real-type y))
       (q179467-positive-p
        real-type
        (q179467-multiply real-type x y)))))))

(defun q179467-distance
    (real-type type x y)
  (declare (ignore real-type))
  (q179467-norm
   type
   (q179467-add type x (q179467-negate type y))))

(defun-sk q179467-norm-values-p (real-type type)
  (forall (x)
    (implies
     (q179467-member-p type x)
     (and
      (q179467-member-p real-type (q179467-norm type x))
      (q179467-leq
       real-type
       (q179467-zero real-type)
       (q179467-norm type x))
      (iff
       (equal
        (q179467-norm type x)
        (q179467-zero real-type))
       (equal x (q179467-zero type)))))))

(defun-sk q179467-norm-triangle-p (real-type type)
  (forall (x y)
    (implies
     (and
      (q179467-member-p type x)
      (q179467-member-p type y))
     (q179467-leq
      real-type
      (q179467-norm type (q179467-add type x y))
      (q179467-add
       real-type
       (q179467-norm type x)
       (q179467-norm type y))))))

(defun q179467-norm-laws-p (real-type type)
  (and
   (q179467-norm-values-p real-type type)
   (q179467-norm-triangle-p real-type type)))

(defun-sk q179467-convergence-tail-p
    (real-type type sequence limit epsilon start)
  (forall (n)
    (implies
     (and (natp n) (natp start) (<= start n))
     (q179467-less
      real-type
      (q179467-distance
       real-type type
       (q179467-sequence-at sequence n)
       limit)
      epsilon))))

(defun-sk q179467-convergence-start-p
    (real-type type sequence limit epsilon)
  (exists (start)
    (and
     (natp start)
     (q179467-convergence-tail-p
      real-type type sequence limit epsilon start))))

(defun-sk q179467-converges-p
    (real-type type sequence limit)
  (forall (epsilon)
    (implies
     (and
      (q179467-member-p real-type epsilon)
      (q179467-positive-p real-type epsilon))
     (q179467-convergence-start-p
      real-type type sequence limit epsilon))))

(defun-sk q179467-cauchy-tail-p
    (real-type type sequence epsilon start)
  (forall (m n)
    (implies
     (and
      (natp m) (natp n) (natp start)
      (<= start m) (<= start n))
     (q179467-less
      real-type
      (q179467-distance
       real-type type
       (q179467-sequence-at sequence m)
       (q179467-sequence-at sequence n))
      epsilon))))

(defun-sk q179467-cauchy-start-p
    (real-type type sequence epsilon)
  (exists (start)
    (and
     (natp start)
     (q179467-cauchy-tail-p
      real-type type sequence epsilon start))))

(defun-sk q179467-cauchy-p (real-type type sequence)
  (forall (epsilon)
    (implies
     (and
      (q179467-member-p real-type epsilon)
      (q179467-positive-p real-type epsilon))
     (q179467-cauchy-start-p
      real-type type sequence epsilon))))

(defun-sk q179467-sequence-in-type-p (type sequence)
  (forall (n)
    (implies
     (natp n)
     (q179467-member-p
      type
      (q179467-sequence-at sequence n)))))

(defun-sk q179467-limit-exists-p
    (real-type type sequence)
  (exists (limit)
    (and
     (q179467-member-p type limit)
     (q179467-converges-p
      real-type type sequence limit))))

(defun-sk q179467-complete-p (real-type type)
  (forall (sequence)
    (implies
     (and
      (q179467-sequence-in-type-p type sequence)
      (q179467-cauchy-p real-type type sequence))
     (q179467-limit-exists-p
      real-type type sequence))))

(defun-sk q179467-archimedean-witness-p (real-type x)
  (exists (n)
    (and
     (natp n)
     (q179467-less
      real-type x
      (q179467-natural-cast real-type n)))))

(defun-sk q179467-archimedean-p (real-type)
  (forall (x)
    (implies
     (q179467-member-p real-type x)
     (q179467-archimedean-witness-p real-type x))))

(defun-sk q179467-real-norm-laws-p (real-type)
  (forall (x)
    (implies
     (q179467-member-p real-type x)
     (and
      (equal
       (q179467-norm real-type x)
       (q179467-abs real-type x))
      (equal (q179467-star real-type x) x)
      (equal
       (q179467-real-part real-type real-type x)
       x)
      (equal
       (q179467-imag-part real-type real-type x)
       (q179467-zero real-type))
      (equal
       (q179467-of-real real-type real-type x)
       x)))))

(defun q179467-real-field-p (real-type)
  (and
   (q179467-member-p real-type (q179467-zero real-type))
   (q179467-member-p real-type (q179467-one real-type))
   (not
    (equal
     (q179467-zero real-type)
     (q179467-one real-type)))
   (q179467-field-laws-p real-type)
   (q179467-order-laws-p real-type)
   (q179467-positive-p real-type (q179467-one real-type))
   (q179467-real-norm-laws-p real-type)
   (q179467-complete-p real-type real-type)
   (q179467-archimedean-p real-type)))

(defun-sk q179467-complex-coordinate-laws-p
    (real-type complex-type)
  (forall (z)
    (implies
     (q179467-member-p complex-type z)
     (let* ((re (q179467-real-part real-type complex-type z))
            (im (q179467-imag-part real-type complex-type z))
            (re-z (q179467-of-real real-type complex-type re))
            (im-z
             (q179467-multiply
              complex-type
              (q179467-of-real real-type complex-type im)
              (q179467-imaginary-unit complex-type))))
       (and
        (q179467-member-p real-type re)
        (q179467-member-p real-type im)
        (equal z (q179467-add complex-type re-z im-z))
        (equal
         (q179467-star complex-type z)
         (q179467-add
          complex-type re-z
          (q179467-negate complex-type im-z)))
        (equal
         (q179467-multiply
          real-type
          (q179467-norm complex-type z)
          (q179467-norm complex-type z))
         (q179467-add
          real-type
          (q179467-multiply real-type re re)
          (q179467-multiply real-type im im))))))))

(defun-sk q179467-of-real-laws-p
    (real-type complex-type)
  (forall (x y)
    (implies
     (and
      (q179467-member-p real-type x)
      (q179467-member-p real-type y))
     (and
      (q179467-member-p
       complex-type
       (q179467-of-real real-type complex-type x))
      (equal
       (q179467-real-part
        real-type complex-type
        (q179467-of-real real-type complex-type x))
       x)
      (equal
       (q179467-imag-part
        real-type complex-type
        (q179467-of-real real-type complex-type x))
       (q179467-zero real-type))
      (equal
       (q179467-of-real
        real-type complex-type
        (q179467-add real-type x y))
       (q179467-add
        complex-type
        (q179467-of-real real-type complex-type x)
        (q179467-of-real real-type complex-type y)))
      (equal
       (q179467-of-real
        real-type complex-type
        (q179467-multiply real-type x y))
       (q179467-multiply
        complex-type
        (q179467-of-real real-type complex-type x)
        (q179467-of-real real-type complex-type y)))))))

(defun q179467-complex-field-p
    (real-type complex-type)
  (and
   (q179467-real-field-p real-type)
   (q179467-member-p complex-type (q179467-zero complex-type))
   (q179467-member-p complex-type (q179467-one complex-type))
   (not
    (equal
     (q179467-zero complex-type)
     (q179467-one complex-type)))
   (q179467-field-laws-p complex-type)
   (q179467-of-real-laws-p real-type complex-type)
   (equal
    (q179467-of-real
     real-type complex-type (q179467-zero real-type))
    (q179467-zero complex-type))
   (equal
    (q179467-of-real
     real-type complex-type (q179467-one real-type))
    (q179467-one complex-type))
   (equal
    (q179467-multiply
     complex-type
     (q179467-imaginary-unit complex-type)
     (q179467-imaginary-unit complex-type))
    (q179467-negate complex-type (q179467-one complex-type)))
   (equal
    (q179467-real-part
     real-type complex-type
     (q179467-imaginary-unit complex-type))
    (q179467-zero real-type))
   (equal
    (q179467-imag-part
     real-type complex-type
     (q179467-imaginary-unit complex-type))
    (q179467-one real-type))
   (q179467-complex-coordinate-laws-p real-type complex-type)
   (q179467-norm-laws-p real-type complex-type)
   (q179467-complete-p real-type complex-type)))

;; Real inner-product domains and complex Banach codomains.

(defun-sk q179467-vector-space-laws-p
    (scalar-type space)
  (forall (a b x y z)
    (implies
     (and
      (q179467-member-p scalar-type a)
      (q179467-member-p scalar-type b)
      (q179467-member-p space x)
      (q179467-member-p space y)
      (q179467-member-p space z))
     (and
      (q179467-member-p space (q179467-add space x y))
      (q179467-member-p space (q179467-negate space x))
      (q179467-member-p
       space (q179467-smul scalar-type space a x))
      (equal
       (q179467-add space (q179467-add space x y) z)
       (q179467-add space x (q179467-add space y z)))
      (equal (q179467-add space x y) (q179467-add space y x))
      (equal (q179467-add space x (q179467-zero space)) x)
      (equal
       (q179467-add space x (q179467-negate space x))
       (q179467-zero space))
      (equal
       (q179467-smul
        scalar-type space (q179467-one scalar-type) x)
       x)
      (equal
       (q179467-smul
        scalar-type space
        (q179467-multiply scalar-type a b) x)
       (q179467-smul
        scalar-type space a
        (q179467-smul scalar-type space b x)))
      (equal
       (q179467-smul
        scalar-type space
        (q179467-add scalar-type a b) x)
       (q179467-add
        space
        (q179467-smul scalar-type space a x)
        (q179467-smul scalar-type space b x)))
      (equal
       (q179467-smul
        scalar-type space a (q179467-add space x y))
       (q179467-add
        space
        (q179467-smul scalar-type space a x)
        (q179467-smul scalar-type space a y)))))))

(defun-sk q179467-normed-space-laws-p
    (real-type scalar-type space)
  (forall (a x)
    (implies
     (and
      (q179467-member-p scalar-type a)
      (q179467-member-p space x))
     (equal
      (q179467-norm
       space
       (q179467-smul scalar-type space a x))
      (q179467-multiply
       real-type
       (q179467-norm scalar-type a)
       (q179467-norm space x))))))

(defun-sk q179467-inner-product-laws-p
    (real-type scalar-type space)
  (forall (a x y z)
    (implies
     (and
      (q179467-member-p scalar-type a)
      (q179467-member-p space x)
      (q179467-member-p space y)
      (q179467-member-p space z))
     (let ((xy (q179467-inner scalar-type space x y))
           (xx (q179467-inner scalar-type space x x)))
       (and
        (q179467-member-p scalar-type xy)
        (equal
         (q179467-inner
          scalar-type space x (q179467-add space y z))
         (q179467-add
          scalar-type xy
          (q179467-inner scalar-type space x z)))
        (equal
         (q179467-inner
          scalar-type space x
          (q179467-smul scalar-type space a y))
         (q179467-multiply scalar-type a xy))
        (equal
         (q179467-inner scalar-type space y x)
         (q179467-star scalar-type xy))
        (equal
         (q179467-multiply
          real-type
          (q179467-norm space x)
          (q179467-norm space x))
         (q179467-real-part real-type scalar-type xx))
        (iff
         (equal xx (q179467-zero scalar-type))
         (equal x (q179467-zero space))))))))

(defun-sk q179467-real-smul-compatibility-p
    (real-type complex-type space)
  (forall (r x)
    (implies
     (and
      (q179467-member-p real-type r)
      (q179467-member-p space x))
     (equal
      (q179467-smul real-type space r x)
      (q179467-smul
       complex-type space
       (q179467-of-real real-type complex-type r)
       x)))))

(defun-sk q179467-orthonormal-basis-laws-p
    (real-type space basis coordinates dimension)
  (forall (i j x)
    (and
     (implies
      (and (natp i) (< i dimension))
      (q179467-member-p space (q179467-basis-at basis i)))
     (implies
      (and
       (natp i) (natp j)
       (< i dimension) (< j dimension))
      (equal
       (q179467-inner
        real-type space
        (q179467-basis-at basis i)
        (q179467-basis-at basis j))
       (if (equal i j)
           (q179467-one real-type)
         (q179467-zero real-type))))
     (implies
      (q179467-member-p space x)
      (and
       (implies
        (and (natp i) (< i dimension))
        (q179467-member-p
         real-type
         (q179467-coordinate coordinates x i)))
       (equal
        x
        (q179467-vector-sum
         real-type space basis coordinates x dimension)))))))

(defun q179467-finite-real-inner-product-space-p
    (real-type space basis coordinates dimension)
  (and
   (natp dimension)
   (q179467-member-p space (q179467-zero space))
   (q179467-vector-space-laws-p real-type space)
   (q179467-norm-laws-p real-type space)
   (q179467-normed-space-laws-p real-type real-type space)
   (q179467-inner-product-laws-p real-type real-type space)
   (q179467-orthonormal-basis-laws-p
    real-type space basis coordinates dimension)))

(defun q179467-complex-banach-space-p
    (real-type complex-type space)
  (and
   (q179467-member-p space (q179467-zero space))
   (q179467-vector-space-laws-p complex-type space)
   (q179467-vector-space-laws-p real-type space)
   (q179467-norm-laws-p real-type space)
   (q179467-normed-space-laws-p
    real-type complex-type space)
   (q179467-normed-space-laws-p
    real-type real-type space)
   (q179467-real-smul-compatibility-p
    real-type complex-type space)
   (q179467-complete-p real-type space)))

;; Borel sigma algebra and normalized translation-invariant volume.

(defun-sk q179467-countable-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q179467-set-member-p
      (q179467-sequence-at sequence n) x))))

(defun-sk q179467-valid-set-p (space set)
  (forall (x)
    (implies
     (q179467-set-member-p set x)
     (q179467-member-p space x))))

(defun-sk q179467-sets-equal-on-p (space left right)
  (forall (x)
    (implies
     (q179467-member-p space x)
     (iff
      (q179467-set-member-p left x)
      (q179467-set-member-p right x)))))

(defun-sk q179467-empty-on-p (space set)
  (forall (x)
    (implies
     (q179467-member-p space x)
     (not (q179467-set-member-p set x)))))

(defun-sk q179467-full-set-law-p (space)
  (forall (x)
    (iff
     (q179467-set-member-p
      (q179467-full-set space) x)
     (q179467-member-p space x))))

(defun-sk q179467-complement-set-law-p (space)
  (forall (set x)
    (iff
     (q179467-set-member-p
      (q179467-complement-set space set) x)
     (and
      (q179467-member-p space x)
      (not (q179467-set-member-p set x))))))

(defun-sk q179467-countable-union-set-law-p (space)
  (forall (sequence x)
    (iff
     (q179467-set-member-p
      (q179467-countable-union-set space sequence) x)
     (and
      (q179467-member-p space x)
      (q179467-countable-union-member-p sequence x)))))

(defun-sk q179467-open-ball-set-law-p (real-type space)
  (forall (center radius x)
    (iff
     (q179467-set-member-p
      (q179467-open-ball-set space center radius) x)
     (and
      (q179467-member-p space x)
      (q179467-member-p space center)
      (q179467-member-p real-type radius)
      (q179467-less
       real-type
       (q179467-distance real-type space x center)
       radius)))))

(defun-sk q179467-preimage-set-law-p (domain)
  (forall (function set x)
    (iff
     (q179467-set-member-p
      (q179467-preimage-set function set) x)
     (and
      (q179467-member-p domain x)
      (q179467-set-member-p
       set (q179467-function-at function x))))))

(defun-sk q179467-translate-set-law-p (space)
  (forall (set shift x)
    (iff
     (q179467-set-member-p
      (q179467-translate-set space set shift) x)
     (and
      (q179467-member-p space x)
      (q179467-set-member-p
       set
       (q179467-add
        space x (q179467-negate space shift)))))))

(defun q179467-set-constructor-laws-p
    (real-type space)
  (and
   (q179467-full-set-law-p space)
   (q179467-complement-set-law-p space)
   (q179467-countable-union-set-law-p space)
   (q179467-open-ball-set-law-p real-type space)
   (q179467-translate-set-law-p space)))

(defun-sk q179467-sequence-measurable-p (family sequence)
  (forall (n)
    (implies
     (natp n)
     (q179467-family-member-p
      family
      (q179467-sequence-at sequence n)))))

(defun-sk q179467-family-valid-sets-p (space family)
  (forall (set)
    (implies
     (q179467-family-member-p family set)
     (q179467-valid-set-p space set))))

(defun-sk q179467-family-extensional-p (space family)
  (forall (left right)
    (implies
     (and
      (q179467-family-member-p family left)
      (q179467-valid-set-p space right)
      (q179467-sets-equal-on-p space left right))
     (q179467-family-member-p family right))))

(defun-sk q179467-sigma-algebra-closure-p (space family)
  (forall (set sequence)
    (and
     (q179467-family-member-p family (q179467-full-set space))
     (implies
      (q179467-family-member-p family set)
      (q179467-family-member-p
       family (q179467-complement-set space set)))
     (implies
      (q179467-sequence-measurable-p family sequence)
      (q179467-family-member-p
       family
       (q179467-countable-union-set space sequence))))))

(defun q179467-sigma-algebra-p (space family)
  (and
   (q179467-family-valid-sets-p space family)
   (q179467-family-extensional-p space family)
   (q179467-sigma-algebra-closure-p space family)))

(defun-sk q179467-balls-measurable-p
    (real-type space family)
  (forall (center radius)
    (implies
     (and
      (q179467-member-p space center)
      (q179467-member-p real-type radius)
      (q179467-positive-p real-type radius))
     (q179467-family-member-p
      family
      (q179467-open-ball-set space center radius)))))

(defun-sk q179467-family-subset-p (left right)
  (forall (set)
    (implies
     (q179467-family-member-p left set)
     (q179467-family-member-p right set))))

(defun-sk q179467-borel-minimal-p
    (real-type space borel)
  (forall (candidate)
    (implies
     (and
      (q179467-sigma-algebra-p space candidate)
      (q179467-balls-measurable-p
       real-type space candidate))
     (q179467-family-subset-p borel candidate))))

(defun q179467-borel-space-p
    (real-type space borel)
  (and
   (q179467-sigma-algebra-p space borel)
   (q179467-balls-measurable-p real-type space borel)
   (q179467-borel-minimal-p real-type space borel)))

(defun q179467-ennreal-p (real-type x)
  (or
   (equal x :q179467-top)
   (and
    (consp x)
    (equal (car x) :q179467-finite)
    (q179467-member-p real-type (cdr x))
    (q179467-leq
     real-type (q179467-zero real-type) (cdr x)))))

(defun q179467-ennreal-finite (x)
  (cons :q179467-finite x))

(defun q179467-ennreal-add (real-type x y)
  (if (or
       (equal x :q179467-top)
       (equal y :q179467-top))
      :q179467-top
    (q179467-ennreal-finite
     (q179467-add real-type (cdr x) (cdr y)))))

(defun q179467-ennreal-leq-p (real-type x y)
  (or
   (equal y :q179467-top)
   (and
    (not (equal x :q179467-top))
    (q179467-leq real-type (cdr x) (cdr y)))))

(defun-sk q179467-disjoint-sequence-p
    (space sequence)
  (forall (i j x)
    (implies
     (and
      (natp i) (natp j)
      (not (equal i j))
      (q179467-member-p space x))
     (not
      (and
       (q179467-set-member-p
        (q179467-sequence-at sequence i) x)
       (q179467-set-member-p
        (q179467-sequence-at sequence j) x))))))

(defun q179467-ennreal-partial-sum
    (real-type measure sequence n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q179467-ennreal-finite (q179467-zero real-type))
    (q179467-ennreal-add
     real-type
     (q179467-ennreal-partial-sum
      real-type measure sequence (- n 1))
     (q179467-measure-value
      measure
      (q179467-sequence-at sequence (- n 1))))))

(defun-sk q179467-ennreal-upper-bound-p
    (real-type measure sequence bound)
  (forall (n)
    (implies
     (natp n)
     (q179467-ennreal-leq-p
      real-type
      (q179467-ennreal-partial-sum
       real-type measure sequence n)
      bound))))

(defun-sk q179467-ennreal-series-value-p
    (real-type measure sequence value)
  (forall (bound)
    (iff
     (q179467-ennreal-upper-bound-p
      real-type measure sequence bound)
     (q179467-ennreal-leq-p real-type value bound))))

(defun-sk q179467-countable-additivity-p
    (real-type space measurable measure)
  (forall (sequence)
    (implies
     (and
      (q179467-sequence-measurable-p measurable sequence)
      (q179467-disjoint-sequence-p space sequence))
     (q179467-ennreal-series-value-p
      real-type
      measure
      sequence
      (q179467-measure-value
       measure
       (q179467-countable-union-set space sequence))))))

(defun-sk q179467-measure-values-p (real-type measure)
  (forall (set)
    (q179467-ennreal-p
     real-type
     (q179467-measure-value measure set))))

(defun-sk q179467-measure-extensional-p (space measure)
  (forall (left right)
    (implies
     (and
      (q179467-valid-set-p space left)
      (q179467-valid-set-p space right)
      (q179467-sets-equal-on-p space left right))
     (equal
      (q179467-measure-value measure left)
      (q179467-measure-value measure right)))))

(defun-sk q179467-empty-measurable-zero-p
    (real-type space measurable measure)
  (forall (set)
    (implies
     (and
      (q179467-family-member-p measurable set)
      (q179467-empty-on-p space set))
     (equal
      (q179467-measure-value measure set)
      (q179467-ennreal-finite
       (q179467-zero real-type))))))

(defun q179467-measure-space-p
    (real-type space measurable measure)
  (and
   (q179467-sigma-algebra-p space measurable)
   (q179467-measure-values-p real-type measure)
   (q179467-measure-extensional-p space measure)
   (q179467-empty-measurable-zero-p
    real-type space measurable measure)
   (equal
    (q179467-measure-value
     measure
     (q179467-complement-set
      space (q179467-full-set space)))
    (q179467-ennreal-finite (q179467-zero real-type)))
   (q179467-countable-additivity-p
    real-type space measurable measure)))

(defun q179467-unit-coordinates-p
    (real-type coordinates x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (let ((c
           (q179467-coordinate
            coordinates x (- n 1))))
      (and
       (q179467-leq
        real-type (q179467-zero real-type) c)
       (q179467-less
        real-type c (q179467-one real-type))
       (q179467-unit-coordinates-p
        real-type coordinates x (- n 1))))))

(defun-sk q179467-unit-cell-coordinate-p
    (real-type space basis coordinates dimension)
  (forall (x)
    (iff
     (q179467-set-member-p
      (q179467-unit-cell-set
       space basis coordinates dimension)
      x)
     (and
      (q179467-member-p space x)
      (q179467-unit-coordinates-p
       real-type coordinates x dimension)))))

(defun-sk q179467-translation-invariant-p
    (space measurable measure)
  (forall (set shift)
    (implies
     (and
      (q179467-family-member-p measurable set)
      (q179467-member-p space shift))
     (equal
      (q179467-measure-value
       measure
       (q179467-translate-set space set shift))
      (q179467-measure-value measure set)))))

(defun q179467-volume-space-p
    (real-type space basis coordinates dimension measurable measure)
  (and
   (q179467-borel-space-p real-type space measurable)
   (q179467-measure-space-p
    real-type space measurable measure)
   (q179467-unit-cell-coordinate-p
    real-type space basis coordinates dimension)
   (q179467-family-member-p
    measurable
    (q179467-unit-cell-set
     space basis coordinates dimension))
   (equal
    (q179467-measure-value
     measure
     (q179467-unit-cell-set
      space basis coordinates dimension))
    (q179467-ennreal-finite
     (q179467-one real-type)))
   (q179467-translation-invariant-p
    space measurable measure)))

;; Lebesgue lower integration and Bochner integration.

(defun-sk q179467-function-into-p
    (domain codomain function)
  (forall (x)
    (implies
     (q179467-member-p domain x)
     (q179467-member-p
      codomain
      (q179467-function-at function x)))))

(defun-sk q179467-continuous-at-delta-p
    (real-type domain codomain function x epsilon delta)
  (forall (y)
    (implies
     (and
      (q179467-member-p domain y)
      (q179467-less
       real-type
       (q179467-distance real-type domain y x)
       delta))
     (q179467-less
      real-type
      (q179467-distance
       real-type codomain
       (q179467-function-at function y)
       (q179467-function-at function x))
      epsilon))))

(defun-sk q179467-continuous-at-epsilon-p
    (real-type domain codomain function x epsilon)
  (exists (delta)
    (and
     (q179467-member-p real-type delta)
     (q179467-positive-p real-type delta)
     (q179467-continuous-at-delta-p
      real-type domain codomain function x epsilon delta))))

(defun-sk q179467-continuous-at-p
    (real-type domain codomain function x)
  (forall (epsilon)
    (implies
     (and
      (q179467-member-p real-type epsilon)
      (q179467-positive-p real-type epsilon))
     (q179467-continuous-at-epsilon-p
      real-type domain codomain function x epsilon))))

(defun-sk q179467-continuous-function-p
    (real-type domain codomain function)
  (forall (x epsilon)
    (implies
     (and
      (q179467-member-p domain x)
      (q179467-member-p real-type epsilon)
      (q179467-positive-p real-type epsilon))
     (q179467-continuous-at-epsilon-p
      real-type domain codomain function x epsilon))))

(defun-sk q179467-function-constructor-laws-p
    (real-type)
  (forall (type f g set value x)
    (and
     (equal
      (q179467-function-at
       (q179467-function-add type f g) x)
      (q179467-add
       type
       (q179467-function-at f x)
       (q179467-function-at g x)))
     (equal
      (q179467-function-at
       (q179467-function-difference type f g) x)
      (q179467-add
       type
       (q179467-function-at f x)
       (q179467-negate
        type (q179467-function-at g x))))
     (equal
      (q179467-function-at
       (q179467-function-norm real-type type f) x)
      (q179467-norm type (q179467-function-at f x)))
     (equal
      (q179467-function-at
       (q179467-indicator-function real-type set) x)
      (if (q179467-set-member-p set x)
          (q179467-one real-type)
        (q179467-zero real-type))))))

(defun-sk q179467-fiber-set-law-p (domain)
  (forall (function value x)
    (iff
     (q179467-set-member-p
      (q179467-fiber-set function value)
      x)
     (and
      (q179467-member-p domain x)
      (equal (q179467-function-at function x) value)))))

(defun-sk q179467-measurable-function-p
    (real-type domain measurable codomain function)
  (forall (center radius)
    (implies
     (and
      (q179467-member-p codomain center)
      (q179467-member-p real-type radius)
      (q179467-positive-p real-type radius))
     (q179467-family-member-p
      measurable
      (q179467-preimage-set
       function
       (q179467-open-ball-set
        codomain center radius))))))

(defun-sk q179467-nonnegative-values-p
    (real-type domain function)
  (forall (x)
    (implies
     (q179467-member-p domain x)
     (q179467-leq
      real-type
      (q179467-zero real-type)
      (q179467-function-at function x)))))

(defun q179467-nonnegative-measurable-p
    (real-type domain measurable function)
  (and
   (q179467-function-into-p
    domain real-type function)
   (q179467-measurable-function-p
    real-type domain measurable real-type function)
   (q179467-nonnegative-values-p
    real-type domain function)))

(defun-sk q179467-pointwise-leq-p
    (real-type domain left right)
  (forall (x)
    (implies
     (q179467-member-p domain x)
     (q179467-leq
      real-type
      (q179467-function-at left x)
      (q179467-function-at right x)))))

(defun-sk q179467-functions-equal-on-p
    (domain left right)
  (forall (x)
    (implies
     (q179467-member-p domain x)
     (equal
      (q179467-function-at left x)
      (q179467-function-at right x)))))

(defun-sk q179467-lintegral-laws-p
    (real-type domain measurable measure lintegral)
  (forall (f g set)
    (and
     (implies
      (q179467-functions-equal-on-p domain f g)
      (equal
       (q179467-lintegral-value lintegral f)
       (q179467-lintegral-value lintegral g)))
     (implies
      (q179467-nonnegative-measurable-p
       real-type domain measurable f)
      (q179467-ennreal-p
       real-type
       (q179467-lintegral-value lintegral f)))
     (implies
      (and
       (q179467-nonnegative-measurable-p
        real-type domain measurable f)
       (q179467-nonnegative-measurable-p
        real-type domain measurable g)
       (q179467-pointwise-leq-p real-type domain f g))
      (q179467-ennreal-leq-p
       real-type
       (q179467-lintegral-value lintegral f)
       (q179467-lintegral-value lintegral g)))
     (implies
      (q179467-family-member-p measurable set)
      (equal
       (q179467-lintegral-value
        lintegral
        (q179467-indicator-function real-type set))
       (q179467-measure-value measure set)))
     (implies
      (and
       (q179467-nonnegative-measurable-p
        real-type domain measurable f)
       (q179467-nonnegative-measurable-p
        real-type domain measurable g))
      (equal
       (q179467-lintegral-value
        lintegral
        (q179467-function-add real-type f g))
       (q179467-ennreal-add
        real-type
        (q179467-lintegral-value lintegral f)
        (q179467-lintegral-value lintegral g)))))))

(defun q179467-simple-values-correct-p
    (domain measurable function values)
  (if (consp values)
      (and
       (q179467-family-member-p
        measurable
        (q179467-fiber-set function (car values)))
       (q179467-simple-values-correct-p
        domain measurable function (cdr values)))
    (equal values nil)))

(defun q179467-simple-listed-values-in-space-p
    (space values)
  (if (consp values)
      (and
       (q179467-member-p space (car values))
       (q179467-simple-listed-values-in-space-p
        space (cdr values)))
    (equal values nil)))

(defun-sk q179467-simple-range-values-p
    (domain function values)
  (forall (x)
    (implies
     (q179467-member-p domain x)
     (member-equal
      (q179467-function-at function x)
      values))))

(defun-sk q179467-value-attained-p
    (domain function value)
  (exists (x)
    (and
     (q179467-member-p domain x)
     (equal
      (q179467-function-at function x)
      value))))

(defun q179467-simple-function-p
    (domain measurable space function)
  (and
   (q179467-function-into-p domain space function)
   (true-listp (q179467-simple-values function))
   (no-duplicatesp-equal (q179467-simple-values function))
   (q179467-simple-listed-values-in-space-p
    space (q179467-simple-values function))
   (q179467-simple-values-correct-p
    domain measurable function
    (q179467-simple-values function))
   (q179467-simple-range-values-p
    domain function
    (q179467-simple-values function))))

(defun q179467-simple-integrable-values-p
    (real-type domain measure zero function values)
  (if (consp values)
      (and
       (implies
        (not
         (q179467-value-attained-p
          domain function (car values)))
        (equal
         (q179467-measure-value
          measure
          (q179467-fiber-set function (car values)))
         (q179467-ennreal-finite
          (q179467-zero real-type))))
       (or
        (equal (car values) zero)
        (not
         (equal
          (q179467-measure-value
           measure
           (q179467-fiber-set function (car values)))
          :q179467-top)))
       (q179467-simple-integrable-values-p
        real-type domain measure zero function (cdr values)))
    (equal values nil)))

(defun q179467-simple-integral
    (real-type domain space measure function values)
  (if (consp values)
      (q179467-add
       space
       (if (or
            (equal (car values) (q179467-zero space))
            (not
             (q179467-value-attained-p
              domain function (car values))))
           (q179467-zero space)
         (q179467-smul
          real-type space
          (cdr
           (q179467-measure-value
            measure
            (q179467-fiber-set function (car values))))
          (car values)))
       (q179467-simple-integral
        real-type domain space measure function (cdr values)))
    (q179467-zero space)))

(defun q179467-ennreal-scale
    (real-type scalar value)
  (if (equal scalar (q179467-zero real-type))
      (q179467-ennreal-finite
       (q179467-zero real-type))
    (if (equal value :q179467-top)
        :q179467-top
      (q179467-ennreal-finite
       (q179467-multiply
        real-type scalar (cdr value))))))

(defun q179467-simple-nonnegative-integral
    (real-type domain measure function values)
  (if (consp values)
      (q179467-ennreal-add
       real-type
       (if
           (q179467-value-attained-p
            domain function (car values))
           (q179467-ennreal-scale
            real-type
            (car values)
            (q179467-measure-value
             measure
             (q179467-fiber-set function (car values))))
         (q179467-ennreal-finite
          (q179467-zero real-type)))
       (q179467-simple-nonnegative-integral
        real-type domain measure function (cdr values)))
    (q179467-ennreal-finite
     (q179467-zero real-type))))

(defun-sk q179467-lintegral-upper-bound-p
    (real-type domain measurable measure function bound)
  (forall (simple)
    (implies
     (and
      (q179467-simple-function-p
       domain measurable real-type simple)
      (q179467-nonnegative-values-p
       real-type domain simple)
      (q179467-pointwise-leq-p
       real-type domain simple function))
     (q179467-ennreal-leq-p
      real-type
      (q179467-simple-nonnegative-integral
       real-type domain measure simple
       (q179467-simple-values simple))
      bound))))

(defun-sk q179467-lintegral-least-upper-bound-p
    (real-type domain measurable measure function value)
  (forall (bound)
    (implies
     (and
      (q179467-ennreal-p real-type bound)
      (q179467-lintegral-upper-bound-p
       real-type domain measurable measure function bound))
     (q179467-ennreal-leq-p real-type value bound))))

(defun-sk q179467-lintegral-supremum-laws-p
    (real-type domain measurable measure lintegral)
  (forall (function)
    (implies
     (and
      (q179467-function-into-p
       domain real-type function)
      (q179467-nonnegative-values-p
       real-type domain function))
     (let ((value
            (q179467-lintegral-value
             lintegral function)))
       (and
        (q179467-ennreal-p real-type value)
        (q179467-lintegral-upper-bound-p
         real-type domain measurable measure function value)
        (q179467-lintegral-least-upper-bound-p
         real-type domain measurable measure function value))))))

(defun-sk q179467-simple-sequence-p
    (domain measurable space sequence)
  (forall (n)
    (implies
     (natp n)
     (q179467-simple-function-p
      domain measurable space
      (q179467-sequence-at sequence n)))))

(defun-sk q179467-pointwise-simple-limit-p
    (real-type domain space sequence function)
  (forall (x)
    (implies
     (q179467-member-p domain x)
     (q179467-converges-p
      real-type
      space
      (q179467-point-sequence sequence x)
      (q179467-function-at function x)))))

(defun-sk q179467-point-sequence-laws-p ()
  (forall (sequence x n)
    (equal
     (q179467-sequence-at
      (q179467-point-sequence sequence x) n)
     (q179467-function-at
      (q179467-sequence-at sequence n) x))))

(defun-sk q179467-strongly-measurable-p
    (real-type domain measurable space function)
  (exists (sequence)
    (and
     (q179467-simple-sequence-p
      domain measurable space sequence)
     (q179467-pointwise-simple-limit-p
      real-type domain space sequence function))))

(defun-sk q179467-equal-outside-p
    (domain exceptional left right)
  (forall (x)
    (implies
     (and
      (q179467-member-p domain x)
      (not (q179467-set-member-p exceptional x)))
     (equal
      (q179467-function-at left x)
      (q179467-function-at right x)))))

(defun-sk q179467-almost-everywhere-equal-p
    (real-type domain measurable measure left right)
  (exists (exceptional)
    (and
     (q179467-family-member-p measurable exceptional)
     (equal
      (q179467-measure-value measure exceptional)
      (q179467-ennreal-finite
       (q179467-zero real-type)))
     (q179467-equal-outside-p
      domain exceptional left right))))

(defun-sk q179467-aestrongly-measurable-p
    (real-type domain measurable measure space function)
  (exists (representative)
    (and
     (q179467-strongly-measurable-p
      real-type domain measurable space representative)
     (q179467-almost-everywhere-equal-p
      real-type domain measurable measure
      function representative))))

(defun q179467-integrable-p
    (real-type domain measurable measure lintegral space function)
  (and
   (q179467-aestrongly-measurable-p
    real-type domain measurable measure space function)
   (not
    (equal
     (q179467-lintegral-value
      lintegral
      (q179467-function-norm real-type space function))
     :q179467-top))))

(defun q179467-l1-distance
    (real-type space lintegral left right)
  (q179467-lintegral-value
   lintegral
   (q179467-function-norm
    real-type space
    (q179467-function-difference space left right))))

(defun-sk q179467-l1-tail-p
    (real-type space lintegral sequence function epsilon start)
  (forall (n)
    (implies
     (and (natp n) (natp start) (<= start n))
     (q179467-ennreal-leq-p
      real-type
      (q179467-l1-distance
       real-type space lintegral
       (q179467-sequence-at sequence n)
       function)
      (q179467-ennreal-finite epsilon)))))

(defun-sk q179467-l1-start-p
    (real-type space lintegral sequence function epsilon)
  (exists (start)
    (and
     (natp start)
     (q179467-l1-tail-p
      real-type space lintegral
      sequence function epsilon start))))

(defun-sk q179467-l1-converges-p
    (real-type space lintegral sequence function)
  (forall (epsilon)
    (implies
     (and
      (q179467-member-p real-type epsilon)
      (q179467-positive-p real-type epsilon))
     (q179467-l1-start-p
      real-type space lintegral sequence function epsilon))))

(defun-sk q179467-integrable-simple-sequence-p
    (real-type domain measurable measure space sequence)
  (forall (n)
    (implies
     (natp n)
     (let ((f (q179467-sequence-at sequence n)))
       (and
        (q179467-simple-function-p
         domain measurable space f)
        (q179467-simple-integrable-values-p
         real-type domain measure
         (q179467-zero space) f
         (q179467-simple-values f)))))))

(defun-sk q179467-simple-integral-sequence-laws-p ()
  (forall (real-type domain space measure sequence n)
    (equal
     (q179467-sequence-at
      (q179467-simple-integral-sequence
       real-type domain space measure sequence)
      n)
     (q179467-simple-integral
      real-type domain space measure
      (q179467-sequence-at sequence n)
      (q179467-simple-values
       (q179467-sequence-at sequence n))))))

(defun q179467-bochner-approximation-p
    (real-type domain measurable measure lintegral
     space function value sequence)
  (and
   (q179467-integrable-simple-sequence-p
    real-type domain measurable measure space sequence)
   (q179467-l1-converges-p
    real-type space lintegral sequence function)
   (q179467-converges-p
    real-type space
    (q179467-simple-integral-sequence
     real-type domain space measure sequence)
    value)))

(defun-sk q179467-bochner-approximation-exists-p
    (real-type domain measurable measure lintegral
     space function value)
  (exists (sequence)
    (q179467-bochner-approximation-p
     real-type domain measurable measure lintegral
     space function value sequence)))

(defun-sk q179467-bochner-integral-operation-p
    (real-type domain measurable measure lintegral space integral)
  (forall (function other)
    (and
     (implies
      (q179467-functions-equal-on-p
       domain function other)
      (equal
       (q179467-bochner-integral-value
        integral function)
       (q179467-bochner-integral-value
        integral other)))
     (implies
      (q179467-function-into-p domain space function)
      (let ((value
             (q179467-bochner-integral-value
              integral function)))
        (and
         (q179467-member-p space value)
         (if
             (and
              (q179467-complete-p real-type space)
              (q179467-integrable-p
               real-type domain measurable measure lintegral
               space function))
             (q179467-bochner-approximation-exists-p
              real-type domain measurable measure lintegral
              space function value)
           (equal value (q179467-zero space)))))))))

;; The normalized Fourier character.

(defun-sk q179467-character-kernel-witness-p
    (real-type complex-type fourier-char x)
  (exists (n)
    (and
     (integerp n)
     (equal x (q179467-integer-cast real-type n)))))

(defun-sk q179467-character-laws-p
    (real-type complex-type fourier-char)
  (forall (x y)
    (implies
     (and
      (q179467-member-p real-type x)
      (q179467-member-p real-type y))
     (and
      (q179467-member-p
       complex-type
       (q179467-character-value fourier-char x))
      (equal
       (q179467-character-value
        fourier-char (q179467-add real-type x y))
       (q179467-multiply
        complex-type
        (q179467-character-value fourier-char x)
        (q179467-character-value fourier-char y)))
      (equal
       (q179467-norm
        complex-type
        (q179467-character-value fourier-char x))
       (q179467-one real-type))
      (iff
       (equal
        (q179467-character-value fourier-char x)
        (q179467-one complex-type))
       (q179467-character-kernel-witness-p
        real-type complex-type fourier-char x))))))

(defun-sk q179467-character-orientation-delta-p
    (real-type complex-type fourier-char delta)
  (forall (x)
    (implies
     (and
      (q179467-member-p real-type x)
      (q179467-positive-p real-type x)
      (q179467-less real-type x delta))
     (q179467-less
      real-type
      (q179467-zero real-type)
      (q179467-imag-part
       real-type complex-type
       (q179467-character-value fourier-char x))))))

(defun-sk q179467-character-orientation-p
    (real-type complex-type fourier-char)
  (exists (delta)
    (and
     (q179467-member-p real-type delta)
     (q179467-positive-p real-type delta)
     (q179467-character-orientation-delta-p
      real-type complex-type fourier-char delta))))

(defun-sk q179467-character-continuity-delta-p
    (real-type complex-type fourier-char epsilon delta)
  (forall (x)
    (implies
     (and
      (q179467-member-p real-type x)
      (q179467-less
       real-type
       (q179467-abs real-type x)
       delta))
     (q179467-less
      real-type
      (q179467-distance
       real-type complex-type
       (q179467-character-value fourier-char x)
       (q179467-one complex-type))
      epsilon))))

(defun-sk q179467-character-continuity-epsilon-p
    (real-type complex-type fourier-char epsilon)
  (exists (delta)
    (and
     (q179467-member-p real-type delta)
     (q179467-positive-p real-type delta)
     (q179467-character-continuity-delta-p
      real-type complex-type fourier-char epsilon delta))))

(defun-sk q179467-character-continuity-p
    (real-type complex-type fourier-char)
  (forall (epsilon)
    (implies
     (and
      (q179467-member-p real-type epsilon)
      (q179467-positive-p real-type epsilon))
     (q179467-character-continuity-epsilon-p
      real-type complex-type fourier-char epsilon))))

(defun q179467-fourier-character-p
    (real-type complex-type fourier-char)
  (and
   (equal
    (q179467-character-value
     fourier-char (q179467-zero real-type))
    (q179467-one complex-type))
   (q179467-character-laws-p
    real-type complex-type fourier-char)
   (q179467-character-continuity-p
    real-type complex-type fourier-char)
   (q179467-character-orientation-p
    real-type complex-type fourier-char)))


(defun-sk q179467-fourier-integrand-laws-p
    (real-type complex-type domain space fourier-char)
  (forall (f frequency x)
    (equal
     (q179467-function-at
      (q179467-fourier-integrand
       real-type complex-type domain space
       fourier-char f frequency)
      x)
     (q179467-smul
      complex-type space
      (q179467-character-value
       fourier-char
       (q179467-negate
        real-type
        (q179467-inner
         real-type domain x frequency)))
      (q179467-function-at f x)))))

(defun-sk q179467-inverse-fourier-integrand-laws-p
    (real-type complex-type domain space fourier-char)
  (forall (f frequency x)
    (equal
     (q179467-function-at
      (q179467-inverse-fourier-integrand
       real-type complex-type domain space
       fourier-char f frequency)
      x)
     (q179467-smul
      complex-type space
      (q179467-character-value
       fourier-char
       (q179467-inner
        real-type domain x frequency))
      (q179467-function-at f x)))))

(defun-sk q179467-fourier-transform-correct-p
    (real-type complex-type domain space
     fourier-char integral fourier function)
  (forall (frequency)
    (implies
     (q179467-member-p domain frequency)
     (and
      (q179467-member-p
       space
       (q179467-function-at
        (q179467-fourier-function fourier function)
        frequency))
      (equal
       (q179467-function-at
        (q179467-fourier-function fourier function)
        frequency)
       (q179467-bochner-integral-value
        integral
        (q179467-fourier-integrand
         real-type complex-type domain space
         fourier-char function frequency)))))))

(defun-sk q179467-fourier-inverse-correct-p
    (real-type complex-type domain space
     fourier-char integral fourier-inverse function)
  (forall (frequency)
    (implies
     (q179467-member-p domain frequency)
     (and
      (q179467-member-p
       space
       (q179467-function-at
        (q179467-fourier-inverse-function
         fourier-inverse function)
        frequency))
      (equal
       (q179467-function-at
        (q179467-fourier-inverse-function
         fourier-inverse function)
        frequency)
       (q179467-bochner-integral-value
        integral
        (q179467-inverse-fourier-integrand
         real-type complex-type domain space
         fourier-char function frequency)))))))

;; The source theorem, with every implicit typeclass and analytic construction
;; represented by the explicit hypotheses above.

(defun q179467-fourier-inversion-context-p
    (real-type complex-type domain space
     basis coordinates dimension
     measurable measure lintegral
     space-integral fourier-char
     fourier fourier-inverse f)
  (and
   (q179467-complex-field-p real-type complex-type)
   (q179467-finite-real-inner-product-space-p
    real-type domain basis coordinates dimension)
   (q179467-complex-banach-space-p
    real-type complex-type space)
   (q179467-set-constructor-laws-p real-type domain)
   (q179467-set-constructor-laws-p real-type real-type)
   (q179467-set-constructor-laws-p real-type space)
   (q179467-preimage-set-law-p domain)
   (q179467-fiber-set-law-p domain)
   (q179467-function-constructor-laws-p real-type)
   (q179467-point-sequence-laws-p)
   (q179467-simple-integral-sequence-laws-p)
   (q179467-volume-space-p
    real-type domain basis coordinates dimension
    measurable measure)
   (q179467-lintegral-laws-p
    real-type domain measurable measure lintegral)
   (q179467-lintegral-supremum-laws-p
    real-type domain measurable measure lintegral)
   (q179467-bochner-integral-operation-p
    real-type domain measurable measure lintegral
    space space-integral)
   (q179467-fourier-character-p
    real-type complex-type fourier-char)
   (q179467-fourier-integrand-laws-p
    real-type complex-type domain space fourier-char)
   (q179467-inverse-fourier-integrand-laws-p
    real-type complex-type domain space fourier-char)
   (q179467-function-into-p domain space f)
   (q179467-fourier-transform-correct-p
    real-type complex-type domain space
    fourier-char space-integral fourier f)
   (q179467-fourier-inverse-correct-p
    real-type complex-type domain space
    fourier-char space-integral fourier-inverse
    (q179467-fourier-function fourier f))))

(defun q179467-fourier-inversion-assumptions-p
    (real-type complex-type domain space
     basis coordinates dimension
     measurable measure lintegral
     space-integral fourier-char
     fourier fourier-inverse f)
  (and
   (q179467-fourier-inversion-context-p
    real-type complex-type domain space
    basis coordinates dimension
    measurable measure lintegral
    space-integral fourier-char
    fourier fourier-inverse f)
   (q179467-integrable-p
    real-type domain measurable measure lintegral
    space f)
   (q179467-integrable-p
    real-type domain measurable measure lintegral
    space
    (q179467-fourier-function fourier f))))

(defun-sk q179467-pointwise-fourier-inversion-statement
    (real-type complex-type domain space
     basis coordinates dimension
     measurable measure lintegral
     space-integral fourier-char
     fourier fourier-inverse f)
  (forall (v)
    (implies
     (and
      (q179467-fourier-inversion-assumptions-p
       real-type complex-type domain space
       basis coordinates dimension
       measurable measure lintegral
       space-integral fourier-char
       fourier fourier-inverse f)
      (q179467-member-p domain v)
      (q179467-continuous-at-p
       real-type domain space f v))
     (equal
      (q179467-function-at
       (q179467-fourier-inverse-function
        fourier-inverse
        (q179467-fourier-function fourier f))
       v)
      (q179467-function-at f v)))))

(defun q179467-continuous-fourier-inversion-statement
    (real-type complex-type domain space
     basis coordinates dimension
     measurable measure lintegral
     space-integral fourier-char
     fourier fourier-inverse f)
  (implies
   (and
    (q179467-fourier-inversion-assumptions-p
     real-type complex-type domain space
     basis coordinates dimension
     measurable measure lintegral
     space-integral fourier-char
     fourier fourier-inverse f)
    (q179467-continuous-function-p
     real-type domain space f))
   (q179467-functions-equal-on-p
    domain
    (q179467-fourier-inverse-function
     fourier-inverse
     (q179467-fourier-function fourier f))
    f)))

(defun thousand-theorems-q179467-fourier-theorem-statement
    (real-type complex-type domain space
     basis coordinates dimension
     measurable measure lintegral
     space-integral fourier-char
     fourier fourier-inverse f)
  (and
   (q179467-pointwise-fourier-inversion-statement
    real-type complex-type domain space
    basis coordinates dimension
    measurable measure lintegral
    space-integral fourier-char
    fourier fourier-inverse f)
   (q179467-continuous-fourier-inversion-statement
    real-type complex-type domain space
    basis coordinates dimension
    measurable measure lintegral
    space-integral fourier-char
    fourier fourier-inverse f)))

(value-triple :itpeval-statement-checked)
:q
