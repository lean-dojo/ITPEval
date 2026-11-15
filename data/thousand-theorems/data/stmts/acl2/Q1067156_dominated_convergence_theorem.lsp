;; Statement-only formalization of thousand-theorems corpus artifact Q1067156,
;; "Dominated convergence theorem": an almost-everywhere convergent sequence
;; of almost-everywhere strongly measurable functions into an arbitrary real
;; normed space has convergent Bochner integrals when its norms are dominated
;; almost everywhere by an integrable real function. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Mathematical objects are unrestricted ACL2 objects. The conservative
;; interfaces below only provide application and constructor symbols; every
;; real-field, normed-space, measure, measurability, convergence, and Bochner
;; integration law used by the statement is imposed explicitly by predicates.

(defstub q1067156-member-p (type object) t)
(defstub q1067156-zero (type) t)
(defstub q1067156-one (type) t)
(defstub q1067156-add (type left right) t)
(defstub q1067156-multiply (type left right) t)
(defstub q1067156-negate (type object) t)
(defstub q1067156-inverse (type object) t)
(defstub q1067156-less (type left right) t)
(defstub q1067156-norm (type object) t)
(defstub q1067156-smul (scalar-type space scalar vector) t)
(defstub q1067156-star (scalar-type scalar) t)
(defstub q1067156-real-part (real-type scalar-type scalar) t)
(defstub q1067156-imag-part (real-type scalar-type scalar) t)
(defstub q1067156-of-real (real-type scalar-type real) t)
(defstub q1067156-imaginary-unit (scalar-type) t)
(defstub q1067156-inner (scalar-type space left right) t)
(defstub q1067156-function-at (function argument) t)
(defstub q1067156-sequence-at (sequence index) t)
(defstub q1067156-basis-at (basis index) t)
(defstub q1067156-coordinate (coordinates vector index) t)
(defstub q1067156-derivative-function (derivatives function multiindex) t)
(defstub q1067156-fourier-function (fourier function) t)
(defstub q1067156-character-value (fourier-char real) t)
(defstub q1067156-set-member-p (set object) t)
(defstub q1067156-family-member-p (family set) t)
(defstub q1067156-open-ball-set (space center radius) t)
(defstub q1067156-preimage-set (function set) t)
(defstub q1067156-complement-set (carrier set) t)
(defstub q1067156-countable-union-set (carrier sequence) t)
(defstub q1067156-translate-set (space set shift) t)
(defstub q1067156-unit-cell-set (space basis coordinates dimension) t)
(defstub q1067156-fiber-set (function value) t)
(defstub q1067156-simple-values (function) t)
(defstub q1067156-indicator-function (real-type set) t)
(defstub q1067156-function-add (type left right) t)
(defstub q1067156-function-difference (type left right) t)
(defstub q1067156-function-norm (real-type type function) t)
(defstub q1067156-inner-integrand (scalar-type space left right) t)
(defstub q1067156-fourier-integrand
  (real-type scalar-type domain space fourier-char function frequency) t)
(defstub q1067156-measure-value (measure set) t)
(defstub q1067156-lintegral-value (lintegral function) t)
(defstub q1067156-bochner-integral-value (integral function) t)
(defstub q1067156-full-set (carrier) t)
(defstub q1067156-point-sequence (function-sequence point) t)
(defstub q1067156-simple-integral-sequence
  (real-type domain space measure function-sequence) t)

(defun q1067156-positive-p (real-type x)
  (q1067156-less real-type (q1067156-zero real-type) x))

(defun q1067156-leq (real-type x y)
  (not (q1067156-less real-type y x)))

(defun q1067156-abs (real-type x)
  (if (q1067156-less real-type x (q1067156-zero real-type))
      (q1067156-negate real-type x)
    x))

(defun q1067156-natural-cast (type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1067156-zero type)
    (q1067156-add
     type
     (q1067156-one type)
     (q1067156-natural-cast type (- n 1)))))

(defun q1067156-integer-cast (type n)
  (if (and (integerp n) (< n 0))
      (q1067156-negate
       type
       (q1067156-natural-cast type (- n)))
    (q1067156-natural-cast type (nfix n))))

(defun q1067156-real-power (real-type x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1067156-one real-type)
    (q1067156-multiply
     real-type x
     (q1067156-real-power real-type x (- n 1)))))

(defun q1067156-vector-sum
    (real-type space basis coordinates vector n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1067156-zero space)
    (let ((i (- n 1)))
      (q1067156-add
       space
       (q1067156-vector-sum
        real-type space basis coordinates vector i)
       (q1067156-smul
        real-type space
        (q1067156-coordinate coordinates vector i)
        (q1067156-basis-at basis i))))))

(defun q1067156-zero-multiindex (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (q1067156-zero-multiindex (- n 1)))))

(defun q1067156-natural-list-p (alpha n)
  (if (zp n)
      (equal alpha nil)
    (and
     (consp alpha)
     (natp (car alpha))
     (q1067156-natural-list-p (cdr alpha) (- n 1)))))

(defun q1067156-increment-multiindex (alpha i)
  (if (consp alpha)
      (if (zp i)
          (cons (+ 1 (nfix (car alpha))) (cdr alpha))
        (cons
         (car alpha)
         (q1067156-increment-multiindex (cdr alpha) (- i 1))))
    nil))

(defun q1067156-multiindex-degree (alpha)
  (if (consp alpha)
      (+ (nfix (car alpha))
         (q1067156-multiindex-degree (cdr alpha)))
    0))

;; Complete ordered real field and its canonical complexification.

(defun-sk q1067156-field-laws-p (type)
  (forall (x y z)
    (implies
     (and
      (q1067156-member-p type x)
      (q1067156-member-p type y)
      (q1067156-member-p type z))
     (and
      (q1067156-member-p type (q1067156-add type x y))
      (q1067156-member-p type (q1067156-multiply type x y))
      (q1067156-member-p type (q1067156-negate type x))
      (implies
       (not (equal x (q1067156-zero type)))
       (q1067156-member-p type (q1067156-inverse type x)))
      (equal
       (q1067156-add type (q1067156-add type x y) z)
       (q1067156-add type x (q1067156-add type y z)))
      (equal (q1067156-add type x y) (q1067156-add type y x))
      (equal (q1067156-add type x (q1067156-zero type)) x)
      (equal
       (q1067156-add type x (q1067156-negate type x))
       (q1067156-zero type))
      (equal
       (q1067156-multiply type (q1067156-multiply type x y) z)
       (q1067156-multiply type x (q1067156-multiply type y z)))
      (equal
       (q1067156-multiply type x y)
       (q1067156-multiply type y x))
      (equal (q1067156-multiply type x (q1067156-one type)) x)
      (implies
       (not (equal x (q1067156-zero type)))
       (equal
        (q1067156-multiply type x (q1067156-inverse type x))
        (q1067156-one type)))
      (equal
       (q1067156-multiply type x (q1067156-add type y z))
       (q1067156-add
        type
        (q1067156-multiply type x y)
        (q1067156-multiply type x z)))))))

(defun-sk q1067156-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q1067156-member-p real-type x)
      (q1067156-member-p real-type y)
      (q1067156-member-p real-type z))
     (and
      (not (q1067156-less real-type x x))
      (or
       (q1067156-less real-type x y)
       (equal x y)
       (q1067156-less real-type y x))
      (implies
       (and
        (q1067156-less real-type x y)
        (q1067156-less real-type y z))
       (q1067156-less real-type x z))
      (implies
       (q1067156-less real-type x y)
       (q1067156-less
        real-type
        (q1067156-add real-type x z)
        (q1067156-add real-type y z)))
      (implies
       (and
        (q1067156-positive-p real-type x)
        (q1067156-positive-p real-type y))
       (q1067156-positive-p
        real-type
        (q1067156-multiply real-type x y)))))))

(defun q1067156-distance
    (real-type type x y)
  (declare (ignore real-type))
  (q1067156-norm
   type
   (q1067156-add type x (q1067156-negate type y))))

(defun-sk q1067156-norm-values-p (real-type type)
  (forall (x)
    (implies
     (q1067156-member-p type x)
     (and
      (q1067156-member-p real-type (q1067156-norm type x))
      (q1067156-leq
       real-type
       (q1067156-zero real-type)
       (q1067156-norm type x))
      (iff
       (equal
        (q1067156-norm type x)
        (q1067156-zero real-type))
       (equal x (q1067156-zero type)))))))

(defun-sk q1067156-norm-triangle-p (real-type type)
  (forall (x y)
    (implies
     (and
      (q1067156-member-p type x)
      (q1067156-member-p type y))
     (q1067156-leq
      real-type
      (q1067156-norm type (q1067156-add type x y))
      (q1067156-add
       real-type
       (q1067156-norm type x)
       (q1067156-norm type y))))))

(defun q1067156-norm-laws-p (real-type type)
  (and
   (q1067156-norm-values-p real-type type)
   (q1067156-norm-triangle-p real-type type)))

(defun-sk q1067156-convergence-tail-p
    (real-type type sequence limit epsilon start)
  (forall (n)
    (implies
     (and (natp n) (natp start) (<= start n))
     (q1067156-less
      real-type
      (q1067156-distance
       real-type type
       (q1067156-sequence-at sequence n)
       limit)
      epsilon))))

(defun-sk q1067156-convergence-start-p
    (real-type type sequence limit epsilon)
  (exists (start)
    (and
     (natp start)
     (q1067156-convergence-tail-p
      real-type type sequence limit epsilon start))))

(defun-sk q1067156-converges-p
    (real-type type sequence limit)
  (forall (epsilon)
    (implies
     (and
      (q1067156-member-p real-type epsilon)
      (q1067156-positive-p real-type epsilon))
     (q1067156-convergence-start-p
      real-type type sequence limit epsilon))))

(defun-sk q1067156-cauchy-tail-p
    (real-type type sequence epsilon start)
  (forall (m n)
    (implies
     (and
      (natp m) (natp n) (natp start)
      (<= start m) (<= start n))
     (q1067156-less
      real-type
      (q1067156-distance
       real-type type
       (q1067156-sequence-at sequence m)
       (q1067156-sequence-at sequence n))
      epsilon))))

(defun-sk q1067156-cauchy-start-p
    (real-type type sequence epsilon)
  (exists (start)
    (and
     (natp start)
     (q1067156-cauchy-tail-p
      real-type type sequence epsilon start))))

(defun-sk q1067156-cauchy-p (real-type type sequence)
  (forall (epsilon)
    (implies
     (and
      (q1067156-member-p real-type epsilon)
      (q1067156-positive-p real-type epsilon))
     (q1067156-cauchy-start-p
      real-type type sequence epsilon))))

(defun-sk q1067156-sequence-in-type-p (type sequence)
  (forall (n)
    (implies
     (natp n)
     (q1067156-member-p
      type
      (q1067156-sequence-at sequence n)))))

(defun-sk q1067156-limit-exists-p
    (real-type type sequence)
  (exists (limit)
    (and
     (q1067156-member-p type limit)
     (q1067156-converges-p
      real-type type sequence limit))))

(defun-sk q1067156-complete-p (real-type type)
  (forall (sequence)
    (implies
     (and
      (q1067156-sequence-in-type-p type sequence)
      (q1067156-cauchy-p real-type type sequence))
     (q1067156-limit-exists-p
      real-type type sequence))))

(defun-sk q1067156-archimedean-witness-p (real-type x)
  (exists (n)
    (and
     (natp n)
     (q1067156-less
      real-type x
      (q1067156-natural-cast real-type n)))))

(defun-sk q1067156-archimedean-p (real-type)
  (forall (x)
    (implies
     (q1067156-member-p real-type x)
     (q1067156-archimedean-witness-p real-type x))))

(defun-sk q1067156-real-norm-laws-p (real-type)
  (forall (x)
    (implies
     (q1067156-member-p real-type x)
     (and
      (equal
       (q1067156-norm real-type x)
       (q1067156-abs real-type x))
      (equal (q1067156-star real-type x) x)
      (equal
       (q1067156-real-part real-type real-type x)
       x)
      (equal
       (q1067156-imag-part real-type real-type x)
       (q1067156-zero real-type))
      (equal
       (q1067156-of-real real-type real-type x)
       x)))))

(defun q1067156-real-field-p (real-type)
  (and
   (q1067156-member-p real-type (q1067156-zero real-type))
   (q1067156-member-p real-type (q1067156-one real-type))
   (not
    (equal
     (q1067156-zero real-type)
     (q1067156-one real-type)))
   (q1067156-field-laws-p real-type)
   (q1067156-order-laws-p real-type)
   (q1067156-positive-p real-type (q1067156-one real-type))
   (q1067156-real-norm-laws-p real-type)
   (q1067156-complete-p real-type real-type)
   (q1067156-archimedean-p real-type)))

(defun-sk q1067156-complex-coordinate-laws-p
    (real-type complex-type)
  (forall (z)
    (implies
     (q1067156-member-p complex-type z)
     (let* ((re (q1067156-real-part real-type complex-type z))
            (im (q1067156-imag-part real-type complex-type z))
            (re-z (q1067156-of-real real-type complex-type re))
            (im-z
             (q1067156-multiply
              complex-type
              (q1067156-of-real real-type complex-type im)
              (q1067156-imaginary-unit complex-type))))
       (and
        (q1067156-member-p real-type re)
        (q1067156-member-p real-type im)
        (equal z (q1067156-add complex-type re-z im-z))
        (equal
         (q1067156-star complex-type z)
         (q1067156-add
          complex-type re-z
          (q1067156-negate complex-type im-z)))
        (equal
         (q1067156-multiply
          real-type
          (q1067156-norm complex-type z)
          (q1067156-norm complex-type z))
         (q1067156-add
          real-type
          (q1067156-multiply real-type re re)
          (q1067156-multiply real-type im im))))))))

(defun-sk q1067156-of-real-laws-p
    (real-type complex-type)
  (forall (x y)
    (implies
     (and
      (q1067156-member-p real-type x)
      (q1067156-member-p real-type y))
     (and
      (q1067156-member-p
       complex-type
       (q1067156-of-real real-type complex-type x))
      (equal
       (q1067156-real-part
        real-type complex-type
        (q1067156-of-real real-type complex-type x))
       x)
      (equal
       (q1067156-imag-part
        real-type complex-type
        (q1067156-of-real real-type complex-type x))
       (q1067156-zero real-type))
      (equal
       (q1067156-of-real
        real-type complex-type
        (q1067156-add real-type x y))
       (q1067156-add
        complex-type
        (q1067156-of-real real-type complex-type x)
        (q1067156-of-real real-type complex-type y)))
      (equal
       (q1067156-of-real
        real-type complex-type
        (q1067156-multiply real-type x y))
       (q1067156-multiply
        complex-type
        (q1067156-of-real real-type complex-type x)
        (q1067156-of-real real-type complex-type y)))))))

(defun q1067156-complex-field-p
    (real-type complex-type)
  (and
   (q1067156-real-field-p real-type)
   (q1067156-member-p complex-type (q1067156-zero complex-type))
   (q1067156-member-p complex-type (q1067156-one complex-type))
   (not
    (equal
     (q1067156-zero complex-type)
     (q1067156-one complex-type)))
   (q1067156-field-laws-p complex-type)
   (q1067156-of-real-laws-p real-type complex-type)
   (equal
    (q1067156-of-real
     real-type complex-type (q1067156-zero real-type))
    (q1067156-zero complex-type))
   (equal
    (q1067156-of-real
     real-type complex-type (q1067156-one real-type))
    (q1067156-one complex-type))
   (equal
    (q1067156-multiply
     complex-type
     (q1067156-imaginary-unit complex-type)
     (q1067156-imaginary-unit complex-type))
    (q1067156-negate complex-type (q1067156-one complex-type)))
   (equal
    (q1067156-real-part
     real-type complex-type
     (q1067156-imaginary-unit complex-type))
    (q1067156-zero real-type))
   (equal
    (q1067156-imag-part
     real-type complex-type
     (q1067156-imaginary-unit complex-type))
    (q1067156-one real-type))
   (q1067156-complex-coordinate-laws-p real-type complex-type)
   (q1067156-norm-laws-p real-type complex-type)
   (q1067156-complete-p real-type complex-type)))

;; Real and complex inner-product spaces.

(defun-sk q1067156-vector-space-laws-p
    (scalar-type space)
  (forall (a b x y z)
    (implies
     (and
      (q1067156-member-p scalar-type a)
      (q1067156-member-p scalar-type b)
      (q1067156-member-p space x)
      (q1067156-member-p space y)
      (q1067156-member-p space z))
     (and
      (q1067156-member-p space (q1067156-add space x y))
      (q1067156-member-p space (q1067156-negate space x))
      (q1067156-member-p
       space (q1067156-smul scalar-type space a x))
      (equal
       (q1067156-add space (q1067156-add space x y) z)
       (q1067156-add space x (q1067156-add space y z)))
      (equal (q1067156-add space x y) (q1067156-add space y x))
      (equal (q1067156-add space x (q1067156-zero space)) x)
      (equal
       (q1067156-add space x (q1067156-negate space x))
       (q1067156-zero space))
      (equal
       (q1067156-smul
        scalar-type space (q1067156-one scalar-type) x)
       x)
      (equal
       (q1067156-smul
        scalar-type space
        (q1067156-multiply scalar-type a b) x)
       (q1067156-smul
        scalar-type space a
        (q1067156-smul scalar-type space b x)))
      (equal
       (q1067156-smul
        scalar-type space
        (q1067156-add scalar-type a b) x)
       (q1067156-add
        space
        (q1067156-smul scalar-type space a x)
        (q1067156-smul scalar-type space b x)))
      (equal
       (q1067156-smul
        scalar-type space a (q1067156-add space x y))
       (q1067156-add
        space
        (q1067156-smul scalar-type space a x)
        (q1067156-smul scalar-type space a y)))))))

(defun-sk q1067156-normed-space-laws-p
    (real-type scalar-type space)
  (forall (a x)
    (implies
     (and
      (q1067156-member-p scalar-type a)
      (q1067156-member-p space x))
     (equal
      (q1067156-norm
       space
       (q1067156-smul scalar-type space a x))
      (q1067156-multiply
       real-type
       (q1067156-norm scalar-type a)
       (q1067156-norm space x))))))

(defun-sk q1067156-inner-product-laws-p
    (real-type scalar-type space)
  (forall (a x y z)
    (implies
     (and
      (q1067156-member-p scalar-type a)
      (q1067156-member-p space x)
      (q1067156-member-p space y)
      (q1067156-member-p space z))
     (let ((xy (q1067156-inner scalar-type space x y))
           (xx (q1067156-inner scalar-type space x x)))
       (and
        (q1067156-member-p scalar-type xy)
        (equal
         (q1067156-inner
          scalar-type space x (q1067156-add space y z))
         (q1067156-add
          scalar-type xy
          (q1067156-inner scalar-type space x z)))
        (equal
         (q1067156-inner
          scalar-type space x
          (q1067156-smul scalar-type space a y))
         (q1067156-multiply scalar-type a xy))
        (equal
         (q1067156-inner scalar-type space y x)
         (q1067156-star scalar-type xy))
        (equal
         (q1067156-multiply
          real-type
          (q1067156-norm space x)
          (q1067156-norm space x))
         (q1067156-real-part real-type scalar-type xx))
        (iff
         (equal xx (q1067156-zero scalar-type))
         (equal x (q1067156-zero space))))))))

(defun-sk q1067156-real-smul-compatibility-p
    (real-type complex-type space)
  (forall (r x)
    (implies
     (and
      (q1067156-member-p real-type r)
      (q1067156-member-p space x))
     (equal
      (q1067156-smul real-type space r x)
      (q1067156-smul
       complex-type space
       (q1067156-of-real real-type complex-type r)
       x)))))

(defun-sk q1067156-orthonormal-basis-laws-p
    (real-type space basis coordinates dimension)
  (forall (i j x)
    (and
     (implies
      (and (natp i) (< i dimension))
      (q1067156-member-p space (q1067156-basis-at basis i)))
     (implies
      (and
       (natp i) (natp j)
       (< i dimension) (< j dimension))
      (equal
       (q1067156-inner
        real-type space
        (q1067156-basis-at basis i)
        (q1067156-basis-at basis j))
       (if (equal i j)
           (q1067156-one real-type)
         (q1067156-zero real-type))))
     (implies
      (q1067156-member-p space x)
      (and
       (implies
        (and (natp i) (< i dimension))
        (q1067156-member-p
         real-type
         (q1067156-coordinate coordinates x i)))
       (equal
        x
        (q1067156-vector-sum
         real-type space basis coordinates x dimension)))))))

(defun q1067156-finite-real-inner-product-space-p
    (real-type space basis coordinates dimension)
  (and
   (natp dimension)
   (q1067156-member-p space (q1067156-zero space))
   (q1067156-vector-space-laws-p real-type space)
   (q1067156-norm-laws-p real-type space)
   (q1067156-normed-space-laws-p real-type real-type space)
   (q1067156-inner-product-laws-p real-type real-type space)
   (q1067156-orthonormal-basis-laws-p
    real-type space basis coordinates dimension)))

(defun q1067156-complex-hilbert-space-p
    (real-type complex-type space)
  (and
   (q1067156-member-p space (q1067156-zero space))
   (q1067156-vector-space-laws-p complex-type space)
   (q1067156-vector-space-laws-p real-type space)
   (q1067156-norm-laws-p real-type space)
   (q1067156-normed-space-laws-p
    real-type complex-type space)
   (q1067156-normed-space-laws-p
    real-type real-type space)
   (q1067156-real-smul-compatibility-p
    real-type complex-type space)
   (q1067156-inner-product-laws-p
    real-type complex-type space)
   (q1067156-complete-p real-type space)))

;; Borel sigma algebra and normalized translation-invariant volume.

(defun-sk q1067156-countable-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q1067156-set-member-p
      (q1067156-sequence-at sequence n) x))))

(defun-sk q1067156-valid-set-p (space set)
  (forall (x)
    (implies
     (q1067156-set-member-p set x)
     (q1067156-member-p space x))))

(defun-sk q1067156-sets-equal-on-p (space left right)
  (forall (x)
    (implies
     (q1067156-member-p space x)
     (iff
      (q1067156-set-member-p left x)
      (q1067156-set-member-p right x)))))

(defun-sk q1067156-empty-on-p (space set)
  (forall (x)
    (implies
     (q1067156-member-p space x)
     (not (q1067156-set-member-p set x)))))

(defun-sk q1067156-full-set-law-p (space)
  (forall (x)
    (iff
     (q1067156-set-member-p
      (q1067156-full-set space) x)
     (q1067156-member-p space x))))

(defun-sk q1067156-complement-set-law-p (space)
  (forall (set x)
    (iff
     (q1067156-set-member-p
      (q1067156-complement-set space set) x)
     (and
      (q1067156-member-p space x)
      (not (q1067156-set-member-p set x))))))

(defun-sk q1067156-countable-union-set-law-p (space)
  (forall (sequence x)
    (iff
     (q1067156-set-member-p
      (q1067156-countable-union-set space sequence) x)
     (and
      (q1067156-member-p space x)
      (q1067156-countable-union-member-p sequence x)))))

(defun-sk q1067156-open-ball-set-law-p (real-type space)
  (forall (center radius x)
    (iff
     (q1067156-set-member-p
      (q1067156-open-ball-set space center radius) x)
     (and
      (q1067156-member-p space x)
      (q1067156-member-p space center)
      (q1067156-member-p real-type radius)
      (q1067156-less
       real-type
       (q1067156-distance real-type space x center)
       radius)))))

(defun-sk q1067156-preimage-set-law-p (domain)
  (forall (function set x)
    (iff
     (q1067156-set-member-p
      (q1067156-preimage-set function set) x)
     (and
      (q1067156-member-p domain x)
      (q1067156-set-member-p
       set (q1067156-function-at function x))))))

(defun-sk q1067156-translate-set-law-p (space)
  (forall (set shift x)
    (iff
     (q1067156-set-member-p
      (q1067156-translate-set space set shift) x)
     (and
      (q1067156-member-p space x)
      (q1067156-set-member-p
       set
       (q1067156-add
        space x (q1067156-negate space shift)))))))

(defun q1067156-set-constructor-laws-p
    (real-type space)
  (and
   (q1067156-full-set-law-p space)
   (q1067156-complement-set-law-p space)
   (q1067156-countable-union-set-law-p space)
   (q1067156-open-ball-set-law-p real-type space)
   (q1067156-translate-set-law-p space)))

(defun-sk q1067156-sequence-measurable-p (family sequence)
  (forall (n)
    (implies
     (natp n)
     (q1067156-family-member-p
      family
      (q1067156-sequence-at sequence n)))))

(defun-sk q1067156-family-valid-sets-p (space family)
  (forall (set)
    (implies
     (q1067156-family-member-p family set)
     (q1067156-valid-set-p space set))))

(defun-sk q1067156-family-extensional-p (space family)
  (forall (left right)
    (implies
     (and
      (q1067156-family-member-p family left)
      (q1067156-valid-set-p space right)
      (q1067156-sets-equal-on-p space left right))
     (q1067156-family-member-p family right))))

(defun-sk q1067156-sigma-algebra-closure-p (space family)
  (forall (set sequence)
    (and
     (q1067156-family-member-p family (q1067156-full-set space))
     (implies
      (q1067156-family-member-p family set)
      (q1067156-family-member-p
       family (q1067156-complement-set space set)))
     (implies
      (q1067156-sequence-measurable-p family sequence)
      (q1067156-family-member-p
       family
       (q1067156-countable-union-set space sequence))))))

(defun q1067156-sigma-algebra-p (space family)
  (and
   (q1067156-family-valid-sets-p space family)
   (q1067156-family-extensional-p space family)
   (q1067156-sigma-algebra-closure-p space family)))

(defun-sk q1067156-balls-measurable-p
    (real-type space family)
  (forall (center radius)
    (implies
     (and
      (q1067156-member-p space center)
      (q1067156-member-p real-type radius)
      (q1067156-positive-p real-type radius))
     (q1067156-family-member-p
      family
      (q1067156-open-ball-set space center radius)))))

(defun-sk q1067156-family-subset-p (left right)
  (forall (set)
    (implies
     (q1067156-family-member-p left set)
     (q1067156-family-member-p right set))))

(defun-sk q1067156-borel-minimal-p
    (real-type space borel)
  (forall (candidate)
    (implies
     (and
      (q1067156-sigma-algebra-p space candidate)
      (q1067156-balls-measurable-p
       real-type space candidate))
     (q1067156-family-subset-p borel candidate))))

(defun q1067156-borel-space-p
    (real-type space borel)
  (and
   (q1067156-sigma-algebra-p space borel)
   (q1067156-balls-measurable-p real-type space borel)
   (q1067156-borel-minimal-p real-type space borel)))

(defun q1067156-ennreal-p (real-type x)
  (or
   (equal x :q1067156-top)
   (and
    (consp x)
    (equal (car x) :q1067156-finite)
    (q1067156-member-p real-type (cdr x))
    (q1067156-leq
     real-type (q1067156-zero real-type) (cdr x)))))

(defun q1067156-ennreal-finite (x)
  (cons :q1067156-finite x))

(defun q1067156-ennreal-add (real-type x y)
  (if (or
       (equal x :q1067156-top)
       (equal y :q1067156-top))
      :q1067156-top
    (q1067156-ennreal-finite
     (q1067156-add real-type (cdr x) (cdr y)))))

(defun q1067156-ennreal-leq-p (real-type x y)
  (or
   (equal y :q1067156-top)
   (and
    (not (equal x :q1067156-top))
    (q1067156-leq real-type (cdr x) (cdr y)))))

(defun-sk q1067156-disjoint-sequence-p
    (space sequence)
  (forall (i j x)
    (implies
     (and
      (natp i) (natp j)
      (not (equal i j))
      (q1067156-member-p space x))
     (not
      (and
       (q1067156-set-member-p
        (q1067156-sequence-at sequence i) x)
       (q1067156-set-member-p
        (q1067156-sequence-at sequence j) x))))))

(defun-sk q1067156-sequence-valid-sets-p
    (space sequence)
  (forall (n)
    (implies
     (natp n)
     (q1067156-valid-set-p
      space
      (q1067156-sequence-at sequence n)))))

(defun-sk q1067156-set-subset-p
    (space left right)
  (forall (x)
    (implies
     (and
      (q1067156-member-p space x)
      (q1067156-set-member-p left x))
     (q1067156-set-member-p right x))))

(defun q1067156-ennreal-partial-sum
    (real-type measure sequence n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1067156-ennreal-finite (q1067156-zero real-type))
    (q1067156-ennreal-add
     real-type
     (q1067156-ennreal-partial-sum
      real-type measure sequence (- n 1))
     (q1067156-measure-value
      measure
      (q1067156-sequence-at sequence (- n 1))))))

(defun-sk q1067156-ennreal-upper-bound-p
    (real-type measure sequence bound)
  (forall (n)
    (implies
     (natp n)
     (q1067156-ennreal-leq-p
      real-type
      (q1067156-ennreal-partial-sum
       real-type measure sequence n)
      bound))))

(defun-sk q1067156-ennreal-series-value-p
    (real-type measure sequence value)
  (forall (bound)
    (iff
     (q1067156-ennreal-upper-bound-p
      real-type measure sequence bound)
     (q1067156-ennreal-leq-p real-type value bound))))

(defun-sk q1067156-countable-additivity-p
    (real-type space measurable measure)
  (forall (sequence)
    (implies
     (and
      (q1067156-sequence-measurable-p measurable sequence)
      (q1067156-disjoint-sequence-p space sequence))
     (q1067156-ennreal-series-value-p
      real-type
      measure
      sequence
     (q1067156-measure-value
       measure
       (q1067156-countable-union-set space sequence))))))

(defun-sk q1067156-measure-monotone-p
    (real-type space measure)
  (forall (left right)
    (implies
     (and
      (q1067156-valid-set-p space left)
      (q1067156-valid-set-p space right)
      (q1067156-set-subset-p space left right))
     (q1067156-ennreal-leq-p
      real-type
      (q1067156-measure-value measure left)
      (q1067156-measure-value measure right)))))

(defun q1067156-countable-subadditivity-witness-p
    (real-type space measure sequence value)
  (and
   (q1067156-ennreal-p real-type value)
   (q1067156-ennreal-series-value-p
    real-type measure sequence value)
   (q1067156-ennreal-leq-p
    real-type
    (q1067156-measure-value
     measure
     (q1067156-countable-union-set space sequence))
    value)))

(defun-sk q1067156-countable-subadditivity-value-p
    (real-type space measure sequence)
  (exists (value)
    (q1067156-countable-subadditivity-witness-p
     real-type space measure sequence value)))

(defun-sk q1067156-countable-subadditivity-p
    (real-type space measure)
  (forall (sequence)
    (implies
     (q1067156-sequence-valid-sets-p space sequence)
     (q1067156-countable-subadditivity-value-p
      real-type space measure sequence))))

(defun-sk q1067156-measure-values-p (real-type measure)
  (forall (set)
    (q1067156-ennreal-p
     real-type
     (q1067156-measure-value measure set))))

(defun-sk q1067156-measure-extensional-p (space measure)
  (forall (left right)
    (implies
     (and
      (q1067156-valid-set-p space left)
      (q1067156-valid-set-p space right)
      (q1067156-sets-equal-on-p space left right))
     (equal
      (q1067156-measure-value measure left)
      (q1067156-measure-value measure right)))))

(defun-sk q1067156-empty-set-zero-p
    (real-type space measure)
  (forall (set)
    (implies
     (and
      (q1067156-valid-set-p space set)
      (q1067156-empty-on-p space set))
     (equal
      (q1067156-measure-value measure set)
      (q1067156-ennreal-finite
       (q1067156-zero real-type))))))

(defun q1067156-measure-space-p
    (real-type space measurable measure)
  (and
   (q1067156-sigma-algebra-p space measurable)
   (q1067156-measure-values-p real-type measure)
   (q1067156-measure-extensional-p space measure)
   (q1067156-empty-set-zero-p
    real-type space measure)
   (q1067156-measure-monotone-p
    real-type space measure)
   (q1067156-countable-subadditivity-p
    real-type space measure)
   (equal
    (q1067156-measure-value
     measure
     (q1067156-complement-set
      space (q1067156-full-set space)))
    (q1067156-ennreal-finite (q1067156-zero real-type)))
   (q1067156-countable-additivity-p
    real-type space measurable measure)))

(defun q1067156-unit-coordinates-p
    (real-type coordinates x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (let ((c
           (q1067156-coordinate
            coordinates x (- n 1))))
      (and
       (q1067156-leq
        real-type (q1067156-zero real-type) c)
       (q1067156-less
        real-type c (q1067156-one real-type))
       (q1067156-unit-coordinates-p
        real-type coordinates x (- n 1))))))

(defun-sk q1067156-unit-cell-coordinate-p
    (real-type space basis coordinates dimension)
  (forall (x)
    (iff
     (q1067156-set-member-p
      (q1067156-unit-cell-set
       space basis coordinates dimension)
      x)
     (and
      (q1067156-member-p space x)
      (q1067156-unit-coordinates-p
       real-type coordinates x dimension)))))

(defun-sk q1067156-translation-invariant-p
    (space measurable measure)
  (forall (set shift)
    (implies
     (and
      (q1067156-family-member-p measurable set)
      (q1067156-member-p space shift))
     (equal
      (q1067156-measure-value
       measure
       (q1067156-translate-set space set shift))
      (q1067156-measure-value measure set)))))

(defun q1067156-volume-space-p
    (real-type space basis coordinates dimension measurable measure)
  (and
   (q1067156-borel-space-p real-type space measurable)
   (q1067156-measure-space-p
    real-type space measurable measure)
   (q1067156-unit-cell-coordinate-p
    real-type space basis coordinates dimension)
   (q1067156-family-member-p
    measurable
    (q1067156-unit-cell-set
     space basis coordinates dimension))
   (equal
    (q1067156-measure-value
     measure
     (q1067156-unit-cell-set
      space basis coordinates dimension))
    (q1067156-ennreal-finite
     (q1067156-one real-type)))
   (q1067156-translation-invariant-p
    space measurable measure)))

;; Lebesgue lower integration and Bochner integration.

(defun-sk q1067156-function-into-p
    (domain codomain function)
  (forall (x)
    (implies
     (q1067156-member-p domain x)
     (q1067156-member-p
      codomain
      (q1067156-function-at function x)))))

(defun-sk q1067156-continuous-at-delta-p
    (real-type domain codomain function x epsilon delta)
  (forall (y)
    (implies
     (and
      (q1067156-member-p domain y)
      (q1067156-less
       real-type
       (q1067156-distance real-type domain y x)
       delta))
     (q1067156-less
      real-type
      (q1067156-distance
       real-type codomain
       (q1067156-function-at function y)
       (q1067156-function-at function x))
      epsilon))))

(defun-sk q1067156-continuous-at-epsilon-p
    (real-type domain codomain function x epsilon)
  (exists (delta)
    (and
     (q1067156-member-p real-type delta)
     (q1067156-positive-p real-type delta)
     (q1067156-continuous-at-delta-p
      real-type domain codomain function x epsilon delta))))

(defun-sk q1067156-continuous-function-p
    (real-type domain codomain function)
  (forall (x epsilon)
    (implies
     (and
      (q1067156-member-p domain x)
      (q1067156-member-p real-type epsilon)
      (q1067156-positive-p real-type epsilon))
     (q1067156-continuous-at-epsilon-p
      real-type domain codomain function x epsilon))))

(defun-sk q1067156-function-constructor-laws-p
    (real-type)
  (forall (type f g set value x)
    (and
     (equal
      (q1067156-function-at
       (q1067156-function-add type f g) x)
      (q1067156-add
       type
       (q1067156-function-at f x)
       (q1067156-function-at g x)))
     (equal
      (q1067156-function-at
       (q1067156-function-difference type f g) x)
      (q1067156-add
       type
       (q1067156-function-at f x)
       (q1067156-negate
        type (q1067156-function-at g x))))
     (equal
      (q1067156-function-at
       (q1067156-function-norm real-type type f) x)
      (q1067156-norm type (q1067156-function-at f x)))
     (equal
      (q1067156-function-at
       (q1067156-indicator-function real-type set) x)
      (if (q1067156-set-member-p set x)
          (q1067156-one real-type)
        (q1067156-zero real-type))))))

(defun-sk q1067156-fiber-set-law-p (domain)
  (forall (function value x)
    (iff
     (q1067156-set-member-p
      (q1067156-fiber-set function value)
      x)
     (and
      (q1067156-member-p domain x)
      (equal (q1067156-function-at function x) value)))))

(defun-sk q1067156-measurable-function-p
    (real-type domain measurable codomain function)
  (forall (center radius)
    (implies
     (and
      (q1067156-member-p codomain center)
      (q1067156-member-p real-type radius)
      (q1067156-positive-p real-type radius))
     (q1067156-family-member-p
      measurable
      (q1067156-preimage-set
       function
       (q1067156-open-ball-set
        codomain center radius))))))

(defun-sk q1067156-nonnegative-values-p
    (real-type domain function)
  (forall (x)
    (implies
     (q1067156-member-p domain x)
     (q1067156-leq
      real-type
      (q1067156-zero real-type)
      (q1067156-function-at function x)))))

(defun q1067156-nonnegative-measurable-p
    (real-type domain measurable function)
  (and
   (q1067156-function-into-p
    domain real-type function)
   (q1067156-measurable-function-p
    real-type domain measurable real-type function)
   (q1067156-nonnegative-values-p
    real-type domain function)))

(defun-sk q1067156-pointwise-leq-p
    (real-type domain left right)
  (forall (x)
    (implies
     (q1067156-member-p domain x)
     (q1067156-leq
      real-type
      (q1067156-function-at left x)
      (q1067156-function-at right x)))))

(defun-sk q1067156-functions-equal-on-p
    (domain left right)
  (forall (x)
    (implies
     (q1067156-member-p domain x)
     (equal
      (q1067156-function-at left x)
      (q1067156-function-at right x)))))

(defun-sk q1067156-lintegral-laws-p
    (real-type domain measurable measure lintegral)
  (forall (f g set)
    (and
     (implies
      (q1067156-functions-equal-on-p domain f g)
      (equal
       (q1067156-lintegral-value lintegral f)
       (q1067156-lintegral-value lintegral g)))
     (implies
      (q1067156-nonnegative-measurable-p
       real-type domain measurable f)
      (q1067156-ennreal-p
       real-type
       (q1067156-lintegral-value lintegral f)))
     (implies
      (and
       (q1067156-nonnegative-measurable-p
        real-type domain measurable f)
       (q1067156-nonnegative-measurable-p
        real-type domain measurable g)
       (q1067156-pointwise-leq-p real-type domain f g))
      (q1067156-ennreal-leq-p
       real-type
       (q1067156-lintegral-value lintegral f)
       (q1067156-lintegral-value lintegral g)))
     (implies
      (q1067156-family-member-p measurable set)
      (equal
       (q1067156-lintegral-value
        lintegral
        (q1067156-indicator-function real-type set))
       (q1067156-measure-value measure set)))
     (implies
      (and
       (q1067156-nonnegative-measurable-p
        real-type domain measurable f)
       (q1067156-nonnegative-measurable-p
        real-type domain measurable g))
      (equal
       (q1067156-lintegral-value
        lintegral
        (q1067156-function-add real-type f g))
       (q1067156-ennreal-add
        real-type
        (q1067156-lintegral-value lintegral f)
        (q1067156-lintegral-value lintegral g)))))))

(defun q1067156-simple-values-correct-p
    (domain measurable function values)
  (if (consp values)
      (and
       (q1067156-family-member-p
        measurable
        (q1067156-fiber-set function (car values)))
       (q1067156-simple-values-correct-p
        domain measurable function (cdr values)))
    (equal values nil)))

(defun q1067156-simple-listed-values-in-space-p
    (space values)
  (if (consp values)
      (and
       (q1067156-member-p space (car values))
       (q1067156-simple-listed-values-in-space-p
        space (cdr values)))
    (equal values nil)))

(defun-sk q1067156-simple-range-values-p
    (domain function values)
  (forall (x)
    (implies
     (q1067156-member-p domain x)
     (member-equal
      (q1067156-function-at function x)
      values))))

(defun-sk q1067156-value-attained-p
    (domain function value)
  (exists (x)
    (and
     (q1067156-member-p domain x)
     (equal
      (q1067156-function-at function x)
      value))))

(defun q1067156-simple-function-p
    (domain measurable space function)
  (and
   (q1067156-function-into-p domain space function)
   (true-listp (q1067156-simple-values function))
   (no-duplicatesp-equal (q1067156-simple-values function))
   (q1067156-simple-listed-values-in-space-p
    space (q1067156-simple-values function))
   (q1067156-simple-values-correct-p
    domain measurable function
    (q1067156-simple-values function))
   (q1067156-simple-range-values-p
    domain function
    (q1067156-simple-values function))))

(defun q1067156-simple-integrable-values-p
    (real-type domain measure zero function values)
  (if (consp values)
      (and
       (implies
        (not
         (q1067156-value-attained-p
          domain function (car values)))
        (equal
         (q1067156-measure-value
          measure
          (q1067156-fiber-set function (car values)))
         (q1067156-ennreal-finite
          (q1067156-zero real-type))))
       (or
        (equal (car values) zero)
        (not
         (equal
          (q1067156-measure-value
           measure
           (q1067156-fiber-set function (car values)))
          :q1067156-top)))
       (q1067156-simple-integrable-values-p
        real-type domain measure zero function (cdr values)))
    (equal values nil)))

(defun q1067156-simple-integral
    (real-type domain space measure function values)
  (if (consp values)
      (q1067156-add
       space
       (if (or
            (equal (car values) (q1067156-zero space))
            (not
             (q1067156-value-attained-p
              domain function (car values))))
           (q1067156-zero space)
         (q1067156-smul
          real-type space
          (cdr
           (q1067156-measure-value
            measure
            (q1067156-fiber-set function (car values))))
          (car values)))
       (q1067156-simple-integral
        real-type domain space measure function (cdr values)))
    (q1067156-zero space)))

(defun q1067156-ennreal-scale
    (real-type scalar value)
  (if (equal scalar (q1067156-zero real-type))
      (q1067156-ennreal-finite
       (q1067156-zero real-type))
    (if (equal value :q1067156-top)
        :q1067156-top
      (q1067156-ennreal-finite
       (q1067156-multiply
        real-type scalar (cdr value))))))

(defun q1067156-simple-nonnegative-integral
    (real-type domain measure function values)
  (if (consp values)
      (q1067156-ennreal-add
       real-type
       (if
           (q1067156-value-attained-p
            domain function (car values))
           (q1067156-ennreal-scale
            real-type
            (car values)
            (q1067156-measure-value
             measure
             (q1067156-fiber-set function (car values))))
         (q1067156-ennreal-finite
          (q1067156-zero real-type)))
       (q1067156-simple-nonnegative-integral
        real-type domain measure function (cdr values)))
    (q1067156-ennreal-finite
     (q1067156-zero real-type))))

(defun-sk q1067156-lintegral-upper-bound-p
    (real-type domain measurable measure function bound)
  (forall (simple)
    (implies
     (and
      (q1067156-simple-function-p
       domain measurable real-type simple)
      (q1067156-nonnegative-values-p
       real-type domain simple)
      (q1067156-pointwise-leq-p
       real-type domain simple function))
     (q1067156-ennreal-leq-p
      real-type
      (q1067156-simple-nonnegative-integral
       real-type domain measure simple
       (q1067156-simple-values simple))
      bound))))

(defun-sk q1067156-lintegral-least-upper-bound-p
    (real-type domain measurable measure function value)
  (forall (bound)
    (implies
     (and
      (q1067156-ennreal-p real-type bound)
      (q1067156-lintegral-upper-bound-p
       real-type domain measurable measure function bound))
     (q1067156-ennreal-leq-p real-type value bound))))

(defun-sk q1067156-lintegral-supremum-laws-p
    (real-type domain measurable measure lintegral)
  (forall (function)
    (implies
     (and
      (q1067156-function-into-p
       domain real-type function)
      (q1067156-nonnegative-values-p
       real-type domain function))
     (let ((value
            (q1067156-lintegral-value
             lintegral function)))
       (and
        (q1067156-ennreal-p real-type value)
        (q1067156-lintegral-upper-bound-p
         real-type domain measurable measure function value)
        (q1067156-lintegral-least-upper-bound-p
         real-type domain measurable measure function value))))))

(defun-sk q1067156-simple-sequence-p
    (domain measurable space sequence)
  (forall (n)
    (implies
     (natp n)
     (q1067156-simple-function-p
      domain measurable space
      (q1067156-sequence-at sequence n)))))

(defun-sk q1067156-pointwise-simple-limit-p
    (real-type domain space sequence function)
  (forall (x)
    (implies
     (q1067156-member-p domain x)
     (q1067156-converges-p
      real-type
      space
      (q1067156-point-sequence sequence x)
      (q1067156-function-at function x)))))

(defun-sk q1067156-point-sequence-laws-p ()
  (forall (sequence x n)
    (equal
     (q1067156-sequence-at
      (q1067156-point-sequence sequence x) n)
     (q1067156-function-at
      (q1067156-sequence-at sequence n) x))))

(defun-sk q1067156-strongly-measurable-p
    (real-type domain measurable space function)
  (exists (sequence)
    (and
     (q1067156-simple-sequence-p
      domain measurable space sequence)
     (q1067156-pointwise-simple-limit-p
      real-type domain space sequence function))))

(defun q1067156-integrable-p
    (real-type domain measurable lintegral space function)
  (and
   (q1067156-strongly-measurable-p
    real-type domain measurable space function)
   (not
    (equal
     (q1067156-lintegral-value
      lintegral
      (q1067156-function-norm real-type space function))
     :q1067156-top))))

(defun q1067156-l1-distance
    (real-type space lintegral left right)
  (q1067156-lintegral-value
   lintegral
   (q1067156-function-norm
    real-type space
    (q1067156-function-difference space left right))))

(defun-sk q1067156-l1-tail-p
    (real-type space lintegral sequence function epsilon start)
  (forall (n)
    (implies
     (and (natp n) (natp start) (<= start n))
     (q1067156-ennreal-leq-p
      real-type
      (q1067156-l1-distance
       real-type space lintegral
       (q1067156-sequence-at sequence n)
       function)
      (q1067156-ennreal-finite epsilon)))))

(defun-sk q1067156-l1-start-p
    (real-type space lintegral sequence function epsilon)
  (exists (start)
    (and
     (natp start)
     (q1067156-l1-tail-p
      real-type space lintegral
      sequence function epsilon start))))

(defun-sk q1067156-l1-converges-p
    (real-type space lintegral sequence function)
  (forall (epsilon)
    (implies
     (and
      (q1067156-member-p real-type epsilon)
      (q1067156-positive-p real-type epsilon))
     (q1067156-l1-start-p
      real-type space lintegral sequence function epsilon))))

(defun-sk q1067156-integrable-simple-sequence-p
    (real-type domain measurable measure space sequence)
  (forall (n)
    (implies
     (natp n)
     (let ((f (q1067156-sequence-at sequence n)))
       (and
        (q1067156-simple-function-p
         domain measurable space f)
        (q1067156-simple-integrable-values-p
         real-type domain measure
         (q1067156-zero space) f
         (q1067156-simple-values f)))))))

(defun-sk q1067156-simple-integral-sequence-laws-p ()
  (forall (real-type domain space measure sequence n)
    (equal
     (q1067156-sequence-at
      (q1067156-simple-integral-sequence
       real-type domain space measure sequence)
      n)
     (q1067156-simple-integral
      real-type domain space measure
      (q1067156-sequence-at sequence n)
      (q1067156-simple-values
       (q1067156-sequence-at sequence n))))))

(defun q1067156-bochner-approximation-p
    (real-type domain measurable measure lintegral
     space function value sequence)
  (and
   (q1067156-integrable-simple-sequence-p
    real-type domain measurable measure space sequence)
   (q1067156-l1-converges-p
    real-type space lintegral sequence function)
   (q1067156-converges-p
    real-type space
    (q1067156-simple-integral-sequence
     real-type domain space measure sequence)
    value)))

(defun-sk q1067156-bochner-approximation-exists-p
    (real-type domain measurable measure lintegral
     space function value)
  (exists (sequence)
    (q1067156-bochner-approximation-p
     real-type domain measurable measure lintegral
     space function value sequence)))

(defun-sk q1067156-bochner-integral-operation-p
    (real-type domain measurable measure lintegral space integral)
  (forall (function other)
    (and
     (implies
      (q1067156-functions-equal-on-p
       domain function other)
      (equal
       (q1067156-bochner-integral-value
        integral function)
       (q1067156-bochner-integral-value
        integral other)))
     (implies
      (q1067156-function-into-p domain space function)
      (let ((value
             (q1067156-bochner-integral-value
              integral function)))
        (and
         (q1067156-member-p space value)
         (if
             (and
              (q1067156-complete-p real-type space)
              (q1067156-integrable-p
               real-type domain measurable lintegral
               space function))
             (q1067156-bochner-approximation-exists-p
              real-type domain measurable measure lintegral
              space function value)
           (equal value (q1067156-zero space)))))))))

;; Schwartz maps and the normalized Fourier fourier-char.

(defun q1067156-directional-difference-quotient
    (real-type domain codomain basis function x i h)
  (q1067156-smul
   real-type codomain
   (q1067156-inverse real-type h)
   (q1067156-add
    codomain
    (q1067156-function-at
     function
     (q1067156-add
      domain x
      (q1067156-smul
       real-type domain h
       (q1067156-basis-at basis i))))
    (q1067156-negate
     codomain
     (q1067156-function-at function x)))))

(defun-sk q1067156-derivative-delta-p
    (real-type domain codomain basis
     function derivative x i epsilon delta)
  (forall (h)
    (implies
     (and
      (q1067156-member-p real-type h)
      (q1067156-positive-p
       real-type (q1067156-abs real-type h))
      (q1067156-less
       real-type (q1067156-abs real-type h) delta))
     (q1067156-less
      real-type
      (q1067156-distance
       real-type codomain
       (q1067156-directional-difference-quotient
        real-type domain codomain basis function x i h)
       (q1067156-function-at derivative x))
      epsilon))))

(defun-sk q1067156-derivative-epsilon-p
    (real-type domain codomain basis
     function derivative x i epsilon)
  (exists (delta)
    (and
     (q1067156-member-p real-type delta)
     (q1067156-positive-p real-type delta)
     (q1067156-derivative-delta-p
      real-type domain codomain basis
      function derivative x i epsilon delta))))

(defun-sk q1067156-directional-derivative-p
    (real-type domain codomain basis
     function derivative i)
  (forall (x epsilon)
    (implies
     (and
      (q1067156-member-p domain x)
      (q1067156-member-p real-type epsilon)
      (q1067156-positive-p real-type epsilon))
     (q1067156-derivative-epsilon-p
      real-type domain codomain basis
      function derivative x i epsilon))))

(defun-sk q1067156-derivative-family-p
    (real-type domain codomain basis dimension derivatives function)
  (forall (alpha i)
    (implies
     (and
      (q1067156-natural-list-p alpha dimension)
      (natp i)
      (< i dimension))
     (and
      (q1067156-function-into-p
       domain codomain
       (q1067156-derivative-function
        derivatives function alpha))
      (q1067156-directional-derivative-p
       real-type domain codomain basis
       (q1067156-derivative-function
        derivatives function alpha)
       (q1067156-derivative-function
        derivatives function
        (q1067156-increment-multiindex alpha i))
       i)))))

(defun-sk q1067156-derivative-functions-continuous-p
    (real-type domain codomain dimension derivatives function)
  (forall (alpha)
    (implies
     (q1067156-natural-list-p alpha dimension)
     (let ((derivative
            (q1067156-derivative-function
             derivatives function alpha)))
       (and
        (q1067156-function-into-p
         domain codomain derivative)
        (q1067156-continuous-function-p
         real-type domain codomain derivative))))))

(defun-sk q1067156-decay-bound-p
    (real-type domain codomain derivatives function alpha k bound)
  (forall (x)
    (implies
     (q1067156-member-p domain x)
     (q1067156-leq
      real-type
      (q1067156-multiply
       real-type
       (q1067156-real-power
        real-type
        (q1067156-add
         real-type
         (q1067156-one real-type)
         (q1067156-norm domain x))
        k)
       (q1067156-norm
        codomain
        (q1067156-function-at
         (q1067156-derivative-function
          derivatives function alpha)
         x)))
      bound))))

(defun-sk q1067156-decay-bound-exists-p
    (real-type domain codomain derivatives function alpha k)
  (exists (bound)
    (and
     (q1067156-member-p real-type bound)
     (q1067156-leq
      real-type (q1067156-zero real-type) bound)
     (q1067156-decay-bound-p
      real-type domain codomain derivatives
      function alpha k bound))))

(defun-sk q1067156-rapid-decay-p
    (real-type domain codomain dimension derivatives function)
  (forall (alpha k)
    (implies
     (and
      (q1067156-natural-list-p alpha dimension)
      (natp k))
     (q1067156-decay-bound-exists-p
      real-type domain codomain derivatives
      function alpha k))))

(defun q1067156-schwartz-map-p
    (real-type domain codomain basis dimension derivatives function)
  (and
   (q1067156-function-into-p domain codomain function)
   (equal
    (q1067156-derivative-function
     derivatives function
     (q1067156-zero-multiindex dimension))
    function)
   (q1067156-derivative-family-p
    real-type domain codomain basis dimension
    derivatives function)
   (q1067156-derivative-functions-continuous-p
    real-type domain codomain dimension
    derivatives function)
   (q1067156-rapid-decay-p
    real-type domain codomain dimension
    derivatives function)))

(defun-sk q1067156-character-kernel-witness-p
    (real-type complex-type fourier-char x)
  (exists (n)
    (and
     (integerp n)
     (equal x (q1067156-integer-cast real-type n)))))

(defun-sk q1067156-character-laws-p
    (real-type complex-type fourier-char)
  (forall (x y)
    (implies
     (and
      (q1067156-member-p real-type x)
      (q1067156-member-p real-type y))
     (and
      (q1067156-member-p
       complex-type
       (q1067156-character-value fourier-char x))
      (equal
       (q1067156-character-value
        fourier-char (q1067156-add real-type x y))
       (q1067156-multiply
        complex-type
        (q1067156-character-value fourier-char x)
        (q1067156-character-value fourier-char y)))
      (equal
       (q1067156-norm
        complex-type
        (q1067156-character-value fourier-char x))
       (q1067156-one real-type))
      (iff
       (equal
        (q1067156-character-value fourier-char x)
        (q1067156-one complex-type))
       (q1067156-character-kernel-witness-p
        real-type complex-type fourier-char x))))))

(defun-sk q1067156-character-orientation-delta-p
    (real-type complex-type fourier-char delta)
  (forall (x)
    (implies
     (and
      (q1067156-member-p real-type x)
      (q1067156-positive-p real-type x)
      (q1067156-less real-type x delta))
     (q1067156-less
      real-type
      (q1067156-zero real-type)
      (q1067156-imag-part
       real-type complex-type
       (q1067156-character-value fourier-char x))))))

(defun-sk q1067156-character-orientation-p
    (real-type complex-type fourier-char)
  (exists (delta)
    (and
     (q1067156-member-p real-type delta)
     (q1067156-positive-p real-type delta)
     (q1067156-character-orientation-delta-p
      real-type complex-type fourier-char delta))))

(defun-sk q1067156-character-continuity-delta-p
    (real-type complex-type fourier-char epsilon delta)
  (forall (x)
    (implies
     (and
      (q1067156-member-p real-type x)
      (q1067156-less
       real-type
       (q1067156-abs real-type x)
       delta))
     (q1067156-less
      real-type
      (q1067156-distance
       real-type complex-type
       (q1067156-character-value fourier-char x)
       (q1067156-one complex-type))
      epsilon))))

(defun-sk q1067156-character-continuity-epsilon-p
    (real-type complex-type fourier-char epsilon)
  (exists (delta)
    (and
     (q1067156-member-p real-type delta)
     (q1067156-positive-p real-type delta)
     (q1067156-character-continuity-delta-p
      real-type complex-type fourier-char epsilon delta))))

(defun-sk q1067156-character-continuity-p
    (real-type complex-type fourier-char)
  (forall (epsilon)
    (implies
     (and
      (q1067156-member-p real-type epsilon)
      (q1067156-positive-p real-type epsilon))
     (q1067156-character-continuity-epsilon-p
      real-type complex-type fourier-char epsilon))))

(defun q1067156-fourier-character-p
    (real-type complex-type fourier-char)
  (and
   (equal
    (q1067156-character-value
     fourier-char (q1067156-zero real-type))
    (q1067156-one complex-type))
   (q1067156-character-laws-p
    real-type complex-type fourier-char)
   (q1067156-character-continuity-p
    real-type complex-type fourier-char)
   (q1067156-character-orientation-p
    real-type complex-type fourier-char)))

(defun-sk q1067156-inner-integrand-laws-p
    (complex-type space)
  (forall (f g x)
    (equal
     (q1067156-function-at
      (q1067156-inner-integrand
       complex-type space f g)
      x)
     (q1067156-inner
      complex-type space
      (q1067156-function-at f x)
      (q1067156-function-at g x)))))

(defun-sk q1067156-fourier-integrand-laws-p
    (real-type complex-type domain space fourier-char)
  (forall (f frequency x)
    (equal
     (q1067156-function-at
      (q1067156-fourier-integrand
       real-type complex-type domain space
       fourier-char f frequency)
      x)
     (q1067156-smul
      complex-type space
      (q1067156-character-value
       fourier-char
       (q1067156-negate
        real-type
        (q1067156-inner
         real-type domain x frequency)))
      (q1067156-function-at f x)))))

(defun-sk q1067156-fourier-transform-correct-p
    (real-type complex-type domain space
     fourier-char integral fourier function)
  (forall (frequency)
    (implies
     (q1067156-member-p domain frequency)
     (equal
      (q1067156-function-at
       (q1067156-fourier-function fourier function)
       frequency)
      (q1067156-bochner-integral-value
       integral
       (q1067156-fourier-integrand
        real-type complex-type domain space
        fourier-char function frequency))))))

;; The source domain is an arbitrary measurable space, so only the set
;; constructors needed for a sigma algebra are required on it.

(defun q1067156-basic-set-constructor-laws-p (domain)
  (and
   (q1067156-full-set-law-p domain)
   (q1067156-complement-set-law-p domain)
   (q1067156-countable-union-set-law-p domain)))

;; A real normed vector space need not be complete. This distinction is
;; semantically relevant because mathlib defines its Bochner integral to be
;; zero when the codomain is incomplete.

(defun q1067156-real-normed-space-p (real-type space)
  (and
   (q1067156-member-p space (q1067156-zero space))
   (q1067156-vector-space-laws-p real-type space)
   (q1067156-norm-laws-p real-type space)
   (q1067156-normed-space-laws-p real-type real-type space)))

;; Almost-everywhere predicates use a null exceptional set. Measurability of
;; that set is intentionally not required: Lean's almost-everywhere filter is
;; defined by the measure-zero condition on the failure set itself.

(defun q1067156-null-set-p
    (real-type domain measure set)
  (and
   (q1067156-valid-set-p domain set)
   (equal
    (q1067156-measure-value measure set)
    (q1067156-ennreal-finite
     (q1067156-zero real-type)))))

(defun-sk q1067156-equal-off-set-p
    (domain left right exceptional)
  (forall (x)
    (implies
     (and
      (q1067156-member-p domain x)
      (not (q1067156-set-member-p exceptional x)))
     (equal
      (q1067156-function-at left x)
      (q1067156-function-at right x)))))

(defun q1067156-ae-equal-witness-p
    (real-type domain measurable measure left right exceptional)
  (declare (ignore measurable))
  (and
   (q1067156-null-set-p
    real-type domain measure exceptional)
   (q1067156-equal-off-set-p
    domain left right exceptional)))

(defun-sk q1067156-ae-equal-p
    (real-type domain measurable measure left right)
  (exists (exceptional)
    (q1067156-ae-equal-witness-p
     real-type domain measurable measure
     left right exceptional)))

(defun q1067156-ae-strongly-measurable-witness-p
    (real-type domain measurable measure
     space function representative)
  (and
   (q1067156-function-into-p
    domain space representative)
   (q1067156-strongly-measurable-p
    real-type domain measurable space representative)
   (q1067156-ae-equal-p
    real-type domain measurable measure
    function representative)))

(defun-sk q1067156-ae-strongly-measurable-p
    (real-type domain measurable measure space function)
  (exists (representative)
    (q1067156-ae-strongly-measurable-witness-p
     real-type domain measurable measure
     space function representative)))

(defun q1067156-ae-integrable-p
    (real-type domain measurable measure
     lintegral space function)
  (and
   (q1067156-function-into-p domain space function)
   (q1067156-ae-strongly-measurable-p
    real-type domain measurable measure space function)
   (not
    (equal
     (q1067156-lintegral-value
      lintegral
      (q1067156-function-norm
       real-type space function))
     :q1067156-top))))

;; Every term of F is an alpha-to-G function and is almost-everywhere
;; strongly measurable.

(defun-sk q1067156-function-sequence-into-p
    (domain space sequence)
  (forall (n)
    (implies
     (natp n)
     (q1067156-function-into-p
      domain space
      (q1067156-sequence-at sequence n)))))

(defun-sk q1067156-sequence-ae-strongly-measurable-p
    (real-type domain measurable measure space sequence)
  (forall (n)
    (implies
     (natp n)
     (q1067156-ae-strongly-measurable-p
      real-type domain measurable measure space
      (q1067156-sequence-at sequence n)))))

;; The domination hypothesis has a separately quantified null exceptional set
;; for each natural-number index, exactly as in forall n, almost everywhere x.

(defun-sk q1067156-dominated-off-set-p
    (real-type domain space sequence bound n exceptional)
  (forall (x)
    (implies
     (and
      (q1067156-member-p domain x)
      (not (q1067156-set-member-p exceptional x)))
     (q1067156-leq
      real-type
      (q1067156-norm
       space
       (q1067156-function-at
        (q1067156-sequence-at sequence n) x))
      (q1067156-function-at bound x)))))

(defun q1067156-dominated-index-witness-p
    (real-type domain measurable measure
     space sequence bound n exceptional)
  (declare (ignore measurable))
  (and
   (q1067156-null-set-p
    real-type domain measure exceptional)
   (q1067156-dominated-off-set-p
    real-type domain space sequence bound n exceptional)))

(defun-sk q1067156-dominated-at-index-p
    (real-type domain measurable measure
     space sequence bound n)
  (exists (exceptional)
    (q1067156-dominated-index-witness-p
     real-type domain measurable measure
     space sequence bound n exceptional)))

(defun-sk q1067156-sequence-dominated-p
    (real-type domain measurable measure
     space sequence bound)
  (forall (n)
    (implies
     (natp n)
     (q1067156-dominated-at-index-p
      real-type domain measurable measure
      space sequence bound n))))

;; Pointwise convergence is asserted outside one measurable null set.

(defun-sk q1067156-pointwise-converges-off-set-p
    (real-type domain space sequence limit exceptional)
  (forall (x)
    (implies
     (and
      (q1067156-member-p domain x)
      (not (q1067156-set-member-p exceptional x)))
     (q1067156-converges-p
      real-type space
      (q1067156-point-sequence sequence x)
      (q1067156-function-at limit x)))))

(defun q1067156-ae-pointwise-convergence-witness-p
    (real-type domain measurable measure
     space sequence limit exceptional)
  (declare (ignore measurable))
  (and
   (q1067156-null-set-p
    real-type domain measure exceptional)
   (q1067156-pointwise-converges-off-set-p
    real-type domain space sequence limit exceptional)))

(defun-sk q1067156-ae-pointwise-converges-p
    (real-type domain measurable measure
     space sequence limit)
  (exists (exceptional)
    (q1067156-ae-pointwise-convergence-witness-p
     real-type domain measurable measure
     space sequence limit exceptional)))

;; Both lower integration and Bochner integration are invariant under
;; almost-everywhere equality. The Bochner operation uses the same simple
;; function/L1 characterization as above, and returns zero for incomplete
;; codomains or nonintegrable functions, matching mathlib's total integral.

(defun-sk q1067156-lintegral-ae-congruence-p
    (real-type domain measurable measure lintegral)
  (forall (left right)
    (implies
     (q1067156-ae-equal-p
      real-type domain measurable measure left right)
     (equal
      (q1067156-lintegral-value lintegral left)
      (q1067156-lintegral-value lintegral right)))))

(defun-sk q1067156-bochner-integral-ae-operation-p
    (real-type domain measurable measure
     lintegral space integral)
  (forall (function other)
    (and
     (implies
      (q1067156-ae-equal-p
       real-type domain measurable measure function other)
      (equal
       (q1067156-bochner-integral-value integral function)
       (q1067156-bochner-integral-value integral other)))
     (implies
      (q1067156-function-into-p domain space function)
      (let ((value
             (q1067156-bochner-integral-value
              integral function)))
        (and
         (q1067156-member-p space value)
         (if
             (and
              (q1067156-complete-p real-type space)
              (q1067156-ae-integrable-p
               real-type domain measurable measure
               lintegral space function))
             (q1067156-bochner-approximation-exists-p
              real-type domain measurable measure lintegral
              space function value)
           (equal value (q1067156-zero space)))))))))

(defstub q1067156-integral-sequence
  (integral function-sequence) t)

(defun-sk q1067156-integral-sequence-laws-p ()
  (forall (integral function-sequence n)
    (equal
     (q1067156-sequence-at
      (q1067156-integral-sequence
       integral function-sequence)
      n)
     (q1067156-bochner-integral-value
      integral
      (q1067156-sequence-at function-sequence n)))))

;; This predicate is exactly the indexed Lean theorem
;; MeasureTheory.tendsto_integral_of_dominated_convergence.

(defun thousand-theorems-q1067156-dominated-convergence-theorem-statement
    (real-type domain space measurable measure lintegral
     integral sequence limit bound)
  (implies
   (and
    (q1067156-real-field-p real-type)
    (q1067156-real-normed-space-p real-type space)
    (q1067156-basic-set-constructor-laws-p domain)
    (q1067156-set-constructor-laws-p real-type real-type)
    (q1067156-fiber-set-law-p domain)
    (q1067156-preimage-set-law-p domain)
    (q1067156-function-constructor-laws-p real-type)
    (q1067156-point-sequence-laws-p)
    (q1067156-simple-integral-sequence-laws-p)
    (q1067156-integral-sequence-laws-p)
    (q1067156-measure-space-p
     real-type domain measurable measure)
    (q1067156-lintegral-laws-p
     real-type domain measurable measure lintegral)
    (q1067156-lintegral-supremum-laws-p
     real-type domain measurable measure lintegral)
    (q1067156-lintegral-ae-congruence-p
     real-type domain measurable measure lintegral)
    (q1067156-bochner-integral-ae-operation-p
     real-type domain measurable measure
     lintegral space integral)
    (q1067156-function-sequence-into-p
     domain space sequence)
    (q1067156-function-into-p domain space limit)
    (q1067156-function-into-p domain real-type bound)
    (q1067156-sequence-ae-strongly-measurable-p
     real-type domain measurable measure space sequence)
    (q1067156-ae-integrable-p
     real-type domain measurable measure
     lintegral real-type bound)
    (q1067156-sequence-dominated-p
     real-type domain measurable measure
     space sequence bound)
    (q1067156-ae-pointwise-converges-p
     real-type domain measurable measure
     space sequence limit))
   (q1067156-converges-p
    real-type space
    (q1067156-integral-sequence integral sequence)
    (q1067156-bochner-integral-value integral limit))))

(value-triple :itpeval-statement-checked)
:q
