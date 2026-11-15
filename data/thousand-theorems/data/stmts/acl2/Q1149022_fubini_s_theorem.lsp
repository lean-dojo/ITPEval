;; Statement-only formalization of thousand-theorems corpus artifact Q1149022,
;; "Fubini's theorem": for an integrable function from the product of two
;; arbitrary s-finite measure spaces into an arbitrary real normed vector
;; space, the Bochner integral over the product measure equals the iterated
;; Bochner integral. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Mathematical objects are unrestricted ACL2 objects. The conservative
;; interfaces below only provide application and constructor symbols; every
;; real-field, normed-space, measure, measurability, convergence, and Bochner
;; integration law used by the statement is imposed explicitly by predicates.

(defstub q1149022-member-p (type object) t)
(defstub q1149022-zero (type) t)
(defstub q1149022-one (type) t)
(defstub q1149022-add (type left right) t)
(defstub q1149022-multiply (type left right) t)
(defstub q1149022-negate (type object) t)
(defstub q1149022-inverse (type object) t)
(defstub q1149022-less (type left right) t)
(defstub q1149022-norm (type object) t)
(defstub q1149022-smul (scalar-type space scalar vector) t)
(defstub q1149022-star (scalar-type scalar) t)
(defstub q1149022-real-part (real-type scalar-type scalar) t)
(defstub q1149022-imag-part (real-type scalar-type scalar) t)
(defstub q1149022-of-real (real-type scalar-type real) t)
(defstub q1149022-imaginary-unit (scalar-type) t)
(defstub q1149022-inner (scalar-type space left right) t)
(defstub q1149022-function-at (function argument) t)
(defstub q1149022-sequence-at (sequence index) t)
(defstub q1149022-basis-at (basis index) t)
(defstub q1149022-coordinate (coordinates vector index) t)
(defstub q1149022-derivative-function (derivatives function multiindex) t)
(defstub q1149022-fourier-function (fourier function) t)
(defstub q1149022-character-value (fourier-char real) t)
(defstub q1149022-set-member-p (set object) t)
(defstub q1149022-family-member-p (family set) t)
(defstub q1149022-open-ball-set (space center radius) t)
(defstub q1149022-preimage-set (function set) t)
(defstub q1149022-complement-set (carrier set) t)
(defstub q1149022-countable-union-set (carrier sequence) t)
(defstub q1149022-translate-set (space set shift) t)
(defstub q1149022-unit-cell-set (space basis coordinates dimension) t)
(defstub q1149022-fiber-set (function value) t)
(defstub q1149022-simple-values (function) t)
(defstub q1149022-indicator-function (real-type set) t)
(defstub q1149022-function-add (type left right) t)
(defstub q1149022-function-difference (type left right) t)
(defstub q1149022-function-norm (real-type type function) t)
(defstub q1149022-inner-integrand (scalar-type space left right) t)
(defstub q1149022-fourier-integrand
  (real-type scalar-type domain space fourier-char function frequency) t)
(defstub q1149022-measure-value (measure set) t)
(defstub q1149022-lintegral-value (lintegral function) t)
(defstub q1149022-ennreal-lintegral-value
  (lintegral function) t)
(defstub q1149022-bochner-integral-value (integral function) t)
(defstub q1149022-full-set (carrier) t)
(defstub q1149022-point-sequence (function-sequence point) t)
(defstub q1149022-simple-integral-sequence
  (real-type domain space measure function-sequence) t)

(defstub q1149022-pair (left-type right-type left right) t)
(defstub q1149022-rectangle-set
  (left-type right-type left-set right-set) t)
(defstub q1149022-section-set
  (left-type right-type set left) t)
(defstub q1149022-section-measure-function
  (left-type right-type right-measure set) t)
(defstub q1149022-section-right
  (left-type right-type function left) t)
(defstub q1149022-iterated-integral-function
  (left-type right-type integral function) t)

(defun q1149022-positive-p (real-type x)
  (q1149022-less real-type (q1149022-zero real-type) x))

(defun q1149022-leq (real-type x y)
  (not (q1149022-less real-type y x)))

(defun q1149022-abs (real-type x)
  (if (q1149022-less real-type x (q1149022-zero real-type))
      (q1149022-negate real-type x)
    x))

(defun q1149022-natural-cast (type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1149022-zero type)
    (q1149022-add
     type
     (q1149022-one type)
     (q1149022-natural-cast type (- n 1)))))

(defun q1149022-integer-cast (type n)
  (if (and (integerp n) (< n 0))
      (q1149022-negate
       type
       (q1149022-natural-cast type (- n)))
    (q1149022-natural-cast type (nfix n))))

(defun q1149022-real-power (real-type x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1149022-one real-type)
    (q1149022-multiply
     real-type x
     (q1149022-real-power real-type x (- n 1)))))

(defun q1149022-vector-sum
    (real-type space basis coordinates vector n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1149022-zero space)
    (let ((i (- n 1)))
      (q1149022-add
       space
       (q1149022-vector-sum
        real-type space basis coordinates vector i)
       (q1149022-smul
        real-type space
        (q1149022-coordinate coordinates vector i)
        (q1149022-basis-at basis i))))))

(defun q1149022-zero-multiindex (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (q1149022-zero-multiindex (- n 1)))))

(defun q1149022-natural-list-p (alpha n)
  (if (zp n)
      (equal alpha nil)
    (and
     (consp alpha)
     (natp (car alpha))
     (q1149022-natural-list-p (cdr alpha) (- n 1)))))

(defun q1149022-increment-multiindex (alpha i)
  (if (consp alpha)
      (if (zp i)
          (cons (+ 1 (nfix (car alpha))) (cdr alpha))
        (cons
         (car alpha)
         (q1149022-increment-multiindex (cdr alpha) (- i 1))))
    nil))

(defun q1149022-multiindex-degree (alpha)
  (if (consp alpha)
      (+ (nfix (car alpha))
         (q1149022-multiindex-degree (cdr alpha)))
    0))

;; Complete ordered real field and its canonical complexification.

(defun-sk q1149022-field-laws-p (type)
  (forall (x y z)
    (implies
     (and
      (q1149022-member-p type x)
      (q1149022-member-p type y)
      (q1149022-member-p type z))
     (and
      (q1149022-member-p type (q1149022-add type x y))
      (q1149022-member-p type (q1149022-multiply type x y))
      (q1149022-member-p type (q1149022-negate type x))
      (implies
       (not (equal x (q1149022-zero type)))
       (q1149022-member-p type (q1149022-inverse type x)))
      (equal
       (q1149022-add type (q1149022-add type x y) z)
       (q1149022-add type x (q1149022-add type y z)))
      (equal (q1149022-add type x y) (q1149022-add type y x))
      (equal (q1149022-add type x (q1149022-zero type)) x)
      (equal
       (q1149022-add type x (q1149022-negate type x))
       (q1149022-zero type))
      (equal
       (q1149022-multiply type (q1149022-multiply type x y) z)
       (q1149022-multiply type x (q1149022-multiply type y z)))
      (equal
       (q1149022-multiply type x y)
       (q1149022-multiply type y x))
      (equal (q1149022-multiply type x (q1149022-one type)) x)
      (implies
       (not (equal x (q1149022-zero type)))
       (equal
        (q1149022-multiply type x (q1149022-inverse type x))
        (q1149022-one type)))
      (equal
       (q1149022-multiply type x (q1149022-add type y z))
       (q1149022-add
        type
        (q1149022-multiply type x y)
        (q1149022-multiply type x z)))))))

(defun-sk q1149022-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q1149022-member-p real-type x)
      (q1149022-member-p real-type y)
      (q1149022-member-p real-type z))
     (and
      (not (q1149022-less real-type x x))
      (or
       (q1149022-less real-type x y)
       (equal x y)
       (q1149022-less real-type y x))
      (implies
       (and
        (q1149022-less real-type x y)
        (q1149022-less real-type y z))
       (q1149022-less real-type x z))
      (implies
       (q1149022-less real-type x y)
       (q1149022-less
        real-type
        (q1149022-add real-type x z)
        (q1149022-add real-type y z)))
      (implies
       (and
        (q1149022-positive-p real-type x)
        (q1149022-positive-p real-type y))
       (q1149022-positive-p
        real-type
        (q1149022-multiply real-type x y)))))))

(defun q1149022-distance
    (real-type type x y)
  (declare (ignore real-type))
  (q1149022-norm
   type
   (q1149022-add type x (q1149022-negate type y))))

(defun-sk q1149022-norm-values-p (real-type type)
  (forall (x)
    (implies
     (q1149022-member-p type x)
     (and
      (q1149022-member-p real-type (q1149022-norm type x))
      (q1149022-leq
       real-type
       (q1149022-zero real-type)
       (q1149022-norm type x))
      (iff
       (equal
        (q1149022-norm type x)
        (q1149022-zero real-type))
       (equal x (q1149022-zero type)))))))

(defun-sk q1149022-norm-triangle-p (real-type type)
  (forall (x y)
    (implies
     (and
      (q1149022-member-p type x)
      (q1149022-member-p type y))
     (q1149022-leq
      real-type
      (q1149022-norm type (q1149022-add type x y))
      (q1149022-add
       real-type
       (q1149022-norm type x)
       (q1149022-norm type y))))))

(defun q1149022-norm-laws-p (real-type type)
  (and
   (q1149022-norm-values-p real-type type)
   (q1149022-norm-triangle-p real-type type)))

(defun-sk q1149022-convergence-tail-p
    (real-type type sequence limit epsilon start)
  (forall (n)
    (implies
     (and (natp n) (natp start) (<= start n))
     (q1149022-less
      real-type
      (q1149022-distance
       real-type type
       (q1149022-sequence-at sequence n)
       limit)
      epsilon))))

(defun-sk q1149022-convergence-start-p
    (real-type type sequence limit epsilon)
  (exists (start)
    (and
     (natp start)
     (q1149022-convergence-tail-p
      real-type type sequence limit epsilon start))))

(defun-sk q1149022-converges-p
    (real-type type sequence limit)
  (forall (epsilon)
    (implies
     (and
      (q1149022-member-p real-type epsilon)
      (q1149022-positive-p real-type epsilon))
     (q1149022-convergence-start-p
      real-type type sequence limit epsilon))))

(defun-sk q1149022-cauchy-tail-p
    (real-type type sequence epsilon start)
  (forall (m n)
    (implies
     (and
      (natp m) (natp n) (natp start)
      (<= start m) (<= start n))
     (q1149022-less
      real-type
      (q1149022-distance
       real-type type
       (q1149022-sequence-at sequence m)
       (q1149022-sequence-at sequence n))
      epsilon))))

(defun-sk q1149022-cauchy-start-p
    (real-type type sequence epsilon)
  (exists (start)
    (and
     (natp start)
     (q1149022-cauchy-tail-p
      real-type type sequence epsilon start))))

(defun-sk q1149022-cauchy-p (real-type type sequence)
  (forall (epsilon)
    (implies
     (and
      (q1149022-member-p real-type epsilon)
      (q1149022-positive-p real-type epsilon))
     (q1149022-cauchy-start-p
      real-type type sequence epsilon))))

(defun-sk q1149022-sequence-in-type-p (type sequence)
  (forall (n)
    (implies
     (natp n)
     (q1149022-member-p
      type
      (q1149022-sequence-at sequence n)))))

(defun-sk q1149022-limit-exists-p
    (real-type type sequence)
  (exists (limit)
    (and
     (q1149022-member-p type limit)
     (q1149022-converges-p
      real-type type sequence limit))))

(defun-sk q1149022-complete-p (real-type type)
  (forall (sequence)
    (implies
     (and
      (q1149022-sequence-in-type-p type sequence)
      (q1149022-cauchy-p real-type type sequence))
     (q1149022-limit-exists-p
      real-type type sequence))))

(defun-sk q1149022-archimedean-witness-p (real-type x)
  (exists (n)
    (and
     (natp n)
     (q1149022-less
      real-type x
      (q1149022-natural-cast real-type n)))))

(defun-sk q1149022-archimedean-p (real-type)
  (forall (x)
    (implies
     (q1149022-member-p real-type x)
     (q1149022-archimedean-witness-p real-type x))))

(defun-sk q1149022-real-norm-laws-p (real-type)
  (forall (x)
    (implies
     (q1149022-member-p real-type x)
     (and
      (equal
       (q1149022-norm real-type x)
       (q1149022-abs real-type x))
      (equal (q1149022-star real-type x) x)
      (equal
       (q1149022-real-part real-type real-type x)
       x)
      (equal
       (q1149022-imag-part real-type real-type x)
       (q1149022-zero real-type))
      (equal
       (q1149022-of-real real-type real-type x)
       x)))))

(defun q1149022-real-field-p (real-type)
  (and
   (q1149022-member-p real-type (q1149022-zero real-type))
   (q1149022-member-p real-type (q1149022-one real-type))
   (not
    (equal
     (q1149022-zero real-type)
     (q1149022-one real-type)))
   (q1149022-field-laws-p real-type)
   (q1149022-order-laws-p real-type)
   (q1149022-positive-p real-type (q1149022-one real-type))
   (q1149022-real-norm-laws-p real-type)
   (q1149022-complete-p real-type real-type)
   (q1149022-archimedean-p real-type)))

(defun-sk q1149022-complex-coordinate-laws-p
    (real-type complex-type)
  (forall (z)
    (implies
     (q1149022-member-p complex-type z)
     (let* ((re (q1149022-real-part real-type complex-type z))
            (im (q1149022-imag-part real-type complex-type z))
            (re-z (q1149022-of-real real-type complex-type re))
            (im-z
             (q1149022-multiply
              complex-type
              (q1149022-of-real real-type complex-type im)
              (q1149022-imaginary-unit complex-type))))
       (and
        (q1149022-member-p real-type re)
        (q1149022-member-p real-type im)
        (equal z (q1149022-add complex-type re-z im-z))
        (equal
         (q1149022-star complex-type z)
         (q1149022-add
          complex-type re-z
          (q1149022-negate complex-type im-z)))
        (equal
         (q1149022-multiply
          real-type
          (q1149022-norm complex-type z)
          (q1149022-norm complex-type z))
         (q1149022-add
          real-type
          (q1149022-multiply real-type re re)
          (q1149022-multiply real-type im im))))))))

(defun-sk q1149022-of-real-laws-p
    (real-type complex-type)
  (forall (x y)
    (implies
     (and
      (q1149022-member-p real-type x)
      (q1149022-member-p real-type y))
     (and
      (q1149022-member-p
       complex-type
       (q1149022-of-real real-type complex-type x))
      (equal
       (q1149022-real-part
        real-type complex-type
        (q1149022-of-real real-type complex-type x))
       x)
      (equal
       (q1149022-imag-part
        real-type complex-type
        (q1149022-of-real real-type complex-type x))
       (q1149022-zero real-type))
      (equal
       (q1149022-of-real
        real-type complex-type
        (q1149022-add real-type x y))
       (q1149022-add
        complex-type
        (q1149022-of-real real-type complex-type x)
        (q1149022-of-real real-type complex-type y)))
      (equal
       (q1149022-of-real
        real-type complex-type
        (q1149022-multiply real-type x y))
       (q1149022-multiply
        complex-type
        (q1149022-of-real real-type complex-type x)
        (q1149022-of-real real-type complex-type y)))))))

(defun q1149022-complex-field-p
    (real-type complex-type)
  (and
   (q1149022-real-field-p real-type)
   (q1149022-member-p complex-type (q1149022-zero complex-type))
   (q1149022-member-p complex-type (q1149022-one complex-type))
   (not
    (equal
     (q1149022-zero complex-type)
     (q1149022-one complex-type)))
   (q1149022-field-laws-p complex-type)
   (q1149022-of-real-laws-p real-type complex-type)
   (equal
    (q1149022-of-real
     real-type complex-type (q1149022-zero real-type))
    (q1149022-zero complex-type))
   (equal
    (q1149022-of-real
     real-type complex-type (q1149022-one real-type))
    (q1149022-one complex-type))
   (equal
    (q1149022-multiply
     complex-type
     (q1149022-imaginary-unit complex-type)
     (q1149022-imaginary-unit complex-type))
    (q1149022-negate complex-type (q1149022-one complex-type)))
   (equal
    (q1149022-real-part
     real-type complex-type
     (q1149022-imaginary-unit complex-type))
    (q1149022-zero real-type))
   (equal
    (q1149022-imag-part
     real-type complex-type
     (q1149022-imaginary-unit complex-type))
    (q1149022-one real-type))
   (q1149022-complex-coordinate-laws-p real-type complex-type)
   (q1149022-norm-laws-p real-type complex-type)
   (q1149022-complete-p real-type complex-type)))

;; Real and complex inner-product spaces.

(defun-sk q1149022-vector-space-laws-p
    (scalar-type space)
  (forall (a b x y z)
    (implies
     (and
      (q1149022-member-p scalar-type a)
      (q1149022-member-p scalar-type b)
      (q1149022-member-p space x)
      (q1149022-member-p space y)
      (q1149022-member-p space z))
     (and
      (q1149022-member-p space (q1149022-add space x y))
      (q1149022-member-p space (q1149022-negate space x))
      (q1149022-member-p
       space (q1149022-smul scalar-type space a x))
      (equal
       (q1149022-add space (q1149022-add space x y) z)
       (q1149022-add space x (q1149022-add space y z)))
      (equal (q1149022-add space x y) (q1149022-add space y x))
      (equal (q1149022-add space x (q1149022-zero space)) x)
      (equal
       (q1149022-add space x (q1149022-negate space x))
       (q1149022-zero space))
      (equal
       (q1149022-smul
        scalar-type space (q1149022-one scalar-type) x)
       x)
      (equal
       (q1149022-smul
        scalar-type space
        (q1149022-multiply scalar-type a b) x)
       (q1149022-smul
        scalar-type space a
        (q1149022-smul scalar-type space b x)))
      (equal
       (q1149022-smul
        scalar-type space
        (q1149022-add scalar-type a b) x)
       (q1149022-add
        space
        (q1149022-smul scalar-type space a x)
        (q1149022-smul scalar-type space b x)))
      (equal
       (q1149022-smul
        scalar-type space a (q1149022-add space x y))
       (q1149022-add
        space
        (q1149022-smul scalar-type space a x)
        (q1149022-smul scalar-type space a y)))))))

(defun-sk q1149022-normed-space-laws-p
    (real-type scalar-type space)
  (forall (a x)
    (implies
     (and
      (q1149022-member-p scalar-type a)
      (q1149022-member-p space x))
     (equal
      (q1149022-norm
       space
       (q1149022-smul scalar-type space a x))
      (q1149022-multiply
       real-type
       (q1149022-norm scalar-type a)
       (q1149022-norm space x))))))

(defun-sk q1149022-inner-product-laws-p
    (real-type scalar-type space)
  (forall (a x y z)
    (implies
     (and
      (q1149022-member-p scalar-type a)
      (q1149022-member-p space x)
      (q1149022-member-p space y)
      (q1149022-member-p space z))
     (let ((xy (q1149022-inner scalar-type space x y))
           (xx (q1149022-inner scalar-type space x x)))
       (and
        (q1149022-member-p scalar-type xy)
        (equal
         (q1149022-inner
          scalar-type space x (q1149022-add space y z))
         (q1149022-add
          scalar-type xy
          (q1149022-inner scalar-type space x z)))
        (equal
         (q1149022-inner
          scalar-type space x
          (q1149022-smul scalar-type space a y))
         (q1149022-multiply scalar-type a xy))
        (equal
         (q1149022-inner scalar-type space y x)
         (q1149022-star scalar-type xy))
        (equal
         (q1149022-multiply
          real-type
          (q1149022-norm space x)
          (q1149022-norm space x))
         (q1149022-real-part real-type scalar-type xx))
        (iff
         (equal xx (q1149022-zero scalar-type))
         (equal x (q1149022-zero space))))))))

(defun-sk q1149022-real-smul-compatibility-p
    (real-type complex-type space)
  (forall (r x)
    (implies
     (and
      (q1149022-member-p real-type r)
      (q1149022-member-p space x))
     (equal
      (q1149022-smul real-type space r x)
      (q1149022-smul
       complex-type space
       (q1149022-of-real real-type complex-type r)
       x)))))

(defun-sk q1149022-orthonormal-basis-laws-p
    (real-type space basis coordinates dimension)
  (forall (i j x)
    (and
     (implies
      (and (natp i) (< i dimension))
      (q1149022-member-p space (q1149022-basis-at basis i)))
     (implies
      (and
       (natp i) (natp j)
       (< i dimension) (< j dimension))
      (equal
       (q1149022-inner
        real-type space
        (q1149022-basis-at basis i)
        (q1149022-basis-at basis j))
       (if (equal i j)
           (q1149022-one real-type)
         (q1149022-zero real-type))))
     (implies
      (q1149022-member-p space x)
      (and
       (implies
        (and (natp i) (< i dimension))
        (q1149022-member-p
         real-type
         (q1149022-coordinate coordinates x i)))
       (equal
        x
        (q1149022-vector-sum
         real-type space basis coordinates x dimension)))))))

(defun q1149022-finite-real-inner-product-space-p
    (real-type space basis coordinates dimension)
  (and
   (natp dimension)
   (q1149022-member-p space (q1149022-zero space))
   (q1149022-vector-space-laws-p real-type space)
   (q1149022-norm-laws-p real-type space)
   (q1149022-normed-space-laws-p real-type real-type space)
   (q1149022-inner-product-laws-p real-type real-type space)
   (q1149022-orthonormal-basis-laws-p
    real-type space basis coordinates dimension)))

(defun q1149022-complex-hilbert-space-p
    (real-type complex-type space)
  (and
   (q1149022-member-p space (q1149022-zero space))
   (q1149022-vector-space-laws-p complex-type space)
   (q1149022-vector-space-laws-p real-type space)
   (q1149022-norm-laws-p real-type space)
   (q1149022-normed-space-laws-p
    real-type complex-type space)
   (q1149022-normed-space-laws-p
    real-type real-type space)
   (q1149022-real-smul-compatibility-p
    real-type complex-type space)
   (q1149022-inner-product-laws-p
    real-type complex-type space)
   (q1149022-complete-p real-type space)))

;; Borel sigma algebra and normalized translation-invariant volume.

(defun-sk q1149022-countable-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q1149022-set-member-p
      (q1149022-sequence-at sequence n) x))))

(defun-sk q1149022-valid-set-p (space set)
  (forall (x)
    (implies
     (q1149022-set-member-p set x)
     (q1149022-member-p space x))))

(defun-sk q1149022-sets-equal-on-p (space left right)
  (forall (x)
    (implies
     (q1149022-member-p space x)
     (iff
      (q1149022-set-member-p left x)
      (q1149022-set-member-p right x)))))

(defun-sk q1149022-empty-on-p (space set)
  (forall (x)
    (implies
     (q1149022-member-p space x)
     (not (q1149022-set-member-p set x)))))

(defun-sk q1149022-full-set-law-p (space)
  (forall (x)
    (iff
     (q1149022-set-member-p
      (q1149022-full-set space) x)
     (q1149022-member-p space x))))

(defun-sk q1149022-complement-set-law-p (space)
  (forall (set x)
    (iff
     (q1149022-set-member-p
      (q1149022-complement-set space set) x)
     (and
      (q1149022-member-p space x)
      (not (q1149022-set-member-p set x))))))

(defun-sk q1149022-countable-union-set-law-p (space)
  (forall (sequence x)
    (iff
     (q1149022-set-member-p
      (q1149022-countable-union-set space sequence) x)
     (and
      (q1149022-member-p space x)
      (q1149022-countable-union-member-p sequence x)))))

(defun-sk q1149022-open-ball-set-law-p (real-type space)
  (forall (center radius x)
    (iff
     (q1149022-set-member-p
      (q1149022-open-ball-set space center radius) x)
     (and
      (q1149022-member-p space x)
      (q1149022-member-p space center)
      (q1149022-member-p real-type radius)
      (q1149022-less
       real-type
       (q1149022-distance real-type space x center)
       radius)))))

(defun-sk q1149022-preimage-set-law-p (domain)
  (forall (function set x)
    (iff
     (q1149022-set-member-p
      (q1149022-preimage-set function set) x)
     (and
      (q1149022-member-p domain x)
      (q1149022-set-member-p
       set (q1149022-function-at function x))))))

(defun-sk q1149022-translate-set-law-p (space)
  (forall (set shift x)
    (iff
     (q1149022-set-member-p
      (q1149022-translate-set space set shift) x)
     (and
      (q1149022-member-p space x)
      (q1149022-set-member-p
       set
       (q1149022-add
        space x (q1149022-negate space shift)))))))

(defun q1149022-set-constructor-laws-p
    (real-type space)
  (and
   (q1149022-full-set-law-p space)
   (q1149022-complement-set-law-p space)
   (q1149022-countable-union-set-law-p space)
   (q1149022-open-ball-set-law-p real-type space)
   (q1149022-translate-set-law-p space)))

(defun-sk q1149022-sequence-measurable-p (family sequence)
  (forall (n)
    (implies
     (natp n)
     (q1149022-family-member-p
      family
      (q1149022-sequence-at sequence n)))))

(defun-sk q1149022-family-valid-sets-p (space family)
  (forall (set)
    (implies
     (q1149022-family-member-p family set)
     (q1149022-valid-set-p space set))))

(defun-sk q1149022-family-extensional-p (space family)
  (forall (left right)
    (implies
     (and
      (q1149022-family-member-p family left)
      (q1149022-valid-set-p space right)
      (q1149022-sets-equal-on-p space left right))
     (q1149022-family-member-p family right))))

(defun-sk q1149022-sigma-algebra-closure-p (space family)
  (forall (set sequence)
    (and
     (q1149022-family-member-p family (q1149022-full-set space))
     (implies
      (q1149022-family-member-p family set)
      (q1149022-family-member-p
       family (q1149022-complement-set space set)))
     (implies
      (q1149022-sequence-measurable-p family sequence)
      (q1149022-family-member-p
       family
       (q1149022-countable-union-set space sequence))))))

(defun q1149022-sigma-algebra-p (space family)
  (and
   (q1149022-family-valid-sets-p space family)
   (q1149022-family-extensional-p space family)
   (q1149022-sigma-algebra-closure-p space family)))

(defun-sk q1149022-balls-measurable-p
    (real-type space family)
  (forall (center radius)
    (implies
     (and
      (q1149022-member-p space center)
      (q1149022-member-p real-type radius)
      (q1149022-positive-p real-type radius))
     (q1149022-family-member-p
      family
      (q1149022-open-ball-set space center radius)))))

(defun-sk q1149022-family-subset-p (left right)
  (forall (set)
    (implies
     (q1149022-family-member-p left set)
     (q1149022-family-member-p right set))))

(defun-sk q1149022-borel-minimal-p
    (real-type space borel)
  (forall (candidate)
    (implies
     (and
      (q1149022-sigma-algebra-p space candidate)
      (q1149022-balls-measurable-p
       real-type space candidate))
     (q1149022-family-subset-p borel candidate))))

(defun q1149022-borel-space-p
    (real-type space borel)
  (and
   (q1149022-sigma-algebra-p space borel)
   (q1149022-balls-measurable-p real-type space borel)
   (q1149022-borel-minimal-p real-type space borel)))

(defun q1149022-ennreal-p (real-type x)
  (or
   (equal x :q1149022-top)
   (and
    (consp x)
    (equal (car x) :q1149022-finite)
    (q1149022-member-p real-type (cdr x))
    (q1149022-leq
     real-type (q1149022-zero real-type) (cdr x)))))

(defun q1149022-ennreal-finite (x)
  (cons :q1149022-finite x))

(defun q1149022-ennreal-add (real-type x y)
  (if (or
       (equal x :q1149022-top)
       (equal y :q1149022-top))
      :q1149022-top
    (q1149022-ennreal-finite
     (q1149022-add real-type (cdr x) (cdr y)))))

(defun q1149022-ennreal-leq-p (real-type x y)
  (or
   (equal y :q1149022-top)
   (and
    (not (equal x :q1149022-top))
    (q1149022-leq real-type (cdr x) (cdr y)))))

(defun q1149022-ennreal-less-p (real-type x y)
  (and
   (q1149022-ennreal-p real-type x)
   (q1149022-ennreal-p real-type y)
   (not (q1149022-ennreal-leq-p real-type y x))))

(defun q1149022-ennreal-zero-p (real-type value)
  (equal
   value
   (q1149022-ennreal-finite
    (q1149022-zero real-type))))

(defun q1149022-ennreal-multiply (real-type left right)
  (if (or
       (q1149022-ennreal-zero-p real-type left)
       (q1149022-ennreal-zero-p real-type right))
      (q1149022-ennreal-finite
       (q1149022-zero real-type))
    (if (or
         (equal left :q1149022-top)
         (equal right :q1149022-top))
        :q1149022-top
      (q1149022-ennreal-finite
       (q1149022-multiply
        real-type (cdr left) (cdr right))))))

(defun-sk q1149022-disjoint-sequence-p
    (space sequence)
  (forall (i j x)
    (implies
     (and
      (natp i) (natp j)
      (not (equal i j))
      (q1149022-member-p space x))
     (not
      (and
       (q1149022-set-member-p
        (q1149022-sequence-at sequence i) x)
       (q1149022-set-member-p
        (q1149022-sequence-at sequence j) x))))))

(defun q1149022-ennreal-partial-sum
    (real-type measure sequence n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1149022-ennreal-finite (q1149022-zero real-type))
    (q1149022-ennreal-add
     real-type
     (q1149022-ennreal-partial-sum
      real-type measure sequence (- n 1))
     (q1149022-measure-value
      measure
      (q1149022-sequence-at sequence (- n 1))))))

(defun-sk q1149022-ennreal-upper-bound-p
    (real-type measure sequence bound)
  (forall (n)
    (implies
     (natp n)
     (q1149022-ennreal-leq-p
      real-type
      (q1149022-ennreal-partial-sum
       real-type measure sequence n)
      bound))))

(defun-sk q1149022-ennreal-series-value-p
    (real-type measure sequence value)
  (forall (bound)
    (iff
     (q1149022-ennreal-upper-bound-p
      real-type measure sequence bound)
     (q1149022-ennreal-leq-p real-type value bound))))

(defun-sk q1149022-countable-additivity-p
    (real-type space measurable measure)
  (forall (sequence)
    (implies
     (and
      (q1149022-sequence-measurable-p measurable sequence)
      (q1149022-disjoint-sequence-p space sequence))
     (q1149022-ennreal-series-value-p
      real-type
      measure
      sequence
      (q1149022-measure-value
       measure
       (q1149022-countable-union-set space sequence))))))

(defun-sk q1149022-measure-values-p (real-type measure)
  (forall (set)
    (q1149022-ennreal-p
     real-type
     (q1149022-measure-value measure set))))

(defun-sk q1149022-measure-extensional-p (space measure)
  (forall (left right)
    (implies
     (and
      (q1149022-valid-set-p space left)
      (q1149022-valid-set-p space right)
      (q1149022-sets-equal-on-p space left right))
     (equal
      (q1149022-measure-value measure left)
      (q1149022-measure-value measure right)))))

(defun-sk q1149022-empty-measurable-zero-p
    (real-type space measurable measure)
  (forall (set)
    (implies
     (and
      (q1149022-family-member-p measurable set)
      (q1149022-empty-on-p space set))
     (equal
      (q1149022-measure-value measure set)
      (q1149022-ennreal-finite
       (q1149022-zero real-type))))))

(defun q1149022-measure-space-p
    (real-type space measurable measure)
  (and
   (q1149022-sigma-algebra-p space measurable)
   (q1149022-measure-values-p real-type measure)
   (q1149022-measure-extensional-p space measure)
   (q1149022-empty-measurable-zero-p
    real-type space measurable measure)
   (equal
    (q1149022-measure-value
     measure
     (q1149022-complement-set
      space (q1149022-full-set space)))
    (q1149022-ennreal-finite (q1149022-zero real-type)))
   (q1149022-countable-additivity-p
    real-type space measurable measure)))

(defun q1149022-unit-coordinates-p
    (real-type coordinates x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (let ((c
           (q1149022-coordinate
            coordinates x (- n 1))))
      (and
       (q1149022-leq
        real-type (q1149022-zero real-type) c)
       (q1149022-less
        real-type c (q1149022-one real-type))
       (q1149022-unit-coordinates-p
        real-type coordinates x (- n 1))))))

(defun-sk q1149022-unit-cell-coordinate-p
    (real-type space basis coordinates dimension)
  (forall (x)
    (iff
     (q1149022-set-member-p
      (q1149022-unit-cell-set
       space basis coordinates dimension)
      x)
     (and
      (q1149022-member-p space x)
      (q1149022-unit-coordinates-p
       real-type coordinates x dimension)))))

(defun-sk q1149022-translation-invariant-p
    (space measurable measure)
  (forall (set shift)
    (implies
     (and
      (q1149022-family-member-p measurable set)
      (q1149022-member-p space shift))
     (equal
      (q1149022-measure-value
       measure
       (q1149022-translate-set space set shift))
      (q1149022-measure-value measure set)))))

(defun q1149022-volume-space-p
    (real-type space basis coordinates dimension measurable measure)
  (and
   (q1149022-borel-space-p real-type space measurable)
   (q1149022-measure-space-p
    real-type space measurable measure)
   (q1149022-unit-cell-coordinate-p
    real-type space basis coordinates dimension)
   (q1149022-family-member-p
    measurable
    (q1149022-unit-cell-set
     space basis coordinates dimension))
   (equal
    (q1149022-measure-value
     measure
     (q1149022-unit-cell-set
      space basis coordinates dimension))
    (q1149022-ennreal-finite
     (q1149022-one real-type)))
   (q1149022-translation-invariant-p
    space measurable measure)))

;; Lebesgue lower integration and Bochner integration.

(defun-sk q1149022-function-into-p
    (domain codomain function)
  (forall (x)
    (implies
     (q1149022-member-p domain x)
     (q1149022-member-p
      codomain
      (q1149022-function-at function x)))))

(defun-sk q1149022-continuous-at-delta-p
    (real-type domain codomain function x epsilon delta)
  (forall (y)
    (implies
     (and
      (q1149022-member-p domain y)
      (q1149022-less
       real-type
       (q1149022-distance real-type domain y x)
       delta))
     (q1149022-less
      real-type
      (q1149022-distance
       real-type codomain
       (q1149022-function-at function y)
       (q1149022-function-at function x))
      epsilon))))

(defun-sk q1149022-continuous-at-epsilon-p
    (real-type domain codomain function x epsilon)
  (exists (delta)
    (and
     (q1149022-member-p real-type delta)
     (q1149022-positive-p real-type delta)
     (q1149022-continuous-at-delta-p
      real-type domain codomain function x epsilon delta))))

(defun-sk q1149022-continuous-function-p
    (real-type domain codomain function)
  (forall (x epsilon)
    (implies
     (and
      (q1149022-member-p domain x)
      (q1149022-member-p real-type epsilon)
      (q1149022-positive-p real-type epsilon))
     (q1149022-continuous-at-epsilon-p
      real-type domain codomain function x epsilon))))

(defun-sk q1149022-function-constructor-laws-p
    (real-type)
  (forall (type f g set value x)
    (and
     (equal
      (q1149022-function-at
       (q1149022-function-add type f g) x)
      (q1149022-add
       type
       (q1149022-function-at f x)
       (q1149022-function-at g x)))
     (equal
      (q1149022-function-at
       (q1149022-function-difference type f g) x)
      (q1149022-add
       type
       (q1149022-function-at f x)
       (q1149022-negate
        type (q1149022-function-at g x))))
     (equal
      (q1149022-function-at
       (q1149022-function-norm real-type type f) x)
      (q1149022-norm type (q1149022-function-at f x)))
     (equal
      (q1149022-function-at
       (q1149022-indicator-function real-type set) x)
      (if (q1149022-set-member-p set x)
          (q1149022-one real-type)
        (q1149022-zero real-type))))))

(defun-sk q1149022-fiber-set-law-p (domain)
  (forall (function value x)
    (iff
     (q1149022-set-member-p
      (q1149022-fiber-set function value)
      x)
     (and
      (q1149022-member-p domain x)
      (equal (q1149022-function-at function x) value)))))

(defun-sk q1149022-measurable-function-p
    (real-type domain measurable codomain function)
  (forall (center radius)
    (implies
     (and
      (q1149022-member-p codomain center)
      (q1149022-member-p real-type radius)
      (q1149022-positive-p real-type radius))
     (q1149022-family-member-p
      measurable
      (q1149022-preimage-set
       function
       (q1149022-open-ball-set
        codomain center radius))))))

(defun-sk q1149022-nonnegative-values-p
    (real-type domain function)
  (forall (x)
    (implies
     (q1149022-member-p domain x)
     (q1149022-leq
      real-type
      (q1149022-zero real-type)
      (q1149022-function-at function x)))))

(defun q1149022-nonnegative-measurable-p
    (real-type domain measurable function)
  (and
   (q1149022-function-into-p
    domain real-type function)
   (q1149022-measurable-function-p
    real-type domain measurable real-type function)
   (q1149022-nonnegative-values-p
    real-type domain function)))

;; ENNReal-valued functions are measurable exactly when all strict upper-ray
;; preimages are measurable. This is the order-topology Borel criterion for
;; the extended nonnegative reals.

(defun-sk q1149022-ennreal-function-p
    (real-type domain function)
  (forall (x)
    (implies
     (q1149022-member-p domain x)
     (q1149022-ennreal-p
      real-type
      (q1149022-function-at function x)))))

(defun-sk q1149022-ennreal-upper-preimage-set-p
    (real-type domain function threshold set)
  (forall (x)
    (iff
     (q1149022-set-member-p set x)
     (and
      (q1149022-member-p domain x)
      (q1149022-ennreal-less-p
       real-type
       threshold
       (q1149022-function-at function x))))))

(defun-sk q1149022-ennreal-upper-preimage-exists-p
    (real-type domain measurable function threshold)
  (exists (set)
    (and
     (q1149022-ennreal-upper-preimage-set-p
      real-type domain function threshold set)
     (q1149022-family-member-p measurable set))))

(defun-sk q1149022-measurable-ennreal-function-p
    (real-type domain measurable function)
  (forall (threshold)
    (and
     (q1149022-ennreal-function-p
      real-type domain function)
     (implies
      (q1149022-ennreal-p real-type threshold)
      (q1149022-ennreal-upper-preimage-exists-p
       real-type domain measurable function threshold)))))

(defun-sk q1149022-pointwise-leq-p
    (real-type domain left right)
  (forall (x)
    (implies
     (q1149022-member-p domain x)
     (q1149022-leq
      real-type
      (q1149022-function-at left x)
      (q1149022-function-at right x)))))

(defun-sk q1149022-functions-equal-on-p
    (domain left right)
  (forall (x)
    (implies
     (q1149022-member-p domain x)
     (equal
      (q1149022-function-at left x)
      (q1149022-function-at right x)))))

(defun-sk q1149022-lintegral-laws-p
    (real-type domain measurable measure lintegral)
  (forall (f g set)
    (and
     (implies
      (q1149022-functions-equal-on-p domain f g)
      (equal
       (q1149022-lintegral-value lintegral f)
       (q1149022-lintegral-value lintegral g)))
     (implies
      (q1149022-nonnegative-measurable-p
       real-type domain measurable f)
      (q1149022-ennreal-p
       real-type
       (q1149022-lintegral-value lintegral f)))
     (implies
      (and
       (q1149022-nonnegative-measurable-p
        real-type domain measurable f)
       (q1149022-nonnegative-measurable-p
        real-type domain measurable g)
       (q1149022-pointwise-leq-p real-type domain f g))
      (q1149022-ennreal-leq-p
       real-type
       (q1149022-lintegral-value lintegral f)
       (q1149022-lintegral-value lintegral g)))
     (implies
      (q1149022-family-member-p measurable set)
      (equal
       (q1149022-lintegral-value
        lintegral
        (q1149022-indicator-function real-type set))
       (q1149022-measure-value measure set)))
     (implies
      (and
       (q1149022-nonnegative-measurable-p
        real-type domain measurable f)
       (q1149022-nonnegative-measurable-p
        real-type domain measurable g))
      (equal
       (q1149022-lintegral-value
        lintegral
        (q1149022-function-add real-type f g))
       (q1149022-ennreal-add
        real-type
        (q1149022-lintegral-value lintegral f)
        (q1149022-lintegral-value lintegral g)))))))

(defun q1149022-simple-values-correct-p
    (domain measurable function values)
  (if (consp values)
      (and
       (q1149022-family-member-p
        measurable
        (q1149022-fiber-set function (car values)))
       (q1149022-simple-values-correct-p
        domain measurable function (cdr values)))
    (equal values nil)))

(defun q1149022-simple-listed-values-in-space-p
    (space values)
  (if (consp values)
      (and
       (q1149022-member-p space (car values))
       (q1149022-simple-listed-values-in-space-p
        space (cdr values)))
    (equal values nil)))

(defun-sk q1149022-simple-range-values-p
    (domain function values)
  (forall (x)
    (implies
     (q1149022-member-p domain x)
     (member-equal
      (q1149022-function-at function x)
      values))))

(defun-sk q1149022-value-attained-p
    (domain function value)
  (exists (x)
    (and
     (q1149022-member-p domain x)
     (equal
      (q1149022-function-at function x)
      value))))

(defun q1149022-simple-function-p
    (domain measurable space function)
  (and
   (q1149022-function-into-p domain space function)
   (true-listp (q1149022-simple-values function))
   (no-duplicatesp-equal (q1149022-simple-values function))
   (q1149022-simple-listed-values-in-space-p
    space (q1149022-simple-values function))
   (q1149022-simple-values-correct-p
    domain measurable function
    (q1149022-simple-values function))
   (q1149022-simple-range-values-p
    domain function
    (q1149022-simple-values function))))

(defun q1149022-ennreal-value-list-p
    (real-type values)
  (if (consp values)
      (and
       (q1149022-ennreal-p real-type (car values))
       (q1149022-ennreal-value-list-p
        real-type (cdr values)))
    (equal values nil)))

(defun q1149022-values-attained-p
    (domain function values)
  (if (consp values)
      (and
       (q1149022-value-attained-p
        domain function (car values))
       (q1149022-values-attained-p
        domain function (cdr values)))
    (equal values nil)))

(defun q1149022-ennreal-simple-function-p
    (real-type domain measurable function)
  (and
   (q1149022-ennreal-function-p
    real-type domain function)
   (true-listp (q1149022-simple-values function))
   (no-duplicatesp-equal
    (q1149022-simple-values function))
   (q1149022-ennreal-value-list-p
    real-type (q1149022-simple-values function))
   (q1149022-values-attained-p
    domain function (q1149022-simple-values function))
   (q1149022-simple-values-correct-p
    domain measurable function
    (q1149022-simple-values function))
   (q1149022-simple-range-values-p
    domain function
    (q1149022-simple-values function))))

(defun-sk q1149022-ennreal-pointwise-leq-p
    (real-type domain left right)
  (forall (x)
    (implies
     (q1149022-member-p domain x)
     (q1149022-ennreal-leq-p
      real-type
      (q1149022-function-at left x)
      (q1149022-function-at right x)))))

(defun q1149022-ennreal-simple-integral
    (real-type domain measure function values)
  (if (consp values)
      (q1149022-ennreal-add
       real-type
       (q1149022-ennreal-multiply
        real-type
        (car values)
        (q1149022-measure-value
         measure
         (q1149022-fiber-set function (car values))))
       (q1149022-ennreal-simple-integral
        real-type domain measure function (cdr values)))
    (q1149022-ennreal-finite
     (q1149022-zero real-type))))

(defun-sk q1149022-ennreal-lintegral-upper-bound-p
    (real-type domain measurable measure function bound)
  (forall (simple)
    (implies
     (and
      (q1149022-ennreal-simple-function-p
       real-type domain measurable simple)
      (q1149022-ennreal-pointwise-leq-p
       real-type domain simple function))
     (q1149022-ennreal-leq-p
      real-type
      (q1149022-ennreal-simple-integral
       real-type domain measure simple
       (q1149022-simple-values simple))
      bound))))

(defun-sk q1149022-ennreal-lintegral-least-upper-bound-p
    (real-type domain measurable measure function value)
  (forall (bound)
    (implies
     (and
      (q1149022-ennreal-p real-type bound)
      (q1149022-ennreal-lintegral-upper-bound-p
       real-type domain measurable measure function bound))
     (q1149022-ennreal-leq-p
      real-type value bound))))

(defun-sk q1149022-ennreal-lintegral-operation-p
    (real-type domain measurable measure lintegral)
  (forall (function)
    (implies
     (q1149022-ennreal-function-p
      real-type domain function)
     (let ((value
            (q1149022-ennreal-lintegral-value
             lintegral function)))
       (and
        (q1149022-ennreal-p real-type value)
        (q1149022-ennreal-lintegral-upper-bound-p
         real-type domain measurable measure function value)
        (q1149022-ennreal-lintegral-least-upper-bound-p
         real-type domain measurable measure function value))))))

(defun q1149022-simple-integrable-values-p
    (real-type domain measure zero function values)
  (if (consp values)
      (and
       (implies
        (not
         (q1149022-value-attained-p
          domain function (car values)))
        (equal
         (q1149022-measure-value
          measure
          (q1149022-fiber-set function (car values)))
         (q1149022-ennreal-finite
          (q1149022-zero real-type))))
       (or
        (equal (car values) zero)
        (not
         (equal
          (q1149022-measure-value
           measure
           (q1149022-fiber-set function (car values)))
          :q1149022-top)))
       (q1149022-simple-integrable-values-p
        real-type domain measure zero function (cdr values)))
    (equal values nil)))

(defun q1149022-simple-integral
    (real-type domain space measure function values)
  (if (consp values)
      (q1149022-add
       space
       (if (or
            (equal (car values) (q1149022-zero space))
            (not
             (q1149022-value-attained-p
              domain function (car values))))
           (q1149022-zero space)
         (q1149022-smul
          real-type space
          (cdr
           (q1149022-measure-value
            measure
            (q1149022-fiber-set function (car values))))
          (car values)))
       (q1149022-simple-integral
        real-type domain space measure function (cdr values)))
    (q1149022-zero space)))

(defun q1149022-ennreal-scale
    (real-type scalar value)
  (if (equal scalar (q1149022-zero real-type))
      (q1149022-ennreal-finite
       (q1149022-zero real-type))
    (if (equal value :q1149022-top)
        :q1149022-top
      (q1149022-ennreal-finite
       (q1149022-multiply
        real-type scalar (cdr value))))))

(defun q1149022-simple-nonnegative-integral
    (real-type domain measure function values)
  (if (consp values)
      (q1149022-ennreal-add
       real-type
       (if
           (q1149022-value-attained-p
            domain function (car values))
           (q1149022-ennreal-scale
            real-type
            (car values)
            (q1149022-measure-value
             measure
             (q1149022-fiber-set function (car values))))
         (q1149022-ennreal-finite
          (q1149022-zero real-type)))
       (q1149022-simple-nonnegative-integral
        real-type domain measure function (cdr values)))
    (q1149022-ennreal-finite
     (q1149022-zero real-type))))

(defun-sk q1149022-lintegral-upper-bound-p
    (real-type domain measurable measure function bound)
  (forall (simple)
    (implies
     (and
      (q1149022-simple-function-p
       domain measurable real-type simple)
      (q1149022-nonnegative-values-p
       real-type domain simple)
      (q1149022-pointwise-leq-p
       real-type domain simple function))
     (q1149022-ennreal-leq-p
      real-type
      (q1149022-simple-nonnegative-integral
       real-type domain measure simple
       (q1149022-simple-values simple))
      bound))))

(defun-sk q1149022-lintegral-least-upper-bound-p
    (real-type domain measurable measure function value)
  (forall (bound)
    (implies
     (and
      (q1149022-ennreal-p real-type bound)
      (q1149022-lintegral-upper-bound-p
       real-type domain measurable measure function bound))
     (q1149022-ennreal-leq-p real-type value bound))))

(defun-sk q1149022-lintegral-supremum-laws-p
    (real-type domain measurable measure lintegral)
  (forall (function)
    (implies
     (q1149022-nonnegative-measurable-p
      real-type domain measurable function)
     (let ((value
            (q1149022-lintegral-value
             lintegral function)))
       (and
        (q1149022-ennreal-p real-type value)
        (q1149022-lintegral-upper-bound-p
         real-type domain measurable measure function value)
        (q1149022-lintegral-least-upper-bound-p
         real-type domain measurable measure function value))))))

(defun-sk q1149022-simple-sequence-p
    (domain measurable space sequence)
  (forall (n)
    (implies
     (natp n)
     (q1149022-simple-function-p
      domain measurable space
      (q1149022-sequence-at sequence n)))))

(defun-sk q1149022-pointwise-simple-limit-p
    (real-type domain space sequence function)
  (forall (x)
    (implies
     (q1149022-member-p domain x)
     (q1149022-converges-p
      real-type
      space
      (q1149022-point-sequence sequence x)
      (q1149022-function-at function x)))))

(defun-sk q1149022-point-sequence-laws-p ()
  (forall (sequence x n)
    (equal
     (q1149022-sequence-at
      (q1149022-point-sequence sequence x) n)
     (q1149022-function-at
      (q1149022-sequence-at sequence n) x))))

(defun-sk q1149022-strongly-measurable-p
    (real-type domain measurable space function)
  (exists (sequence)
    (and
     (q1149022-simple-sequence-p
      domain measurable space sequence)
     (q1149022-pointwise-simple-limit-p
      real-type domain space sequence function))))

(defun q1149022-integrable-p
    (real-type domain measurable lintegral space function)
  (and
   (q1149022-strongly-measurable-p
    real-type domain measurable space function)
   (not
    (equal
     (q1149022-lintegral-value
      lintegral
      (q1149022-function-norm real-type space function))
     :q1149022-top))))

(defun q1149022-l1-distance
    (real-type space lintegral left right)
  (q1149022-lintegral-value
   lintegral
   (q1149022-function-norm
    real-type space
    (q1149022-function-difference space left right))))

(defun-sk q1149022-l1-tail-p
    (real-type space lintegral sequence function epsilon start)
  (forall (n)
    (implies
     (and (natp n) (natp start) (<= start n))
     (q1149022-ennreal-leq-p
      real-type
      (q1149022-l1-distance
       real-type space lintegral
       (q1149022-sequence-at sequence n)
       function)
      (q1149022-ennreal-finite epsilon)))))

(defun-sk q1149022-l1-start-p
    (real-type space lintegral sequence function epsilon)
  (exists (start)
    (and
     (natp start)
     (q1149022-l1-tail-p
      real-type space lintegral
      sequence function epsilon start))))

(defun-sk q1149022-l1-converges-p
    (real-type space lintegral sequence function)
  (forall (epsilon)
    (implies
     (and
      (q1149022-member-p real-type epsilon)
      (q1149022-positive-p real-type epsilon))
     (q1149022-l1-start-p
      real-type space lintegral sequence function epsilon))))

(defun-sk q1149022-integrable-simple-sequence-p
    (real-type domain measurable measure space sequence)
  (forall (n)
    (implies
     (natp n)
     (let ((f (q1149022-sequence-at sequence n)))
       (and
        (q1149022-simple-function-p
         domain measurable space f)
        (q1149022-simple-integrable-values-p
         real-type domain measure
         (q1149022-zero space) f
         (q1149022-simple-values f)))))))

(defun-sk q1149022-simple-integral-sequence-laws-p ()
  (forall (real-type domain space measure sequence n)
    (equal
     (q1149022-sequence-at
      (q1149022-simple-integral-sequence
       real-type domain space measure sequence)
      n)
     (q1149022-simple-integral
      real-type domain space measure
      (q1149022-sequence-at sequence n)
      (q1149022-simple-values
       (q1149022-sequence-at sequence n))))))

(defun q1149022-bochner-approximation-p
    (real-type domain measurable measure lintegral
     space function value sequence)
  (and
   (q1149022-integrable-simple-sequence-p
    real-type domain measurable measure space sequence)
   (q1149022-l1-converges-p
    real-type space lintegral sequence function)
   (q1149022-converges-p
    real-type space
    (q1149022-simple-integral-sequence
     real-type domain space measure sequence)
    value)))

(defun-sk q1149022-bochner-approximation-exists-p
    (real-type domain measurable measure lintegral
     space function value)
  (exists (sequence)
    (q1149022-bochner-approximation-p
     real-type domain measurable measure lintegral
     space function value sequence)))

(defun-sk q1149022-bochner-integral-operation-p
    (real-type domain measurable measure lintegral space integral)
  (forall (function other)
    (and
     (implies
      (q1149022-functions-equal-on-p
       domain function other)
      (equal
       (q1149022-bochner-integral-value
        integral function)
       (q1149022-bochner-integral-value
        integral other)))
     (implies
      (q1149022-function-into-p domain space function)
      (let ((value
             (q1149022-bochner-integral-value
              integral function)))
        (and
         (q1149022-member-p space value)
         (if
             (and
              (q1149022-complete-p real-type space)
              (q1149022-integrable-p
               real-type domain measurable lintegral
               space function))
             (q1149022-bochner-approximation-exists-p
              real-type domain measurable measure lintegral
              space function value)
           (equal value (q1149022-zero space)))))))))

;; Schwartz maps and the normalized Fourier fourier-char.

(defun q1149022-directional-difference-quotient
    (real-type domain codomain basis function x i h)
  (q1149022-smul
   real-type codomain
   (q1149022-inverse real-type h)
   (q1149022-add
    codomain
    (q1149022-function-at
     function
     (q1149022-add
      domain x
      (q1149022-smul
       real-type domain h
       (q1149022-basis-at basis i))))
    (q1149022-negate
     codomain
     (q1149022-function-at function x)))))

(defun-sk q1149022-derivative-delta-p
    (real-type domain codomain basis
     function derivative x i epsilon delta)
  (forall (h)
    (implies
     (and
      (q1149022-member-p real-type h)
      (q1149022-positive-p
       real-type (q1149022-abs real-type h))
      (q1149022-less
       real-type (q1149022-abs real-type h) delta))
     (q1149022-less
      real-type
      (q1149022-distance
       real-type codomain
       (q1149022-directional-difference-quotient
        real-type domain codomain basis function x i h)
       (q1149022-function-at derivative x))
      epsilon))))

(defun-sk q1149022-derivative-epsilon-p
    (real-type domain codomain basis
     function derivative x i epsilon)
  (exists (delta)
    (and
     (q1149022-member-p real-type delta)
     (q1149022-positive-p real-type delta)
     (q1149022-derivative-delta-p
      real-type domain codomain basis
      function derivative x i epsilon delta))))

(defun-sk q1149022-directional-derivative-p
    (real-type domain codomain basis
     function derivative i)
  (forall (x epsilon)
    (implies
     (and
      (q1149022-member-p domain x)
      (q1149022-member-p real-type epsilon)
      (q1149022-positive-p real-type epsilon))
     (q1149022-derivative-epsilon-p
      real-type domain codomain basis
      function derivative x i epsilon))))

(defun-sk q1149022-derivative-family-p
    (real-type domain codomain basis dimension derivatives function)
  (forall (alpha i)
    (implies
     (and
      (q1149022-natural-list-p alpha dimension)
      (natp i)
      (< i dimension))
     (and
      (q1149022-function-into-p
       domain codomain
       (q1149022-derivative-function
        derivatives function alpha))
      (q1149022-directional-derivative-p
       real-type domain codomain basis
       (q1149022-derivative-function
        derivatives function alpha)
       (q1149022-derivative-function
        derivatives function
        (q1149022-increment-multiindex alpha i))
       i)))))

(defun-sk q1149022-derivative-functions-continuous-p
    (real-type domain codomain dimension derivatives function)
  (forall (alpha)
    (implies
     (q1149022-natural-list-p alpha dimension)
     (let ((derivative
            (q1149022-derivative-function
             derivatives function alpha)))
       (and
        (q1149022-function-into-p
         domain codomain derivative)
        (q1149022-continuous-function-p
         real-type domain codomain derivative))))))

(defun-sk q1149022-decay-bound-p
    (real-type domain codomain derivatives function alpha k bound)
  (forall (x)
    (implies
     (q1149022-member-p domain x)
     (q1149022-leq
      real-type
      (q1149022-multiply
       real-type
       (q1149022-real-power
        real-type
        (q1149022-add
         real-type
         (q1149022-one real-type)
         (q1149022-norm domain x))
        k)
       (q1149022-norm
        codomain
        (q1149022-function-at
         (q1149022-derivative-function
          derivatives function alpha)
         x)))
      bound))))

(defun-sk q1149022-decay-bound-exists-p
    (real-type domain codomain derivatives function alpha k)
  (exists (bound)
    (and
     (q1149022-member-p real-type bound)
     (q1149022-leq
      real-type (q1149022-zero real-type) bound)
     (q1149022-decay-bound-p
      real-type domain codomain derivatives
      function alpha k bound))))

(defun-sk q1149022-rapid-decay-p
    (real-type domain codomain dimension derivatives function)
  (forall (alpha k)
    (implies
     (and
      (q1149022-natural-list-p alpha dimension)
      (natp k))
     (q1149022-decay-bound-exists-p
      real-type domain codomain derivatives
      function alpha k))))

(defun q1149022-schwartz-map-p
    (real-type domain codomain basis dimension derivatives function)
  (and
   (q1149022-function-into-p domain codomain function)
   (equal
    (q1149022-derivative-function
     derivatives function
     (q1149022-zero-multiindex dimension))
    function)
   (q1149022-derivative-family-p
    real-type domain codomain basis dimension
    derivatives function)
   (q1149022-derivative-functions-continuous-p
    real-type domain codomain dimension
    derivatives function)
   (q1149022-rapid-decay-p
    real-type domain codomain dimension
    derivatives function)))

(defun-sk q1149022-character-kernel-witness-p
    (real-type complex-type fourier-char x)
  (exists (n)
    (and
     (integerp n)
     (equal x (q1149022-integer-cast real-type n)))))

(defun-sk q1149022-character-laws-p
    (real-type complex-type fourier-char)
  (forall (x y)
    (implies
     (and
      (q1149022-member-p real-type x)
      (q1149022-member-p real-type y))
     (and
      (q1149022-member-p
       complex-type
       (q1149022-character-value fourier-char x))
      (equal
       (q1149022-character-value
        fourier-char (q1149022-add real-type x y))
       (q1149022-multiply
        complex-type
        (q1149022-character-value fourier-char x)
        (q1149022-character-value fourier-char y)))
      (equal
       (q1149022-norm
        complex-type
        (q1149022-character-value fourier-char x))
       (q1149022-one real-type))
      (iff
       (equal
        (q1149022-character-value fourier-char x)
        (q1149022-one complex-type))
       (q1149022-character-kernel-witness-p
        real-type complex-type fourier-char x))))))

(defun-sk q1149022-character-orientation-delta-p
    (real-type complex-type fourier-char delta)
  (forall (x)
    (implies
     (and
      (q1149022-member-p real-type x)
      (q1149022-positive-p real-type x)
      (q1149022-less real-type x delta))
     (q1149022-less
      real-type
      (q1149022-zero real-type)
      (q1149022-imag-part
       real-type complex-type
       (q1149022-character-value fourier-char x))))))

(defun-sk q1149022-character-orientation-p
    (real-type complex-type fourier-char)
  (exists (delta)
    (and
     (q1149022-member-p real-type delta)
     (q1149022-positive-p real-type delta)
     (q1149022-character-orientation-delta-p
      real-type complex-type fourier-char delta))))

(defun-sk q1149022-character-continuity-delta-p
    (real-type complex-type fourier-char epsilon delta)
  (forall (x)
    (implies
     (and
      (q1149022-member-p real-type x)
      (q1149022-less
       real-type
       (q1149022-abs real-type x)
       delta))
     (q1149022-less
      real-type
      (q1149022-distance
       real-type complex-type
       (q1149022-character-value fourier-char x)
       (q1149022-one complex-type))
      epsilon))))

(defun-sk q1149022-character-continuity-epsilon-p
    (real-type complex-type fourier-char epsilon)
  (exists (delta)
    (and
     (q1149022-member-p real-type delta)
     (q1149022-positive-p real-type delta)
     (q1149022-character-continuity-delta-p
      real-type complex-type fourier-char epsilon delta))))

(defun-sk q1149022-character-continuity-p
    (real-type complex-type fourier-char)
  (forall (epsilon)
    (implies
     (and
      (q1149022-member-p real-type epsilon)
      (q1149022-positive-p real-type epsilon))
     (q1149022-character-continuity-epsilon-p
      real-type complex-type fourier-char epsilon))))

(defun q1149022-fourier-character-p
    (real-type complex-type fourier-char)
  (and
   (equal
    (q1149022-character-value
     fourier-char (q1149022-zero real-type))
    (q1149022-one complex-type))
   (q1149022-character-laws-p
    real-type complex-type fourier-char)
   (q1149022-character-continuity-p
    real-type complex-type fourier-char)
   (q1149022-character-orientation-p
    real-type complex-type fourier-char)))

(defun-sk q1149022-inner-integrand-laws-p
    (complex-type space)
  (forall (f g x)
    (equal
     (q1149022-function-at
      (q1149022-inner-integrand
       complex-type space f g)
      x)
     (q1149022-inner
      complex-type space
      (q1149022-function-at f x)
      (q1149022-function-at g x)))))

(defun-sk q1149022-fourier-integrand-laws-p
    (real-type complex-type domain space fourier-char)
  (forall (f frequency x)
    (equal
     (q1149022-function-at
      (q1149022-fourier-integrand
       real-type complex-type domain space
       fourier-char f frequency)
      x)
     (q1149022-smul
      complex-type space
      (q1149022-character-value
       fourier-char
       (q1149022-negate
        real-type
        (q1149022-inner
         real-type domain x frequency)))
      (q1149022-function-at f x)))))

(defun-sk q1149022-fourier-transform-correct-p
    (real-type complex-type domain space
     fourier-char integral fourier function)
  (forall (frequency)
    (implies
     (q1149022-member-p domain frequency)
     (equal
      (q1149022-function-at
       (q1149022-fourier-function fourier function)
       frequency)
      (q1149022-bochner-integral-value
       integral
       (q1149022-fourier-integrand
        real-type complex-type domain space
        fourier-char function frequency))))))

;; The source domain is an arbitrary measurable space, so only the set
;; constructors needed for a sigma algebra are required on it.

(defun q1149022-basic-set-constructor-laws-p (domain)
  (and
   (q1149022-full-set-law-p domain)
   (q1149022-complement-set-law-p domain)
   (q1149022-countable-union-set-law-p domain)))

;; A real normed vector space need not be complete. This distinction is
;; semantically relevant because mathlib defines its Bochner integral to be
;; zero when the codomain is incomplete.

(defun q1149022-real-normed-space-p (real-type space)
  (and
   (q1149022-member-p space (q1149022-zero space))
   (q1149022-vector-space-laws-p real-type space)
   (q1149022-norm-laws-p real-type space)
   (q1149022-normed-space-laws-p real-type real-type space)))

;; Almost-everywhere predicates use a measurable null envelope, which is
;; equivalent to membership in the measure's almost-everywhere filter.

(defun q1149022-null-measurable-set-p
    (real-type domain measurable measure set)
  (and
   (q1149022-valid-set-p domain set)
   (q1149022-family-member-p measurable set)
   (equal
    (q1149022-measure-value measure set)
    (q1149022-ennreal-finite
     (q1149022-zero real-type)))))

(defun-sk q1149022-equal-off-set-p
    (domain left right exceptional)
  (forall (x)
    (implies
     (and
      (q1149022-member-p domain x)
      (not (q1149022-set-member-p exceptional x)))
     (equal
      (q1149022-function-at left x)
      (q1149022-function-at right x)))))

(defun q1149022-ae-equal-witness-p
    (real-type domain measurable measure left right exceptional)
  (and
   (q1149022-null-measurable-set-p
    real-type domain measurable measure exceptional)
   (q1149022-equal-off-set-p
    domain left right exceptional)))

(defun-sk q1149022-ae-equal-p
    (real-type domain measurable measure left right)
  (exists (exceptional)
    (q1149022-ae-equal-witness-p
     real-type domain measurable measure
     left right exceptional)))

(defun q1149022-ae-strongly-measurable-witness-p
    (real-type domain measurable measure
     space function representative)
  (and
   (q1149022-function-into-p
    domain space representative)
   (q1149022-strongly-measurable-p
    real-type domain measurable space representative)
   (q1149022-ae-equal-p
    real-type domain measurable measure
    function representative)))

(defun-sk q1149022-ae-strongly-measurable-p
    (real-type domain measurable measure space function)
  (exists (representative)
    (q1149022-ae-strongly-measurable-witness-p
     real-type domain measurable measure
     space function representative)))

(defun q1149022-ae-integrable-p
    (real-type domain measurable measure
     lintegral space function)
  (and
   (q1149022-function-into-p domain space function)
   (q1149022-ae-strongly-measurable-p
    real-type domain measurable measure space function)
   (not
    (equal
     (q1149022-lintegral-value
      lintegral
      (q1149022-function-norm
       real-type space function))
     :q1149022-top))))

;; Every term of F is an alpha-to-G function and is almost-everywhere
;; strongly measurable.

(defun-sk q1149022-function-sequence-into-p
    (domain space sequence)
  (forall (n)
    (implies
     (natp n)
     (q1149022-function-into-p
      domain space
      (q1149022-sequence-at sequence n)))))

(defun-sk q1149022-sequence-ae-strongly-measurable-p
    (real-type domain measurable measure space sequence)
  (forall (n)
    (implies
     (natp n)
     (q1149022-ae-strongly-measurable-p
      real-type domain measurable measure space
      (q1149022-sequence-at sequence n)))))

;; The domination hypothesis has a separately quantified null exceptional set
;; for each natural-number index, exactly as in forall n, almost everywhere x.

(defun-sk q1149022-dominated-off-set-p
    (real-type domain space sequence bound n exceptional)
  (forall (x)
    (implies
     (and
      (q1149022-member-p domain x)
      (not (q1149022-set-member-p exceptional x)))
     (q1149022-leq
      real-type
      (q1149022-norm
       space
       (q1149022-function-at
        (q1149022-sequence-at sequence n) x))
      (q1149022-function-at bound x)))))

(defun q1149022-dominated-index-witness-p
    (real-type domain measurable measure
     space sequence bound n exceptional)
  (and
   (q1149022-null-measurable-set-p
    real-type domain measurable measure exceptional)
   (q1149022-dominated-off-set-p
    real-type domain space sequence bound n exceptional)))

(defun-sk q1149022-dominated-at-index-p
    (real-type domain measurable measure
     space sequence bound n)
  (exists (exceptional)
    (q1149022-dominated-index-witness-p
     real-type domain measurable measure
     space sequence bound n exceptional)))

(defun-sk q1149022-sequence-dominated-p
    (real-type domain measurable measure
     space sequence bound)
  (forall (n)
    (implies
     (natp n)
     (q1149022-dominated-at-index-p
      real-type domain measurable measure
      space sequence bound n))))

;; Pointwise convergence is asserted outside one measurable null set.

(defun-sk q1149022-pointwise-converges-off-set-p
    (real-type domain space sequence limit exceptional)
  (forall (x)
    (implies
     (and
      (q1149022-member-p domain x)
      (not (q1149022-set-member-p exceptional x)))
     (q1149022-converges-p
      real-type space
      (q1149022-point-sequence sequence x)
      (q1149022-function-at limit x)))))

(defun q1149022-ae-pointwise-convergence-witness-p
    (real-type domain measurable measure
     space sequence limit exceptional)
  (and
   (q1149022-null-measurable-set-p
    real-type domain measurable measure exceptional)
   (q1149022-pointwise-converges-off-set-p
    real-type domain space sequence limit exceptional)))

(defun-sk q1149022-ae-pointwise-converges-p
    (real-type domain measurable measure
     space sequence limit)
  (exists (exceptional)
    (q1149022-ae-pointwise-convergence-witness-p
     real-type domain measurable measure
     space sequence limit exceptional)))

;; Both lower integration and Bochner integration are invariant under
;; almost-everywhere equality. The Bochner operation uses the same simple
;; function/L1 characterization as above, and returns zero for incomplete
;; codomains or nonintegrable functions, matching mathlib's total integral.

(defun-sk q1149022-lintegral-ae-congruence-p
    (real-type domain measurable measure lintegral)
  (forall (left right)
    (implies
     (q1149022-ae-equal-p
      real-type domain measurable measure left right)
     (equal
      (q1149022-lintegral-value lintegral left)
      (q1149022-lintegral-value lintegral right)))))

(defun-sk q1149022-bochner-integral-ae-operation-p
    (real-type domain measurable measure
     lintegral space integral)
  (forall (function other)
    (and
     (implies
      (q1149022-ae-equal-p
       real-type domain measurable measure function other)
      (equal
       (q1149022-bochner-integral-value integral function)
       (q1149022-bochner-integral-value integral other)))
     (implies
      (q1149022-function-into-p domain space function)
      (let ((value
             (q1149022-bochner-integral-value
              integral function)))
        (and
         (q1149022-member-p space value)
         (if
             (and
              (q1149022-complete-p real-type space)
              (q1149022-ae-integrable-p
               real-type domain measurable measure
               lintegral space function))
             (q1149022-bochner-approximation-exists-p
              real-type domain measurable measure lintegral
              space function value)
           (equal value (q1149022-zero space)))))))))

(defstub q1149022-integral-sequence
  (integral function-sequence) t)

(defun-sk q1149022-integral-sequence-laws-p ()
  (forall (integral function-sequence n)
    (equal
     (q1149022-sequence-at
      (q1149022-integral-sequence
       integral function-sequence)
      n)
     (q1149022-bochner-integral-value
      integral
      (q1149022-sequence-at function-sequence n)))))

;; Product carriers and measurable rectangles.

(defun-sk q1149022-product-member-represented-p
    (left-type right-type product-type object)
  (exists (left right)
    (and
     (q1149022-member-p left-type left)
     (q1149022-member-p right-type right)
     (equal
      object
      (q1149022-pair left-type right-type left right)))))

(defun-sk q1149022-pair-laws-p
    (left-type right-type product-type)
  (forall (left right left2 right2 object)
    (and
     (implies
      (and
       (q1149022-member-p left-type left)
       (q1149022-member-p right-type right))
      (q1149022-member-p
       product-type
       (q1149022-pair left-type right-type left right)))
     (implies
      (q1149022-member-p product-type object)
      (q1149022-product-member-represented-p
       left-type right-type product-type object))
     (implies
      (and
       (q1149022-member-p left-type left)
       (q1149022-member-p right-type right)
       (q1149022-member-p left-type left2)
       (q1149022-member-p right-type right2)
       (equal
        (q1149022-pair left-type right-type left right)
        (q1149022-pair left-type right-type left2 right2)))
      (and (equal left left2) (equal right right2))))))

(defun-sk q1149022-rectangle-set-laws-p
    (left-type right-type)
  (forall (left-set right-set left right)
    (iff
     (q1149022-set-member-p
      (q1149022-rectangle-set
       left-type right-type left-set right-set)
      (q1149022-pair left-type right-type left right))
     (and
      (q1149022-member-p left-type left)
      (q1149022-member-p right-type right)
      (q1149022-set-member-p left-set left)
      (q1149022-set-member-p right-set right)))))

(defun-sk q1149022-rectangles-measurable-p
    (left-type right-type left-measurable right-measurable
     product-measurable)
  (forall (left-set right-set)
    (implies
     (and
      (q1149022-family-member-p left-measurable left-set)
      (q1149022-family-member-p right-measurable right-set))
     (q1149022-family-member-p
      product-measurable
      (q1149022-rectangle-set
       left-type right-type left-set right-set)))))

(defun-sk q1149022-product-sigma-minimal-p
    (left-type right-type product-type
     left-measurable right-measurable product-measurable)
  (forall (candidate)
    (implies
     (and
      (q1149022-sigma-algebra-p product-type candidate)
      (q1149022-rectangles-measurable-p
       left-type right-type
       left-measurable right-measurable candidate))
     (q1149022-family-subset-p
      product-measurable candidate))))

(defun q1149022-product-measurable-space-p
    (left-type right-type product-type
     left-measurable right-measurable product-measurable)
  (and
   (q1149022-sigma-algebra-p left-type left-measurable)
   (q1149022-sigma-algebra-p right-type right-measurable)
   (q1149022-sigma-algebra-p product-type product-measurable)
   (q1149022-rectangles-measurable-p
    left-type right-type
    left-measurable right-measurable product-measurable)
   (q1149022-product-sigma-minimal-p
    left-type right-type product-type
    left-measurable right-measurable product-measurable)))

;; S-finite measures.

(defun q1149022-measure-sequence-partial-sum
    (real-type sequence set n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1149022-ennreal-finite
       (q1149022-zero real-type))
    (q1149022-ennreal-add
     real-type
     (q1149022-measure-sequence-partial-sum
      real-type sequence set (- n 1))
     (q1149022-measure-value
      (q1149022-sequence-at sequence (- n 1))
      set))))

(defun-sk q1149022-measure-sequence-upper-bound-p
    (real-type sequence set bound)
  (forall (n)
    (implies
     (natp n)
     (q1149022-ennreal-leq-p
      real-type
      (q1149022-measure-sequence-partial-sum
       real-type sequence set n)
      bound))))

(defun-sk q1149022-measure-sequence-series-value-p
    (real-type sequence set value)
  (forall (bound)
    (implies
     (q1149022-ennreal-p real-type bound)
     (iff
      (q1149022-measure-sequence-upper-bound-p
       real-type sequence set bound)
      (q1149022-ennreal-leq-p real-type value bound)))))

(defun q1149022-finite-measure-p
    (real-type domain measure)
  (not
   (equal
    (q1149022-measure-value
     measure (q1149022-full-set domain))
    :q1149022-top)))

(defun-sk q1149022-finite-measure-sequence-p
    (real-type domain measurable sequence)
  (forall (n)
    (implies
     (natp n)
     (let ((measure (q1149022-sequence-at sequence n)))
       (and
        (q1149022-measure-space-p
         real-type domain measurable measure)
        (q1149022-finite-measure-p
         real-type domain measure))))))

(defun-sk q1149022-measure-sequence-sums-to-p
    (real-type domain measurable sequence measure)
  (forall (set)
    (implies
     (q1149022-family-member-p measurable set)
     (q1149022-measure-sequence-series-value-p
      real-type sequence set
      (q1149022-measure-value measure set)))))

(defun q1149022-sfinite-witness-p
    (real-type domain measurable measure sequence)
  (and
   (q1149022-finite-measure-sequence-p
    real-type domain measurable sequence)
   (q1149022-measure-sequence-sums-to-p
    real-type domain measurable sequence measure)))

(defun-sk q1149022-sfinite-measure-p
    (real-type domain measurable measure)
  (exists (sequence)
    (q1149022-sfinite-witness-p
     real-type domain measurable measure sequence)))

;; The product measure is characterized on every measurable set by integrating
;; the right-section measures. This is the defining product-measure formula
;; used by mathlib for s-finite measures; rectangle values alone would not
;; uniquely characterize a product of arbitrary s-finite measures.

(defun-sk q1149022-section-set-laws-p
    (left-type right-type)
  (forall (set left right)
    (iff
     (q1149022-set-member-p
      (q1149022-section-set left-type right-type set left)
      right)
     (and
      (q1149022-member-p left-type left)
      (q1149022-member-p right-type right)
      (q1149022-set-member-p
       set
       (q1149022-pair
        left-type right-type left right))))))

(defun-sk q1149022-section-measure-function-values-p
    (left-type right-type right-measure)
  (forall (set left)
    (implies
     (q1149022-member-p left-type left)
     (equal
      (q1149022-function-at
       (q1149022-section-measure-function
        left-type right-type right-measure set)
       left)
      (q1149022-measure-value
       right-measure
       (q1149022-section-set
        left-type right-type set left))))))

(defun-sk q1149022-section-measure-functions-measurable-p
    (real-type left-type right-type
     left-measurable product-measurable right-measure)
  (forall (set)
    (implies
     (q1149022-family-member-p product-measurable set)
     (let ((section-measure-function
            (q1149022-section-measure-function
             left-type right-type right-measure set)))
       (and
        (q1149022-ennreal-function-p
         real-type left-type section-measure-function)
        (q1149022-measurable-ennreal-function-p
         real-type left-type left-measurable
         section-measure-function))))))

(defun q1149022-section-measure-function-laws-p
    (real-type left-type right-type
     left-measurable product-measurable right-measure)
  (and
   (q1149022-section-measure-function-values-p
    left-type right-type right-measure)
   (q1149022-section-measure-functions-measurable-p
    real-type left-type right-type
    left-measurable product-measurable right-measure)))

(defun-sk q1149022-product-measure-values-p
    (left-type right-type product-measurable
     right-measure left-ennreal-lintegral product-measure)
  (forall (set)
    (implies
     (q1149022-family-member-p product-measurable set)
     (equal
      (q1149022-measure-value product-measure set)
      (q1149022-ennreal-lintegral-value
       left-ennreal-lintegral
       (q1149022-section-measure-function
        left-type right-type right-measure set))))))

(defun q1149022-product-measure-p
    (real-type left-type right-type product-type
     left-measurable right-measurable product-measurable
     left-measure right-measure
     left-ennreal-lintegral product-measure)
  (and
   (q1149022-measure-space-p
    real-type product-type product-measurable product-measure)
   (q1149022-ennreal-lintegral-operation-p
    real-type left-type left-measurable
    left-measure left-ennreal-lintegral)
   (q1149022-product-measure-values-p
    left-type right-type product-measurable
    right-measure left-ennreal-lintegral product-measure)))

;; Sections and the function of inner Bochner integrals.

(defun-sk q1149022-section-and-iterated-laws-p
    (left-type right-type)
  (forall (function integral left right)
    (and
     (equal
      (q1149022-function-at
       (q1149022-section-right
        left-type right-type function left)
       right)
      (q1149022-function-at
       function
       (q1149022-pair left-type right-type left right)))
     (equal
      (q1149022-function-at
       (q1149022-iterated-integral-function
        left-type right-type integral function)
       left)
      (q1149022-bochner-integral-value
       integral
       (q1149022-section-right
        left-type right-type function left))))))

;; This predicate is exactly the indexed Lean theorem
;; MeasureTheory.integral_prod.

(defun thousand-theorems-q1149022-fubini-s-theorem-statement
    (real-type left-type right-type product-type space
     left-measurable right-measurable product-measurable
     left-measure right-measure product-measure
     left-ennreal-lintegral
     left-lintegral right-lintegral product-lintegral
     left-integral right-integral product-integral function)
  (implies
   (and
    (q1149022-real-field-p real-type)
    (q1149022-real-normed-space-p real-type space)
    (q1149022-basic-set-constructor-laws-p left-type)
    (q1149022-basic-set-constructor-laws-p right-type)
    (q1149022-basic-set-constructor-laws-p product-type)
    (q1149022-set-constructor-laws-p real-type real-type)
    (q1149022-set-constructor-laws-p real-type space)
    (q1149022-pair-laws-p
     left-type right-type product-type)
    (q1149022-rectangle-set-laws-p
     left-type right-type)
    (q1149022-section-set-laws-p
     left-type right-type)
    (q1149022-section-measure-function-laws-p
     real-type left-type right-type
     left-measurable product-measurable right-measure)
    (q1149022-section-and-iterated-laws-p
     left-type right-type)
    (q1149022-fiber-set-law-p left-type)
    (q1149022-fiber-set-law-p right-type)
    (q1149022-fiber-set-law-p product-type)
    (q1149022-preimage-set-law-p left-type)
    (q1149022-preimage-set-law-p right-type)
    (q1149022-preimage-set-law-p product-type)
    (q1149022-function-constructor-laws-p real-type)
    (q1149022-point-sequence-laws-p)
    (q1149022-simple-integral-sequence-laws-p)
    (q1149022-measure-space-p
     real-type left-type left-measurable left-measure)
    (q1149022-measure-space-p
     real-type right-type right-measurable right-measure)
    (q1149022-sfinite-measure-p
     real-type left-type left-measurable left-measure)
    (q1149022-sfinite-measure-p
     real-type right-type right-measurable right-measure)
    (q1149022-product-measurable-space-p
     left-type right-type product-type
     left-measurable right-measurable product-measurable)
    (q1149022-product-measure-p
     real-type left-type right-type product-type
     left-measurable right-measurable product-measurable
     left-measure right-measure
     left-ennreal-lintegral product-measure)
    (q1149022-lintegral-laws-p
     real-type left-type left-measurable
     left-measure left-lintegral)
    (q1149022-lintegral-supremum-laws-p
     real-type left-type left-measurable
     left-measure left-lintegral)
    (q1149022-lintegral-ae-congruence-p
     real-type left-type left-measurable
     left-measure left-lintegral)
    (q1149022-lintegral-laws-p
     real-type right-type right-measurable
     right-measure right-lintegral)
    (q1149022-lintegral-supremum-laws-p
     real-type right-type right-measurable
     right-measure right-lintegral)
    (q1149022-lintegral-ae-congruence-p
     real-type right-type right-measurable
     right-measure right-lintegral)
    (q1149022-lintegral-laws-p
     real-type product-type product-measurable
     product-measure product-lintegral)
    (q1149022-lintegral-supremum-laws-p
     real-type product-type product-measurable
     product-measure product-lintegral)
    (q1149022-lintegral-ae-congruence-p
     real-type product-type product-measurable
     product-measure product-lintegral)
    (q1149022-bochner-integral-ae-operation-p
     real-type left-type left-measurable left-measure
     left-lintegral space left-integral)
    (q1149022-bochner-integral-ae-operation-p
     real-type right-type right-measurable right-measure
     right-lintegral space right-integral)
    (q1149022-bochner-integral-ae-operation-p
     real-type product-type product-measurable product-measure
     product-lintegral space product-integral)
    (q1149022-function-into-p
     product-type space function)
    (q1149022-ae-integrable-p
     real-type product-type product-measurable product-measure
     product-lintegral space function))
   (equal
    (q1149022-bochner-integral-value
     product-integral function)
    (q1149022-bochner-integral-value
     left-integral
     (q1149022-iterated-integral-function
      left-type right-type right-integral function)))))

(value-triple :itpeval-statement-checked)
:q
