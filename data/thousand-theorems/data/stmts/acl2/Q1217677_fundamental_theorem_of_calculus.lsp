;; Statement-only formalization of thousand-theorems corpus artifact Q1217677,
;; "Fundamental theorem of calculus": for Banach-space-valued functions on
;; real intervals, an almost-everywhere endpoint limit gives the strict
;; derivative of the indefinite Bochner integral, and an integrable right
;; derivative integrates to the endpoint difference. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Mathematical objects are unrestricted ACL2 objects. The conservative
;; interfaces below only provide application and constructor symbols; every
;; real-field, normed-space, measure, measurability, convergence, and Bochner
;; integration law used by the statement is imposed explicitly by predicates.

(defstub q1217677-member-p (type object) t)
(defstub q1217677-zero (type) t)
(defstub q1217677-one (type) t)
(defstub q1217677-add (type left right) t)
(defstub q1217677-multiply (type left right) t)
(defstub q1217677-negate (type object) t)
(defstub q1217677-inverse (type object) t)
(defstub q1217677-less (type left right) t)
(defstub q1217677-norm (type object) t)
(defstub q1217677-smul (scalar-type space scalar vector) t)
(defstub q1217677-star (scalar-type scalar) t)
(defstub q1217677-real-part (real-type scalar-type scalar) t)
(defstub q1217677-imag-part (real-type scalar-type scalar) t)
(defstub q1217677-of-real (real-type scalar-type real) t)
(defstub q1217677-imaginary-unit (scalar-type) t)
(defstub q1217677-inner (scalar-type space left right) t)
(defstub q1217677-function-at (function argument) t)
(defstub q1217677-sequence-at (sequence index) t)
(defstub q1217677-basis-at (basis index) t)
(defstub q1217677-coordinate (coordinates vector index) t)
(defstub q1217677-derivative-function (derivatives function multiindex) t)
(defstub q1217677-fourier-function (fourier function) t)
(defstub q1217677-character-value (fourier-char real) t)
(defstub q1217677-set-member-p (set object) t)
(defstub q1217677-family-member-p (family set) t)
(defstub q1217677-open-ball-set (space center radius) t)
(defstub q1217677-preimage-set (function set) t)
(defstub q1217677-complement-set (carrier set) t)
(defstub q1217677-countable-union-set (carrier sequence) t)
(defstub q1217677-translate-set (space set shift) t)
(defstub q1217677-unit-cell-set (space basis coordinates dimension) t)
(defstub q1217677-fiber-set (function value) t)
(defstub q1217677-simple-values (function) t)
(defstub q1217677-indicator-function (real-type set) t)
(defstub q1217677-function-add (type left right) t)
(defstub q1217677-function-difference (type left right) t)
(defstub q1217677-function-norm (real-type type function) t)
(defstub q1217677-inner-integrand (scalar-type space left right) t)
(defstub q1217677-fourier-integrand
  (real-type scalar-type domain space fourier-char function frequency) t)
(defstub q1217677-measure-value (measure set) t)
(defstub q1217677-lintegral-value (lintegral function) t)
(defstub q1217677-bochner-integral-value (integral function) t)
(defstub q1217677-full-set (carrier) t)
(defstub q1217677-point-sequence (function-sequence point) t)
(defstub q1217677-simple-integral-sequence
  (real-type domain space measure function-sequence) t)
(defstub q1217677-closed-interval-set (left right) t)
(defstub q1217677-open-interval-set (left right) t)
(defstub q1217677-right-ray-set (left) t)
(defstub q1217677-half-open-interval-set (left right) t)
(defstub q1217677-restricted-function (space function set) t)

(defun q1217677-positive-p (real-type x)
  (q1217677-less real-type (q1217677-zero real-type) x))

(defun q1217677-leq (real-type x y)
  (not (q1217677-less real-type y x)))

(defun q1217677-abs (real-type x)
  (if (q1217677-less real-type x (q1217677-zero real-type))
      (q1217677-negate real-type x)
    x))

(defun q1217677-natural-cast (type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1217677-zero type)
    (q1217677-add
     type
     (q1217677-one type)
     (q1217677-natural-cast type (- n 1)))))

(defun q1217677-integer-cast (type n)
  (if (and (integerp n) (< n 0))
      (q1217677-negate
       type
       (q1217677-natural-cast type (- n)))
    (q1217677-natural-cast type (nfix n))))

(defun q1217677-real-power (real-type x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1217677-one real-type)
    (q1217677-multiply
     real-type x
     (q1217677-real-power real-type x (- n 1)))))

(defun q1217677-vector-sum
    (real-type space basis coordinates vector n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1217677-zero space)
    (let ((i (- n 1)))
      (q1217677-add
       space
       (q1217677-vector-sum
        real-type space basis coordinates vector i)
       (q1217677-smul
        real-type space
        (q1217677-coordinate coordinates vector i)
        (q1217677-basis-at basis i))))))

(defun q1217677-zero-multiindex (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (q1217677-zero-multiindex (- n 1)))))

(defun q1217677-natural-list-p (alpha n)
  (if (zp n)
      (equal alpha nil)
    (and
     (consp alpha)
     (natp (car alpha))
     (q1217677-natural-list-p (cdr alpha) (- n 1)))))

(defun q1217677-increment-multiindex (alpha i)
  (if (consp alpha)
      (if (zp i)
          (cons (+ 1 (nfix (car alpha))) (cdr alpha))
        (cons
         (car alpha)
         (q1217677-increment-multiindex (cdr alpha) (- i 1))))
    nil))

(defun q1217677-multiindex-degree (alpha)
  (if (consp alpha)
      (+ (nfix (car alpha))
         (q1217677-multiindex-degree (cdr alpha)))
    0))

;; Complete ordered real field and its canonical complexification.

(defun-sk q1217677-field-laws-p (type)
  (forall (x y z)
    (implies
     (and
      (q1217677-member-p type x)
      (q1217677-member-p type y)
      (q1217677-member-p type z))
     (and
      (q1217677-member-p type (q1217677-add type x y))
      (q1217677-member-p type (q1217677-multiply type x y))
      (q1217677-member-p type (q1217677-negate type x))
      (implies
       (not (equal x (q1217677-zero type)))
       (q1217677-member-p type (q1217677-inverse type x)))
      (equal
       (q1217677-add type (q1217677-add type x y) z)
       (q1217677-add type x (q1217677-add type y z)))
      (equal (q1217677-add type x y) (q1217677-add type y x))
      (equal (q1217677-add type x (q1217677-zero type)) x)
      (equal
       (q1217677-add type x (q1217677-negate type x))
       (q1217677-zero type))
      (equal
       (q1217677-multiply type (q1217677-multiply type x y) z)
       (q1217677-multiply type x (q1217677-multiply type y z)))
      (equal
       (q1217677-multiply type x y)
       (q1217677-multiply type y x))
      (equal (q1217677-multiply type x (q1217677-one type)) x)
      (implies
       (not (equal x (q1217677-zero type)))
       (equal
        (q1217677-multiply type x (q1217677-inverse type x))
        (q1217677-one type)))
      (equal
       (q1217677-multiply type x (q1217677-add type y z))
       (q1217677-add
        type
        (q1217677-multiply type x y)
        (q1217677-multiply type x z)))))))

(defun-sk q1217677-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q1217677-member-p real-type x)
      (q1217677-member-p real-type y)
      (q1217677-member-p real-type z))
     (and
      (not (q1217677-less real-type x x))
      (or
       (q1217677-less real-type x y)
       (equal x y)
       (q1217677-less real-type y x))
      (implies
       (and
        (q1217677-less real-type x y)
        (q1217677-less real-type y z))
       (q1217677-less real-type x z))
      (implies
       (q1217677-less real-type x y)
       (q1217677-less
        real-type
        (q1217677-add real-type x z)
        (q1217677-add real-type y z)))
      (implies
       (and
        (q1217677-positive-p real-type x)
        (q1217677-positive-p real-type y))
       (q1217677-positive-p
        real-type
        (q1217677-multiply real-type x y)))))))

(defun q1217677-distance
    (real-type type x y)
  (declare (ignore real-type))
  (q1217677-norm
   type
   (q1217677-add type x (q1217677-negate type y))))

(defun-sk q1217677-norm-values-p (real-type type)
  (forall (x)
    (implies
     (q1217677-member-p type x)
     (and
      (q1217677-member-p real-type (q1217677-norm type x))
      (q1217677-leq
       real-type
       (q1217677-zero real-type)
       (q1217677-norm type x))
      (iff
       (equal
        (q1217677-norm type x)
        (q1217677-zero real-type))
       (equal x (q1217677-zero type)))))))

(defun-sk q1217677-norm-triangle-p (real-type type)
  (forall (x y)
    (implies
     (and
      (q1217677-member-p type x)
      (q1217677-member-p type y))
     (q1217677-leq
      real-type
      (q1217677-norm type (q1217677-add type x y))
      (q1217677-add
       real-type
       (q1217677-norm type x)
       (q1217677-norm type y))))))

(defun q1217677-norm-laws-p (real-type type)
  (and
   (q1217677-norm-values-p real-type type)
   (q1217677-norm-triangle-p real-type type)))

(defun-sk q1217677-convergence-tail-p
    (real-type type sequence limit epsilon start)
  (forall (n)
    (implies
     (and (natp n) (natp start) (<= start n))
     (q1217677-less
      real-type
      (q1217677-distance
       real-type type
       (q1217677-sequence-at sequence n)
       limit)
      epsilon))))

(defun-sk q1217677-convergence-start-p
    (real-type type sequence limit epsilon)
  (exists (start)
    (and
     (natp start)
     (q1217677-convergence-tail-p
      real-type type sequence limit epsilon start))))

(defun-sk q1217677-converges-p
    (real-type type sequence limit)
  (forall (epsilon)
    (implies
     (and
      (q1217677-member-p real-type epsilon)
      (q1217677-positive-p real-type epsilon))
     (q1217677-convergence-start-p
      real-type type sequence limit epsilon))))

(defun-sk q1217677-cauchy-tail-p
    (real-type type sequence epsilon start)
  (forall (m n)
    (implies
     (and
      (natp m) (natp n) (natp start)
      (<= start m) (<= start n))
     (q1217677-less
      real-type
      (q1217677-distance
       real-type type
       (q1217677-sequence-at sequence m)
       (q1217677-sequence-at sequence n))
      epsilon))))

(defun-sk q1217677-cauchy-start-p
    (real-type type sequence epsilon)
  (exists (start)
    (and
     (natp start)
     (q1217677-cauchy-tail-p
      real-type type sequence epsilon start))))

(defun-sk q1217677-cauchy-p (real-type type sequence)
  (forall (epsilon)
    (implies
     (and
      (q1217677-member-p real-type epsilon)
      (q1217677-positive-p real-type epsilon))
     (q1217677-cauchy-start-p
      real-type type sequence epsilon))))

(defun-sk q1217677-sequence-in-type-p (type sequence)
  (forall (n)
    (implies
     (natp n)
     (q1217677-member-p
      type
      (q1217677-sequence-at sequence n)))))

(defun-sk q1217677-limit-exists-p
    (real-type type sequence)
  (exists (limit)
    (and
     (q1217677-member-p type limit)
     (q1217677-converges-p
      real-type type sequence limit))))

(defun-sk q1217677-complete-p (real-type type)
  (forall (sequence)
    (implies
     (and
      (q1217677-sequence-in-type-p type sequence)
      (q1217677-cauchy-p real-type type sequence))
     (q1217677-limit-exists-p
      real-type type sequence))))

(defun-sk q1217677-archimedean-witness-p (real-type x)
  (exists (n)
    (and
     (natp n)
     (q1217677-less
      real-type x
      (q1217677-natural-cast real-type n)))))

(defun-sk q1217677-archimedean-p (real-type)
  (forall (x)
    (implies
     (q1217677-member-p real-type x)
     (q1217677-archimedean-witness-p real-type x))))

(defun-sk q1217677-real-norm-laws-p (real-type)
  (forall (x)
    (implies
     (q1217677-member-p real-type x)
     (and
      (equal
       (q1217677-norm real-type x)
       (q1217677-abs real-type x))
      (equal (q1217677-star real-type x) x)
      (equal
       (q1217677-real-part real-type real-type x)
       x)
      (equal
       (q1217677-imag-part real-type real-type x)
       (q1217677-zero real-type))
      (equal
       (q1217677-of-real real-type real-type x)
       x)))))

(defun q1217677-real-field-p (real-type)
  (and
   (q1217677-member-p real-type (q1217677-zero real-type))
   (q1217677-member-p real-type (q1217677-one real-type))
   (not
    (equal
     (q1217677-zero real-type)
     (q1217677-one real-type)))
   (q1217677-field-laws-p real-type)
   (q1217677-order-laws-p real-type)
   (q1217677-positive-p real-type (q1217677-one real-type))
   (q1217677-real-norm-laws-p real-type)
   (q1217677-complete-p real-type real-type)
   (q1217677-archimedean-p real-type)))

;; Real and complex inner-product spaces.

(defun-sk q1217677-vector-space-laws-p
    (scalar-type space)
  (forall (a b x y z)
    (implies
     (and
      (q1217677-member-p scalar-type a)
      (q1217677-member-p scalar-type b)
      (q1217677-member-p space x)
      (q1217677-member-p space y)
      (q1217677-member-p space z))
     (and
      (q1217677-member-p space (q1217677-add space x y))
      (q1217677-member-p space (q1217677-negate space x))
      (q1217677-member-p
       space (q1217677-smul scalar-type space a x))
      (equal
       (q1217677-add space (q1217677-add space x y) z)
       (q1217677-add space x (q1217677-add space y z)))
      (equal (q1217677-add space x y) (q1217677-add space y x))
      (equal (q1217677-add space x (q1217677-zero space)) x)
      (equal
       (q1217677-add space x (q1217677-negate space x))
       (q1217677-zero space))
      (equal
       (q1217677-smul
        scalar-type space (q1217677-one scalar-type) x)
       x)
      (equal
       (q1217677-smul
        scalar-type space
        (q1217677-multiply scalar-type a b) x)
       (q1217677-smul
        scalar-type space a
        (q1217677-smul scalar-type space b x)))
      (equal
       (q1217677-smul
        scalar-type space
        (q1217677-add scalar-type a b) x)
       (q1217677-add
        space
        (q1217677-smul scalar-type space a x)
        (q1217677-smul scalar-type space b x)))
      (equal
       (q1217677-smul
        scalar-type space a (q1217677-add space x y))
       (q1217677-add
        space
        (q1217677-smul scalar-type space a x)
        (q1217677-smul scalar-type space a y)))))))

(defun-sk q1217677-normed-space-laws-p
    (real-type scalar-type space)
  (forall (a x)
    (implies
     (and
      (q1217677-member-p scalar-type a)
      (q1217677-member-p space x))
     (equal
      (q1217677-norm
       space
       (q1217677-smul scalar-type space a x))
      (q1217677-multiply
       real-type
       (q1217677-norm scalar-type a)
       (q1217677-norm space x))))))

;; Borel sigma algebra and normalized translation-invariant volume.

(defun-sk q1217677-countable-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q1217677-set-member-p
      (q1217677-sequence-at sequence n) x))))

(defun-sk q1217677-valid-set-p (space set)
  (forall (x)
    (implies
     (q1217677-set-member-p set x)
     (q1217677-member-p space x))))

(defun-sk q1217677-sets-equal-on-p (space left right)
  (forall (x)
    (implies
     (q1217677-member-p space x)
     (iff
      (q1217677-set-member-p left x)
      (q1217677-set-member-p right x)))))

(defun-sk q1217677-empty-on-p (space set)
  (forall (x)
    (implies
     (q1217677-member-p space x)
     (not (q1217677-set-member-p set x)))))

(defun-sk q1217677-full-set-law-p (space)
  (forall (x)
    (iff
     (q1217677-set-member-p
      (q1217677-full-set space) x)
     (q1217677-member-p space x))))

(defun-sk q1217677-complement-set-law-p (space)
  (forall (set x)
    (iff
     (q1217677-set-member-p
      (q1217677-complement-set space set) x)
     (and
      (q1217677-member-p space x)
      (not (q1217677-set-member-p set x))))))

(defun-sk q1217677-countable-union-set-law-p (space)
  (forall (sequence x)
    (iff
     (q1217677-set-member-p
      (q1217677-countable-union-set space sequence) x)
     (and
      (q1217677-member-p space x)
      (q1217677-countable-union-member-p sequence x)))))

(defun-sk q1217677-open-ball-set-law-p (real-type space)
  (forall (center radius x)
    (iff
     (q1217677-set-member-p
      (q1217677-open-ball-set space center radius) x)
     (and
      (q1217677-member-p space x)
      (q1217677-member-p space center)
      (q1217677-member-p real-type radius)
      (q1217677-less
       real-type
       (q1217677-distance real-type space x center)
       radius)))))

(defun-sk q1217677-preimage-set-law-p (domain)
  (forall (function set x)
    (iff
     (q1217677-set-member-p
      (q1217677-preimage-set function set) x)
     (and
      (q1217677-member-p domain x)
      (q1217677-set-member-p
       set (q1217677-function-at function x))))))

(defun-sk q1217677-translate-set-law-p (space)
  (forall (set shift x)
    (iff
     (q1217677-set-member-p
      (q1217677-translate-set space set shift) x)
     (and
      (q1217677-member-p space x)
      (q1217677-set-member-p
       set
       (q1217677-add
        space x (q1217677-negate space shift)))))))

(defun q1217677-set-constructor-laws-p
    (real-type space)
  (and
   (q1217677-full-set-law-p space)
   (q1217677-complement-set-law-p space)
   (q1217677-countable-union-set-law-p space)
   (q1217677-open-ball-set-law-p real-type space)
   (q1217677-translate-set-law-p space)))

(defun-sk q1217677-sequence-measurable-p (family sequence)
  (forall (n)
    (implies
     (natp n)
     (q1217677-family-member-p
      family
      (q1217677-sequence-at sequence n)))))

(defun-sk q1217677-family-valid-sets-p (space family)
  (forall (set)
    (implies
     (q1217677-family-member-p family set)
     (q1217677-valid-set-p space set))))

(defun-sk q1217677-family-extensional-p (space family)
  (forall (left right)
    (implies
     (and
      (q1217677-family-member-p family left)
      (q1217677-valid-set-p space right)
      (q1217677-sets-equal-on-p space left right))
     (q1217677-family-member-p family right))))

(defun-sk q1217677-sigma-algebra-closure-p (space family)
  (forall (set sequence)
    (and
     (q1217677-family-member-p family (q1217677-full-set space))
     (implies
      (q1217677-family-member-p family set)
      (q1217677-family-member-p
       family (q1217677-complement-set space set)))
     (implies
      (q1217677-sequence-measurable-p family sequence)
      (q1217677-family-member-p
       family
       (q1217677-countable-union-set space sequence))))))

(defun q1217677-sigma-algebra-p (space family)
  (and
   (q1217677-family-valid-sets-p space family)
   (q1217677-family-extensional-p space family)
   (q1217677-sigma-algebra-closure-p space family)))

(defun-sk q1217677-balls-measurable-p
    (real-type space family)
  (forall (center radius)
    (implies
     (and
      (q1217677-member-p space center)
      (q1217677-member-p real-type radius)
      (q1217677-positive-p real-type radius))
     (q1217677-family-member-p
      family
      (q1217677-open-ball-set space center radius)))))

(defun-sk q1217677-family-subset-p (left right)
  (forall (set)
    (implies
     (q1217677-family-member-p left set)
     (q1217677-family-member-p right set))))

(defun-sk q1217677-borel-minimal-p
    (real-type space borel)
  (forall (candidate)
    (implies
     (and
      (q1217677-sigma-algebra-p space candidate)
      (q1217677-balls-measurable-p
       real-type space candidate))
     (q1217677-family-subset-p borel candidate))))

(defun q1217677-borel-space-p
    (real-type space borel)
  (and
   (q1217677-sigma-algebra-p space borel)
   (q1217677-balls-measurable-p real-type space borel)
   (q1217677-borel-minimal-p real-type space borel)))

(defun q1217677-ennreal-p (real-type x)
  (or
   (equal x :q1217677-top)
   (and
    (consp x)
    (equal (car x) :q1217677-finite)
    (q1217677-member-p real-type (cdr x))
    (q1217677-leq
     real-type (q1217677-zero real-type) (cdr x)))))

(defun q1217677-ennreal-finite (x)
  (cons :q1217677-finite x))

(defun q1217677-ennreal-add (real-type x y)
  (if (or
       (equal x :q1217677-top)
       (equal y :q1217677-top))
      :q1217677-top
    (q1217677-ennreal-finite
     (q1217677-add real-type (cdr x) (cdr y)))))

(defun q1217677-ennreal-leq-p (real-type x y)
  (or
   (equal y :q1217677-top)
   (and
    (not (equal x :q1217677-top))
    (q1217677-leq real-type (cdr x) (cdr y)))))

(defun-sk q1217677-disjoint-sequence-p
    (space sequence)
  (forall (i j x)
    (implies
     (and
      (natp i) (natp j)
      (not (equal i j))
      (q1217677-member-p space x))
     (not
      (and
       (q1217677-set-member-p
        (q1217677-sequence-at sequence i) x)
       (q1217677-set-member-p
        (q1217677-sequence-at sequence j) x))))))

(defun q1217677-ennreal-partial-sum
    (real-type measure sequence n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1217677-ennreal-finite (q1217677-zero real-type))
    (q1217677-ennreal-add
     real-type
     (q1217677-ennreal-partial-sum
      real-type measure sequence (- n 1))
     (q1217677-measure-value
      measure
      (q1217677-sequence-at sequence (- n 1))))))

(defun-sk q1217677-ennreal-upper-bound-p
    (real-type measure sequence bound)
  (forall (n)
    (implies
     (natp n)
     (q1217677-ennreal-leq-p
      real-type
      (q1217677-ennreal-partial-sum
       real-type measure sequence n)
      bound))))

(defun-sk q1217677-ennreal-series-value-p
    (real-type measure sequence value)
  (forall (bound)
    (iff
     (q1217677-ennreal-upper-bound-p
      real-type measure sequence bound)
     (q1217677-ennreal-leq-p real-type value bound))))

(defun-sk q1217677-countable-additivity-p
    (real-type space measurable measure)
  (forall (sequence)
    (implies
     (and
      (q1217677-sequence-measurable-p measurable sequence)
      (q1217677-disjoint-sequence-p space sequence))
     (q1217677-ennreal-series-value-p
      real-type
      measure
      sequence
      (q1217677-measure-value
       measure
       (q1217677-countable-union-set space sequence))))))

(defun-sk q1217677-measure-values-p (real-type measure)
  (forall (set)
    (q1217677-ennreal-p
     real-type
     (q1217677-measure-value measure set))))

(defun-sk q1217677-measure-extensional-p (space measure)
  (forall (left right)
    (implies
     (and
      (q1217677-valid-set-p space left)
      (q1217677-valid-set-p space right)
      (q1217677-sets-equal-on-p space left right))
     (equal
      (q1217677-measure-value measure left)
      (q1217677-measure-value measure right)))))

(defun-sk q1217677-empty-measurable-zero-p
    (real-type space measurable measure)
  (forall (set)
    (implies
     (and
      (q1217677-family-member-p measurable set)
      (q1217677-empty-on-p space set))
     (equal
      (q1217677-measure-value measure set)
      (q1217677-ennreal-finite
       (q1217677-zero real-type))))))

(defun q1217677-measure-space-p
    (real-type space measurable measure)
  (and
   (q1217677-sigma-algebra-p space measurable)
   (q1217677-measure-values-p real-type measure)
   (q1217677-measure-extensional-p space measure)
   (q1217677-empty-measurable-zero-p
    real-type space measurable measure)
   (equal
    (q1217677-measure-value
     measure
     (q1217677-complement-set
      space (q1217677-full-set space)))
    (q1217677-ennreal-finite (q1217677-zero real-type)))
   (q1217677-countable-additivity-p
    real-type space measurable measure)))

(defun q1217677-unit-coordinates-p
    (real-type coordinates x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (let ((c
           (q1217677-coordinate
            coordinates x (- n 1))))
      (and
       (q1217677-leq
        real-type (q1217677-zero real-type) c)
       (q1217677-less
        real-type c (q1217677-one real-type))
       (q1217677-unit-coordinates-p
        real-type coordinates x (- n 1))))))

(defun-sk q1217677-unit-cell-coordinate-p
    (real-type space basis coordinates dimension)
  (forall (x)
    (iff
     (q1217677-set-member-p
      (q1217677-unit-cell-set
       space basis coordinates dimension)
      x)
     (and
      (q1217677-member-p space x)
      (q1217677-unit-coordinates-p
       real-type coordinates x dimension)))))

(defun-sk q1217677-translation-invariant-p
    (space measurable measure)
  (forall (set shift)
    (implies
     (and
      (q1217677-family-member-p measurable set)
      (q1217677-member-p space shift))
     (equal
      (q1217677-measure-value
       measure
       (q1217677-translate-set space set shift))
      (q1217677-measure-value measure set)))))

(defun q1217677-volume-space-p
    (real-type space basis coordinates dimension measurable measure)
  (and
   (q1217677-borel-space-p real-type space measurable)
   (q1217677-measure-space-p
    real-type space measurable measure)
   (q1217677-unit-cell-coordinate-p
    real-type space basis coordinates dimension)
   (q1217677-family-member-p
    measurable
    (q1217677-unit-cell-set
     space basis coordinates dimension))
   (equal
    (q1217677-measure-value
     measure
     (q1217677-unit-cell-set
      space basis coordinates dimension))
    (q1217677-ennreal-finite
     (q1217677-one real-type)))
   (q1217677-translation-invariant-p
    space measurable measure)))

;; Lebesgue lower integration and Bochner integration.

(defun-sk q1217677-function-into-p
    (domain codomain function)
  (forall (x)
    (implies
     (q1217677-member-p domain x)
     (q1217677-member-p
      codomain
      (q1217677-function-at function x)))))

(defun-sk q1217677-continuous-at-delta-p
    (real-type domain codomain function x epsilon delta)
  (forall (y)
    (implies
     (and
      (q1217677-member-p domain y)
      (q1217677-less
       real-type
       (q1217677-distance real-type domain y x)
       delta))
     (q1217677-less
      real-type
      (q1217677-distance
       real-type codomain
       (q1217677-function-at function y)
       (q1217677-function-at function x))
      epsilon))))

(defun-sk q1217677-continuous-at-epsilon-p
    (real-type domain codomain function x epsilon)
  (exists (delta)
    (and
     (q1217677-member-p real-type delta)
     (q1217677-positive-p real-type delta)
     (q1217677-continuous-at-delta-p
      real-type domain codomain function x epsilon delta))))

(defun-sk q1217677-continuous-function-p
    (real-type domain codomain function)
  (forall (x epsilon)
    (implies
     (and
      (q1217677-member-p domain x)
      (q1217677-member-p real-type epsilon)
      (q1217677-positive-p real-type epsilon))
     (q1217677-continuous-at-epsilon-p
      real-type domain codomain function x epsilon))))

(defun-sk q1217677-function-constructor-laws-p
    (real-type)
  (forall (type f g set value x)
    (and
     (equal
      (q1217677-function-at
       (q1217677-function-add type f g) x)
      (q1217677-add
       type
       (q1217677-function-at f x)
       (q1217677-function-at g x)))
     (equal
      (q1217677-function-at
       (q1217677-function-difference type f g) x)
      (q1217677-add
       type
       (q1217677-function-at f x)
       (q1217677-negate
        type (q1217677-function-at g x))))
     (equal
      (q1217677-function-at
       (q1217677-function-norm real-type type f) x)
      (q1217677-norm type (q1217677-function-at f x)))
     (equal
      (q1217677-function-at
       (q1217677-indicator-function real-type set) x)
      (if (q1217677-set-member-p set x)
          (q1217677-one real-type)
        (q1217677-zero real-type))))))

(defun-sk q1217677-fiber-set-law-p (domain)
  (forall (function value x)
    (iff
     (q1217677-set-member-p
      (q1217677-fiber-set function value)
      x)
     (and
      (q1217677-member-p domain x)
      (equal (q1217677-function-at function x) value)))))

(defun-sk q1217677-measurable-function-p
    (real-type domain measurable codomain function)
  (forall (center radius)
    (implies
     (and
      (q1217677-member-p codomain center)
      (q1217677-member-p real-type radius)
      (q1217677-positive-p real-type radius))
     (q1217677-family-member-p
      measurable
      (q1217677-preimage-set
       function
       (q1217677-open-ball-set
        codomain center radius))))))

(defun-sk q1217677-nonnegative-values-p
    (real-type domain function)
  (forall (x)
    (implies
     (q1217677-member-p domain x)
     (q1217677-leq
      real-type
      (q1217677-zero real-type)
      (q1217677-function-at function x)))))

(defun q1217677-nonnegative-measurable-p
    (real-type domain measurable function)
  (and
   (q1217677-function-into-p
    domain real-type function)
   (q1217677-measurable-function-p
    real-type domain measurable real-type function)
   (q1217677-nonnegative-values-p
    real-type domain function)))

(defun-sk q1217677-pointwise-leq-p
    (real-type domain left right)
  (forall (x)
    (implies
     (q1217677-member-p domain x)
     (q1217677-leq
      real-type
      (q1217677-function-at left x)
      (q1217677-function-at right x)))))

(defun-sk q1217677-functions-equal-on-p
    (domain left right)
  (forall (x)
    (implies
     (q1217677-member-p domain x)
     (equal
      (q1217677-function-at left x)
      (q1217677-function-at right x)))))

(defun-sk q1217677-lintegral-laws-p
    (real-type domain measurable measure lintegral)
  (forall (f g set)
    (and
     (implies
      (q1217677-functions-equal-on-p domain f g)
      (equal
       (q1217677-lintegral-value lintegral f)
       (q1217677-lintegral-value lintegral g)))
     (implies
      (q1217677-nonnegative-measurable-p
       real-type domain measurable f)
      (q1217677-ennreal-p
       real-type
       (q1217677-lintegral-value lintegral f)))
     (implies
      (and
       (q1217677-nonnegative-measurable-p
        real-type domain measurable f)
       (q1217677-nonnegative-measurable-p
        real-type domain measurable g)
       (q1217677-pointwise-leq-p real-type domain f g))
      (q1217677-ennreal-leq-p
       real-type
       (q1217677-lintegral-value lintegral f)
       (q1217677-lintegral-value lintegral g)))
     (implies
      (q1217677-family-member-p measurable set)
      (equal
       (q1217677-lintegral-value
        lintegral
        (q1217677-indicator-function real-type set))
       (q1217677-measure-value measure set)))
     (implies
      (and
       (q1217677-nonnegative-measurable-p
        real-type domain measurable f)
       (q1217677-nonnegative-measurable-p
        real-type domain measurable g))
      (equal
       (q1217677-lintegral-value
        lintegral
        (q1217677-function-add real-type f g))
       (q1217677-ennreal-add
        real-type
        (q1217677-lintegral-value lintegral f)
        (q1217677-lintegral-value lintegral g)))))))

(defun q1217677-simple-values-correct-p
    (domain measurable function values)
  (if (consp values)
      (and
       (q1217677-family-member-p
        measurable
        (q1217677-fiber-set function (car values)))
       (q1217677-simple-values-correct-p
        domain measurable function (cdr values)))
    (equal values nil)))

(defun q1217677-simple-listed-values-in-space-p
    (space values)
  (if (consp values)
      (and
       (q1217677-member-p space (car values))
       (q1217677-simple-listed-values-in-space-p
        space (cdr values)))
    (equal values nil)))

(defun-sk q1217677-simple-range-values-p
    (domain function values)
  (forall (x)
    (implies
     (q1217677-member-p domain x)
     (member-equal
      (q1217677-function-at function x)
      values))))

(defun-sk q1217677-value-attained-p
    (domain function value)
  (exists (x)
    (and
     (q1217677-member-p domain x)
     (equal
      (q1217677-function-at function x)
      value))))

(defun q1217677-simple-function-p
    (domain measurable space function)
  (and
   (q1217677-function-into-p domain space function)
   (true-listp (q1217677-simple-values function))
   (no-duplicatesp-equal (q1217677-simple-values function))
   (q1217677-simple-listed-values-in-space-p
    space (q1217677-simple-values function))
   (q1217677-simple-values-correct-p
    domain measurable function
    (q1217677-simple-values function))
   (q1217677-simple-range-values-p
    domain function
    (q1217677-simple-values function))))

(defun q1217677-simple-integrable-values-p
    (real-type domain measure zero function values)
  (if (consp values)
      (and
       (implies
        (not
         (q1217677-value-attained-p
          domain function (car values)))
        (equal
         (q1217677-measure-value
          measure
          (q1217677-fiber-set function (car values)))
         (q1217677-ennreal-finite
          (q1217677-zero real-type))))
       (or
        (equal (car values) zero)
        (not
         (equal
          (q1217677-measure-value
           measure
           (q1217677-fiber-set function (car values)))
          :q1217677-top)))
       (q1217677-simple-integrable-values-p
        real-type domain measure zero function (cdr values)))
    (equal values nil)))

(defun q1217677-simple-integral
    (real-type domain space measure function values)
  (if (consp values)
      (q1217677-add
       space
       (if (or
            (equal (car values) (q1217677-zero space))
            (not
             (q1217677-value-attained-p
              domain function (car values))))
           (q1217677-zero space)
         (q1217677-smul
          real-type space
          (cdr
           (q1217677-measure-value
            measure
            (q1217677-fiber-set function (car values))))
          (car values)))
       (q1217677-simple-integral
        real-type domain space measure function (cdr values)))
    (q1217677-zero space)))

(defun q1217677-ennreal-scale
    (real-type scalar value)
  (if (equal scalar (q1217677-zero real-type))
      (q1217677-ennreal-finite
       (q1217677-zero real-type))
    (if (equal value :q1217677-top)
        :q1217677-top
      (q1217677-ennreal-finite
       (q1217677-multiply
        real-type scalar (cdr value))))))

(defun q1217677-simple-nonnegative-integral
    (real-type domain measure function values)
  (if (consp values)
      (q1217677-ennreal-add
       real-type
       (if
           (q1217677-value-attained-p
            domain function (car values))
           (q1217677-ennreal-scale
            real-type
            (car values)
            (q1217677-measure-value
             measure
             (q1217677-fiber-set function (car values))))
         (q1217677-ennreal-finite
          (q1217677-zero real-type)))
       (q1217677-simple-nonnegative-integral
        real-type domain measure function (cdr values)))
    (q1217677-ennreal-finite
     (q1217677-zero real-type))))

(defun-sk q1217677-lintegral-upper-bound-p
    (real-type domain measurable measure function bound)
  (forall (simple)
    (implies
     (and
      (q1217677-simple-function-p
       domain measurable real-type simple)
      (q1217677-nonnegative-values-p
       real-type domain simple)
      (q1217677-pointwise-leq-p
       real-type domain simple function))
     (q1217677-ennreal-leq-p
      real-type
      (q1217677-simple-nonnegative-integral
       real-type domain measure simple
       (q1217677-simple-values simple))
      bound))))

(defun-sk q1217677-lintegral-least-upper-bound-p
    (real-type domain measurable measure function value)
  (forall (bound)
    (implies
     (and
      (q1217677-ennreal-p real-type bound)
      (q1217677-lintegral-upper-bound-p
       real-type domain measurable measure function bound))
     (q1217677-ennreal-leq-p real-type value bound))))

(defun-sk q1217677-lintegral-supremum-laws-p
    (real-type domain measurable measure lintegral)
  (forall (function)
    (implies
     (q1217677-nonnegative-measurable-p
      real-type domain measurable function)
     (let ((value
            (q1217677-lintegral-value
             lintegral function)))
       (and
        (q1217677-ennreal-p real-type value)
        (q1217677-lintegral-upper-bound-p
         real-type domain measurable measure function value)
        (q1217677-lintegral-least-upper-bound-p
         real-type domain measurable measure function value))))))

(defun-sk q1217677-simple-sequence-p
    (domain measurable space sequence)
  (forall (n)
    (implies
     (natp n)
     (q1217677-simple-function-p
      domain measurable space
      (q1217677-sequence-at sequence n)))))

(defun-sk q1217677-pointwise-simple-limit-p
    (real-type domain space sequence function)
  (forall (x)
    (implies
     (q1217677-member-p domain x)
     (q1217677-converges-p
      real-type
      space
      (q1217677-point-sequence sequence x)
      (q1217677-function-at function x)))))

(defun-sk q1217677-point-sequence-laws-p ()
  (forall (sequence x n)
    (equal
     (q1217677-sequence-at
      (q1217677-point-sequence sequence x) n)
     (q1217677-function-at
      (q1217677-sequence-at sequence n) x))))

(defun-sk q1217677-strongly-measurable-p
    (real-type domain measurable space function)
  (exists (sequence)
    (and
     (q1217677-simple-sequence-p
      domain measurable space sequence)
     (q1217677-pointwise-simple-limit-p
      real-type domain space sequence function))))

(defun q1217677-integrable-p
    (real-type domain measurable lintegral space function)
  (and
   (q1217677-strongly-measurable-p
    real-type domain measurable space function)
   (not
    (equal
     (q1217677-lintegral-value
      lintegral
      (q1217677-function-norm real-type space function))
     :q1217677-top))))

(defun q1217677-l1-distance
    (real-type space lintegral left right)
  (q1217677-lintegral-value
   lintegral
   (q1217677-function-norm
    real-type space
    (q1217677-function-difference space left right))))

(defun-sk q1217677-l1-tail-p
    (real-type space lintegral sequence function epsilon start)
  (forall (n)
    (implies
     (and (natp n) (natp start) (<= start n))
     (q1217677-ennreal-leq-p
      real-type
      (q1217677-l1-distance
       real-type space lintegral
       (q1217677-sequence-at sequence n)
       function)
      (q1217677-ennreal-finite epsilon)))))

(defun-sk q1217677-l1-start-p
    (real-type space lintegral sequence function epsilon)
  (exists (start)
    (and
     (natp start)
     (q1217677-l1-tail-p
      real-type space lintegral
      sequence function epsilon start))))

(defun-sk q1217677-l1-converges-p
    (real-type space lintegral sequence function)
  (forall (epsilon)
    (implies
     (and
      (q1217677-member-p real-type epsilon)
      (q1217677-positive-p real-type epsilon))
     (q1217677-l1-start-p
      real-type space lintegral sequence function epsilon))))

(defun-sk q1217677-integrable-simple-sequence-p
    (real-type domain measurable measure space sequence)
  (forall (n)
    (implies
     (natp n)
     (let ((f (q1217677-sequence-at sequence n)))
       (and
        (q1217677-simple-function-p
         domain measurable space f)
        (q1217677-simple-integrable-values-p
         real-type domain measure
         (q1217677-zero space) f
         (q1217677-simple-values f)))))))

(defun-sk q1217677-simple-integral-sequence-laws-p ()
  (forall (real-type domain space measure sequence n)
    (equal
     (q1217677-sequence-at
      (q1217677-simple-integral-sequence
       real-type domain space measure sequence)
      n)
     (q1217677-simple-integral
      real-type domain space measure
      (q1217677-sequence-at sequence n)
      (q1217677-simple-values
       (q1217677-sequence-at sequence n))))))

(defun q1217677-bochner-approximation-p
    (real-type domain measurable measure lintegral
     space function value sequence)
  (and
   (q1217677-integrable-simple-sequence-p
    real-type domain measurable measure space sequence)
   (q1217677-l1-converges-p
    real-type space lintegral sequence function)
   (q1217677-converges-p
    real-type space
    (q1217677-simple-integral-sequence
     real-type domain space measure sequence)
    value)))

(defun-sk q1217677-bochner-approximation-exists-p
    (real-type domain measurable measure lintegral
     space function value)
  (exists (sequence)
    (q1217677-bochner-approximation-p
     real-type domain measurable measure lintegral
     space function value sequence)))

(defun-sk q1217677-bochner-integral-operation-p
    (real-type domain measurable measure lintegral space integral)
  (forall (function other)
    (and
     (implies
      (q1217677-functions-equal-on-p
       domain function other)
      (equal
       (q1217677-bochner-integral-value
        integral function)
       (q1217677-bochner-integral-value
        integral other)))
     (implies
      (q1217677-function-into-p domain space function)
      (let ((value
             (q1217677-bochner-integral-value
              integral function)))
        (and
         (q1217677-member-p space value)
         (if
             (and
              (q1217677-complete-p real-type space)
              (q1217677-integrable-p
               real-type domain measurable lintegral
               space function))
             (q1217677-bochner-approximation-exists-p
              real-type domain measurable measure lintegral
              space function value)
           (equal value (q1217677-zero space)))))))))
;; The source domain is an arbitrary measurable space, so only the set
;; constructors needed for a sigma algebra are required on it.

(defun q1217677-basic-set-constructor-laws-p (domain)
  (and
   (q1217677-full-set-law-p domain)
   (q1217677-complement-set-law-p domain)
   (q1217677-countable-union-set-law-p domain)))

;; A real normed vector space need not be complete. This distinction is
;; semantically relevant because mathlib defines its Bochner integral to be
;; zero when the codomain is incomplete.

(defun q1217677-real-normed-space-p (real-type space)
  (and
   (q1217677-member-p space (q1217677-zero space))
   (q1217677-vector-space-laws-p real-type space)
   (q1217677-norm-laws-p real-type space)
   (q1217677-normed-space-laws-p real-type real-type space)))

;; Almost-everywhere predicates use a measurable null envelope, which is
;; equivalent to membership in the measure's almost-everywhere filter.

(defun q1217677-null-measurable-set-p
    (real-type domain measurable measure set)
  (and
   (q1217677-valid-set-p domain set)
   (q1217677-family-member-p measurable set)
   (equal
    (q1217677-measure-value measure set)
    (q1217677-ennreal-finite
     (q1217677-zero real-type)))))

(defun-sk q1217677-equal-off-set-p
    (domain left right exceptional)
  (forall (x)
    (implies
     (and
      (q1217677-member-p domain x)
      (not (q1217677-set-member-p exceptional x)))
     (equal
      (q1217677-function-at left x)
      (q1217677-function-at right x)))))

(defun q1217677-ae-equal-witness-p
    (real-type domain measurable measure left right exceptional)
  (and
   (q1217677-null-measurable-set-p
    real-type domain measurable measure exceptional)
   (q1217677-equal-off-set-p
    domain left right exceptional)))

(defun-sk q1217677-ae-equal-p
    (real-type domain measurable measure left right)
  (exists (exceptional)
    (q1217677-ae-equal-witness-p
     real-type domain measurable measure
     left right exceptional)))

(defun q1217677-ae-strongly-measurable-witness-p
    (real-type domain measurable measure
     space function representative)
  (and
   (q1217677-function-into-p
    domain space representative)
   (q1217677-strongly-measurable-p
    real-type domain measurable space representative)
   (q1217677-ae-equal-p
    real-type domain measurable measure
    function representative)))

(defun-sk q1217677-ae-strongly-measurable-p
    (real-type domain measurable measure space function)
  (exists (representative)
    (q1217677-ae-strongly-measurable-witness-p
     real-type domain measurable measure
     space function representative)))

(defun q1217677-ae-integrable-p
    (real-type domain measurable measure
     lintegral space function)
  (and
   (q1217677-function-into-p domain space function)
   (q1217677-ae-strongly-measurable-p
    real-type domain measurable measure space function)
   (not
    (equal
     (q1217677-lintegral-value
      lintegral
      (q1217677-function-norm
       real-type space function))
     :q1217677-top))))

;; Both lower integration and Bochner integration are invariant under
;; almost-everywhere equality. The Bochner operation uses the same simple
;; function/L1 characterization as above, and returns zero for incomplete
;; codomains or nonintegrable functions, matching mathlib's total integral.

(defun-sk q1217677-lintegral-ae-congruence-p
    (real-type domain measurable measure lintegral)
  (forall (left right)
    (implies
     (q1217677-ae-equal-p
      real-type domain measurable measure left right)
     (equal
      (q1217677-lintegral-value lintegral left)
      (q1217677-lintegral-value lintegral right)))))

(defun-sk q1217677-bochner-integral-ae-operation-p
    (real-type domain measurable measure
     lintegral space integral)
  (forall (function other)
    (and
     (implies
      (q1217677-ae-equal-p
       real-type domain measurable measure function other)
      (equal
       (q1217677-bochner-integral-value integral function)
       (q1217677-bochner-integral-value integral other)))
     (implies
      (q1217677-function-into-p domain space function)
      (let ((value
             (q1217677-bochner-integral-value
              integral function)))
        (and
         (q1217677-member-p space value)
         (if
             (and
              (q1217677-complete-p real-type space)
              (q1217677-ae-integrable-p
               real-type domain measurable measure
               lintegral space function))
             (q1217677-bochner-approximation-exists-p
              real-type domain measurable measure lintegral
              space function value)
           (equal value (q1217677-zero space)))))))))

;; Real interval constructors, restriction by zero, and normalized Lebesgue
;; volume.  The half-open interval is (left,right], so the signed interval
;; integral below is integral_(a,b] f - integral_(b,a] f.

(defun-sk q1217677-real-interval-constructor-laws-p (real-type)
  (forall (a b x)
    (implies
     (and
      (q1217677-member-p real-type a)
      (q1217677-member-p real-type b))
     (and
      (iff
       (q1217677-set-member-p
        (q1217677-closed-interval-set a b) x)
       (and
        (q1217677-member-p real-type x)
        (q1217677-leq real-type a x)
        (q1217677-leq real-type x b)))
      (iff
       (q1217677-set-member-p
        (q1217677-open-interval-set a b) x)
       (and
        (q1217677-member-p real-type x)
        (q1217677-less real-type a x)
        (q1217677-less real-type x b)))
      (iff
       (q1217677-set-member-p
        (q1217677-right-ray-set a) x)
       (and
        (q1217677-member-p real-type x)
        (q1217677-less real-type a x)))
      (iff
       (q1217677-set-member-p
        (q1217677-half-open-interval-set a b) x)
       (and
        (q1217677-member-p real-type x)
        (q1217677-less real-type a x)
        (q1217677-leq real-type x b)))))))

(defun-sk q1217677-restricted-function-laws-p ()
  (forall (space function set x)
    (equal
     (q1217677-function-at
      (q1217677-restricted-function space function set) x)
     (if (q1217677-set-member-p set x)
         (q1217677-function-at function x)
       (q1217677-zero space)))))

(defun q1217677-lebesgue-volume-p
    (real-type measurable measure)
  (and
   (q1217677-borel-space-p real-type real-type measurable)
   (q1217677-measure-space-p
    real-type real-type measurable measure)
   (q1217677-translation-invariant-p
    real-type measurable measure)
   (q1217677-family-member-p
    measurable
    (q1217677-half-open-interval-set
     (q1217677-zero real-type)
     (q1217677-one real-type)))
   (equal
    (q1217677-measure-value
     measure
     (q1217677-half-open-interval-set
      (q1217677-zero real-type)
      (q1217677-one real-type)))
    (q1217677-ennreal-finite
     (q1217677-one real-type)))))

(defun q1217677-analysis-context-p
    (real-type space measurable measure lintegral integral)
  (and
   (q1217677-real-field-p real-type)
   (q1217677-real-normed-space-p real-type space)
   (q1217677-complete-p real-type space)
   (q1217677-basic-set-constructor-laws-p real-type)
   (q1217677-open-ball-set-law-p real-type real-type)
   (q1217677-preimage-set-law-p real-type)
   (q1217677-translate-set-law-p real-type)
   (q1217677-fiber-set-law-p real-type)
   (q1217677-real-interval-constructor-laws-p real-type)
   (q1217677-restricted-function-laws-p)
   (q1217677-function-constructor-laws-p real-type)
   (q1217677-point-sequence-laws-p)
   (q1217677-simple-integral-sequence-laws-p)
   (q1217677-lebesgue-volume-p
    real-type measurable measure)
   (q1217677-lintegral-laws-p
    real-type real-type measurable measure lintegral)
   (q1217677-lintegral-supremum-laws-p
    real-type real-type measurable measure lintegral)
   (q1217677-lintegral-ae-congruence-p
    real-type real-type measurable measure lintegral)
   (q1217677-bochner-integral-ae-operation-p
    real-type real-type measurable measure
    lintegral space integral)))

;; Signed Bochner interval integration and interval integrability.

(defun q1217677-interval-integral-value
    (space integral function a b)
  (q1217677-add
   space
   (q1217677-bochner-integral-value
    integral
    (q1217677-restricted-function
     space function
     (q1217677-half-open-interval-set a b)))
   (q1217677-negate
    space
    (q1217677-bochner-integral-value
     integral
     (q1217677-restricted-function
      space function
      (q1217677-half-open-interval-set b a))))))

(defun q1217677-interval-integrable-p
    (real-type space measurable measure lintegral function a b)
  (and
   (q1217677-ae-integrable-p
    real-type real-type measurable measure lintegral space
    (q1217677-restricted-function
     space function
     (q1217677-half-open-interval-set a b)))
   (q1217677-ae-integrable-p
    real-type real-type measurable measure lintegral space
    (q1217677-restricted-function
     space function
     (q1217677-half-open-interval-set b a)))))

;; AE strong measurability at the neighborhood filter of b is expressed by an
;; AE strongly measurable zero extension on some open ball around b.

(defun q1217677-strongly-measurable-near-witness-p
    (real-type space measurable measure function b radius)
  (and
   (q1217677-member-p real-type radius)
   (q1217677-positive-p real-type radius)
   (q1217677-ae-strongly-measurable-p
    real-type real-type measurable measure space
    (q1217677-restricted-function
     space function
     (q1217677-open-ball-set real-type b radius)))))

(defun-sk q1217677-strongly-measurable-at-p
    (real-type space measurable measure function b)
  (exists (radius)
    (q1217677-strongly-measurable-near-witness-p
     real-type space measurable measure function b radius)))

;; Tendsto f (nhds b inf ae volume) (nhds c): for every target radius there
;; are a source neighborhood and a measurable null exceptional set.

(defun-sk q1217677-tendsto-ae-near-off-set-p
    (real-type space function b c epsilon radius exceptional)
  (forall (x)
    (implies
     (and
      (q1217677-member-p real-type x)
      (q1217677-less
       real-type
       (q1217677-distance real-type real-type x b)
       radius)
      (not (q1217677-set-member-p exceptional x)))
     (q1217677-less
      real-type
      (q1217677-distance
       real-type space
       (q1217677-function-at function x) c)
      epsilon))))

(defun q1217677-tendsto-ae-near-witness-p
    (real-type space measurable measure
     function b c epsilon radius exceptional)
  (and
   (q1217677-member-p real-type radius)
   (q1217677-positive-p real-type radius)
   (q1217677-null-measurable-set-p
    real-type real-type measurable measure exceptional)
   (q1217677-tendsto-ae-near-off-set-p
    real-type space function b c epsilon radius exceptional)))

(defun-sk q1217677-tendsto-ae-near-at-epsilon-p
    (real-type space measurable measure function b c epsilon)
  (exists (radius exceptional)
    (q1217677-tendsto-ae-near-witness-p
     real-type space measurable measure
     function b c epsilon radius exceptional)))

(defun-sk q1217677-tendsto-ae-near-p
    (real-type space measurable measure function b c)
  (forall (epsilon)
    (implies
     (and
      (q1217677-member-p real-type epsilon)
      (q1217677-positive-p real-type epsilon))
     (q1217677-tendsto-ae-near-at-epsilon-p
      real-type space measurable measure function b c epsilon))))

;; Strict derivative of u |-> integral a..u f at b with derivative c.

(defun-sk q1217677-interval-integral-strict-derivative-bound-p
    (real-type space integral function a b c epsilon radius)
  (forall (x y)
    (implies
     (and
      (q1217677-member-p real-type x)
      (q1217677-member-p real-type y)
      (q1217677-less
       real-type
       (q1217677-distance real-type real-type x b)
       radius)
      (q1217677-less
       real-type
       (q1217677-distance real-type real-type y b)
       radius))
     (q1217677-leq
      real-type
      (q1217677-norm
       space
       (q1217677-add
        space
        (q1217677-add
         space
         (q1217677-interval-integral-value
          space integral function a x)
         (q1217677-negate
          space
          (q1217677-interval-integral-value
           space integral function a y)))
        (q1217677-negate
         space
         (q1217677-smul
          real-type space
          (q1217677-add
           real-type x (q1217677-negate real-type y))
          c))))
      (q1217677-multiply
       real-type epsilon
       (q1217677-distance real-type real-type x y))))))

(defun-sk q1217677-interval-integral-strict-derivative-epsilon-p
    (real-type space integral function a b c epsilon)
  (exists (radius)
    (and
     (q1217677-member-p real-type radius)
     (q1217677-positive-p real-type radius)
     (q1217677-interval-integral-strict-derivative-bound-p
      real-type space integral function a b c epsilon radius))))

(defun-sk q1217677-interval-integral-has-strict-derivative-p
    (real-type space integral function a b c)
  (forall (epsilon)
    (implies
     (and
      (q1217677-member-p real-type epsilon)
      (q1217677-positive-p real-type epsilon))
     (q1217677-interval-integral-strict-derivative-epsilon-p
      real-type space integral function a b c epsilon))))

;; Continuity on [a,b].

(defun-sk q1217677-continuous-on-delta-p
    (real-type space function set x epsilon delta)
  (forall (y)
    (implies
     (and
      (q1217677-set-member-p set y)
      (q1217677-less
       real-type
       (q1217677-distance real-type real-type y x)
       delta))
     (q1217677-less
      real-type
      (q1217677-distance
       real-type space
       (q1217677-function-at function y)
       (q1217677-function-at function x))
      epsilon))))

(defun-sk q1217677-continuous-on-epsilon-p
    (real-type space function set x epsilon)
  (exists (delta)
    (and
     (q1217677-member-p real-type delta)
     (q1217677-positive-p real-type delta)
     (q1217677-continuous-on-delta-p
      real-type space function set x epsilon delta))))

(defun-sk q1217677-continuous-on-p
    (real-type space function set)
  (forall (x epsilon)
    (implies
     (and
      (q1217677-set-member-p set x)
      (q1217677-member-p real-type epsilon)
      (q1217677-positive-p real-type epsilon))
     (q1217677-continuous-on-epsilon-p
      real-type space function set x epsilon))))

;; HasDerivWithinAt f d (Ioi x) x, written as the usual one-sided
;; epsilon estimate on the derivative remainder.

(defun-sk q1217677-has-right-derivative-bound-p
    (real-type space function derivative x epsilon delta)
  (forall (y)
    (implies
     (and
      (q1217677-member-p real-type y)
      (q1217677-set-member-p
       (q1217677-right-ray-set x) y)
      (q1217677-less
       real-type
       (q1217677-distance real-type real-type y x)
       delta))
     (q1217677-leq
      real-type
      (q1217677-norm
       space
       (q1217677-add
        space
        (q1217677-add
         space
         (q1217677-function-at function y)
         (q1217677-negate
          space (q1217677-function-at function x)))
        (q1217677-negate
         space
         (q1217677-smul
          real-type space
          (q1217677-add
           real-type y (q1217677-negate real-type x))
          derivative))))
      (q1217677-multiply
       real-type epsilon
       (q1217677-distance real-type real-type y x))))))

(defun-sk q1217677-has-right-derivative-epsilon-p
    (real-type space function derivative x epsilon)
  (exists (delta)
    (and
     (q1217677-member-p real-type delta)
     (q1217677-positive-p real-type delta)
     (q1217677-has-right-derivative-bound-p
      real-type space function derivative x epsilon delta))))

(defun-sk q1217677-has-right-derivative-p
    (real-type space function derivative x)
  (forall (epsilon)
    (implies
     (and
      (q1217677-member-p real-type epsilon)
      (q1217677-positive-p real-type epsilon))
     (q1217677-has-right-derivative-epsilon-p
      real-type space function derivative x epsilon))))

(defun-sk q1217677-has-right-derivative-on-open-interval-p
    (real-type space function derivative-function a b)
  (forall (x)
    (implies
     (q1217677-set-member-p
      (q1217677-open-interval-set a b) x)
     (q1217677-has-right-derivative-p
      real-type space function
      (q1217677-function-at derivative-function x) x))))

;; This predicate is exactly the indexed Lean theorem
;; intervalIntegral.integral_hasStrictDerivAt_of_tendsto_ae_right.

(defun thousand-theorems-q1217677-ftc-strict-derivative-statement
    (real-type space measurable measure lintegral integral
     function a b c)
  (implies
   (and
    (q1217677-analysis-context-p
     real-type space measurable measure lintegral integral)
    (q1217677-member-p real-type a)
    (q1217677-member-p real-type b)
    (q1217677-member-p space c)
    (q1217677-function-into-p real-type space function)
    (q1217677-interval-integrable-p
     real-type space measurable measure lintegral function a b)
    (q1217677-strongly-measurable-at-p
     real-type space measurable measure function b)
    (q1217677-tendsto-ae-near-p
     real-type space measurable measure function b c))
   (q1217677-interval-integral-has-strict-derivative-p
    real-type space integral function a b c)))

;; This predicate is exactly the indexed Lean theorem
;; intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le.

(defun thousand-theorems-q1217677-ftc-integral-equals-sub-statement
    (real-type space measurable measure lintegral integral
     function derivative-function a b)
  (implies
   (and
    (q1217677-analysis-context-p
     real-type space measurable measure lintegral integral)
    (q1217677-member-p real-type a)
    (q1217677-member-p real-type b)
    (q1217677-function-into-p real-type space function)
    (q1217677-function-into-p
     real-type space derivative-function)
    (q1217677-leq real-type a b)
    (q1217677-continuous-on-p
     real-type space function
     (q1217677-closed-interval-set a b))
    (q1217677-has-right-derivative-on-open-interval-p
     real-type space function derivative-function a b)
    (q1217677-interval-integrable-p
     real-type space measurable measure lintegral
     derivative-function a b))
   (equal
    (q1217677-interval-integral-value
     space integral derivative-function a b)
    (q1217677-add
     space
     (q1217677-function-at function b)
     (q1217677-negate
      space
      (q1217677-function-at function a))))))

(value-triple :itpeval-statement-checked)
:q
