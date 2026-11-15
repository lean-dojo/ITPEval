;; Statement-only formalization of thousand-theorems corpus artifact Q1966978,
;; "Lévy continuity theorem": for probability measures on an arbitrary
;; finite-dimensional real inner-product space with its Borel sigma algebra,
;; weak convergence is equivalent to pointwise convergence of the complex
;; characteristic functions. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Types, sets, functions, measures, and sequences are unrestricted ACL2
;; objects interpreted by conservative interfaces.  The predicates below
;; explicitly impose a complete ordered real field, a finite-dimensional real
;; inner-product space, its Borel sigma algebra, countably additive probability
;; measures, exact bounded Lebesgue integration, and the power-series sine and
;; cosine used by the characteristic function.  No carrier is made finite:
;; only the internally quantified basis has finite length.

(defstub q1966978-member-p (type object) t)
(defstub q1966978-set-member-p (set object) t)
(defstub q1966978-family-member-p (family set) t)
(defstub q1966978-function-at (function argument) t)
(defstub q1966978-sequence-at (sequence index) t)

(defstub q1966978-zero (type) t)
(defstub q1966978-one (type) t)
(defstub q1966978-add (type left right) t)
(defstub q1966978-multiply (type left right) t)
(defstub q1966978-negate (type object) t)
(defstub q1966978-inverse (type object) t)
(defstub q1966978-less (type left right) t)

(defstub q1966978-smul (real space scalar vector) t)
(defstub q1966978-inner (real space left right) t)
(defstub q1966978-norm (real space vector) t)
(defstub q1966978-basis-at (basis index) t)
(defstub q1966978-coordinate (coordinates vector index) t)

(defstub q1966978-empty-set (space) t)
(defstub q1966978-full-set (space) t)
(defstub q1966978-complement-set (space set) t)
(defstub q1966978-countable-union-set (space sequence) t)
(defstub q1966978-open-ball-set (real space center radius) t)
(defstub q1966978-upper-ray-preimage-set
  (real space function threshold) t)
(defstub q1966978-fiber-set (space function value) t)

(defstub q1966978-measure-at (measure-sequence index) t)
(defstub q1966978-measure-value (measure set) t)
(defstub q1966978-lintegral-value (measure function) t)

(defstub q1966978-zero-function (real space) t)
(defstub q1966978-positive-part-function (real function) t)
(defstub q1966978-negative-part-function (real function) t)
(defstub q1966978-cos-inner-function (real space frequency) t)
(defstub q1966978-sin-inner-function (real space frequency) t)
(defstub q1966978-sine (real value) t)
(defstub q1966978-cosine (real value) t)

(defun q1966978-leq (real x y)
  (not (q1966978-less real y x)))

(defun q1966978-positive-p (real x)
  (and
   (q1966978-member-p real x)
   (q1966978-less real (q1966978-zero real) x)))

(defun q1966978-nonnegative-p (real x)
  (and
   (q1966978-member-p real x)
   (q1966978-leq real (q1966978-zero real) x)))

(defun q1966978-subtract (type x y)
  (q1966978-add type x (q1966978-negate type y)))

(defun q1966978-absolute-value (real x)
  (if (q1966978-less real x (q1966978-zero real))
      (q1966978-negate real x)
    x))

(defun q1966978-natural-cast (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1966978-zero real)
    (q1966978-add
     real
     (q1966978-natural-cast real (- n 1))
     (q1966978-one real))))

(defun q1966978-power (real x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1966978-one real)
    (q1966978-multiply
     real x (q1966978-power real x (- n 1)))))

(defun q1966978-factorial (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1966978-one real)
    (q1966978-multiply
     real
     (q1966978-natural-cast real n)
     (q1966978-factorial real (- n 1)))))

(defun q1966978-divide (real x y)
  (q1966978-multiply real x (q1966978-inverse real y)))

(defun q1966978-alternating (real k x)
  (if (equal (mod (nfix k) 2) 0)
      x
    (q1966978-negate real x)))

(defun q1966978-cosine-partial-sum (real count x)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q1966978-zero real)
    (let* ((k (- count 1))
           (degree (* 2 k))
           (term
            (q1966978-alternating
             real k
             (q1966978-divide
              real
              (q1966978-power real x degree)
              (q1966978-factorial real degree)))))
      (q1966978-add
       real
       (q1966978-cosine-partial-sum real k x)
       term))))

(defun q1966978-sine-partial-sum (real count x)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q1966978-zero real)
    (let* ((k (- count 1))
           (degree (+ 1 (* 2 k)))
           (term
            (q1966978-alternating
             real k
             (q1966978-divide
              real
              (q1966978-power real x degree)
              (q1966978-factorial real degree)))))
      (q1966978-add
       real
       (q1966978-sine-partial-sum real k x)
       term))))

;; A Dedekind-complete ordered field presents the real numbers.

(defun-sk q1966978-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q1966978-member-p real x)
      (q1966978-member-p real y)
      (q1966978-member-p real z))
     (let ((zero (q1966978-zero real))
           (one (q1966978-one real)))
       (and
        (q1966978-member-p real (q1966978-add real x y))
        (q1966978-member-p real (q1966978-multiply real x y))
        (q1966978-member-p real (q1966978-negate real x))
        (q1966978-member-p real (q1966978-inverse real x))
        (equal
         (q1966978-add real (q1966978-add real x y) z)
         (q1966978-add real x (q1966978-add real y z)))
        (equal (q1966978-add real x y)
               (q1966978-add real y x))
        (equal (q1966978-add real x zero) x)
        (equal (q1966978-add real x (q1966978-negate real x))
               zero)
        (equal
         (q1966978-multiply
          real (q1966978-multiply real x y) z)
         (q1966978-multiply
          real x (q1966978-multiply real y z)))
        (equal (q1966978-multiply real x y)
               (q1966978-multiply real y x))
        (equal (q1966978-multiply real x one) x)
        (equal (q1966978-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q1966978-multiply
           real x (q1966978-inverse real x))
          one))
        (equal
         (q1966978-multiply
          real x (q1966978-add real y z))
         (q1966978-add
          real
          (q1966978-multiply real x y)
          (q1966978-multiply real x z))))))))

(defun-sk q1966978-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q1966978-member-p real x)
      (q1966978-member-p real y)
      (q1966978-member-p real z))
     (let ((zero (q1966978-zero real)))
       (and
        (not (q1966978-less real x x))
        (or
         (equal x y)
         (q1966978-less real x y)
         (q1966978-less real y x))
        (implies
         (and
          (q1966978-less real x y)
          (q1966978-less real y z))
         (q1966978-less real x z))
        (implies
         (q1966978-less real x y)
         (q1966978-less
          real
          (q1966978-add real x z)
          (q1966978-add real y z)))
        (implies
         (and
          (q1966978-less real zero x)
          (q1966978-less real zero y))
         (q1966978-less
          real zero (q1966978-multiply real x y))))))))

(defun-sk q1966978-real-set-nonempty-p (real set)
  (exists (x)
    (and
     (q1966978-member-p real x)
     (q1966978-set-member-p set x))))

(defun-sk q1966978-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q1966978-member-p real x)
      (q1966978-set-member-p set x))
     (q1966978-leq real x bound))))

(defun-sk q1966978-bounded-above-p (real set)
  (exists (bound)
    (and
     (q1966978-member-p real bound)
     (q1966978-upper-bound-p real set bound))))

(defun-sk q1966978-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q1966978-member-p real supremum)
     (q1966978-upper-bound-p real set supremum)
     (implies
      (and
       (q1966978-member-p real bound)
       (q1966978-upper-bound-p real set bound))
      (q1966978-leq real supremum bound)))))

(defun-sk q1966978-supremum-exists-p (real set)
  (exists (supremum)
    (q1966978-supremum-p real set supremum)))

(defun-sk q1966978-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q1966978-real-set-nonempty-p real set)
      (q1966978-bounded-above-p real set))
     (q1966978-supremum-exists-p real set))))

(defun q1966978-real-structure-p (real)
  (and
   (q1966978-member-p real (q1966978-zero real))
   (q1966978-member-p real (q1966978-one real))
   (not (equal (q1966978-zero real)
               (q1966978-one real)))
   (q1966978-less
    real (q1966978-zero real) (q1966978-one real))
   (q1966978-field-laws-p real)
   (q1966978-order-laws-p real)
   (q1966978-dedekind-complete-p real)))

;; The finite-dimensional real inner-product space.  The orthonormal basis and
;; coordinate map are internal existential witnesses, as in the source's
;; FiniteDimensional typeclass rather than additional theorem parameters.

(defun-sk q1966978-vector-space-laws-p (real space)
  (forall (a b x y z)
    (implies
     (and
      (q1966978-member-p real a)
      (q1966978-member-p real b)
      (q1966978-member-p space x)
      (q1966978-member-p space y)
      (q1966978-member-p space z))
     (and
      (q1966978-member-p space (q1966978-add space x y))
      (q1966978-member-p space (q1966978-negate space x))
      (q1966978-member-p
       space (q1966978-smul real space a x))
      (equal
       (q1966978-add space (q1966978-add space x y) z)
       (q1966978-add space x (q1966978-add space y z)))
      (equal (q1966978-add space x y)
             (q1966978-add space y x))
      (equal (q1966978-add space x (q1966978-zero space)) x)
      (equal
       (q1966978-add space x (q1966978-negate space x))
       (q1966978-zero space))
      (equal
       (q1966978-smul real space (q1966978-one real) x)
       x)
      (equal
       (q1966978-smul
        real space (q1966978-multiply real a b) x)
       (q1966978-smul
        real space a (q1966978-smul real space b x)))
      (equal
       (q1966978-smul
        real space (q1966978-add real a b) x)
       (q1966978-add
        space
        (q1966978-smul real space a x)
        (q1966978-smul real space b x)))
      (equal
       (q1966978-smul
        real space a (q1966978-add space x y))
       (q1966978-add
        space
        (q1966978-smul real space a x)
        (q1966978-smul real space a y)))))))

(defun-sk q1966978-inner-product-laws-p (real space)
  (forall (a x y z)
    (implies
     (and
      (q1966978-member-p real a)
      (q1966978-member-p space x)
      (q1966978-member-p space y)
      (q1966978-member-p space z))
     (let ((xy (q1966978-inner real space x y))
           (xx (q1966978-inner real space x x)))
       (and
        (q1966978-member-p real xy)
        (q1966978-nonnegative-p real xx)
        (equal
         (q1966978-inner
          real space x (q1966978-add space y z))
         (q1966978-add
          real xy (q1966978-inner real space x z)))
        (equal
         (q1966978-inner
          real space x (q1966978-smul real space a y))
         (q1966978-multiply real a xy))
        (equal
         (q1966978-inner real space y x)
         xy)
        (iff
         (equal xx (q1966978-zero real))
         (equal x (q1966978-zero space)))
        (q1966978-member-p
         real (q1966978-norm real space x))
        (q1966978-nonnegative-p
         real (q1966978-norm real space x))
        (equal
         (q1966978-multiply
          real
          (q1966978-norm real space x)
          (q1966978-norm real space x))
         xx))))))

(defun q1966978-vector-sum
    (real space basis coordinates vector count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q1966978-zero space)
    (let ((i (- count 1)))
      (q1966978-add
       space
       (q1966978-vector-sum
        real space basis coordinates vector i)
       (q1966978-smul
        real space
        (q1966978-coordinate coordinates vector i)
        (q1966978-basis-at basis i))))))

(defun-sk q1966978-orthonormal-basis-p
    (real space basis coordinates dimension)
  (forall (i j x)
    (and
     (implies
      (and (natp i) (< i dimension))
      (q1966978-member-p
       space (q1966978-basis-at basis i)))
     (implies
      (and
       (natp i) (natp j)
       (< i dimension) (< j dimension))
      (equal
       (q1966978-inner
        real space
        (q1966978-basis-at basis i)
        (q1966978-basis-at basis j))
       (if (equal i j)
           (q1966978-one real)
         (q1966978-zero real))))
     (implies
      (q1966978-member-p space x)
      (and
       (implies
        (and (natp i) (< i dimension))
        (q1966978-member-p
         real (q1966978-coordinate coordinates x i)))
       (equal
        x
        (q1966978-vector-sum
         real space basis coordinates x dimension)))))))

(defun-sk q1966978-finite-basis-exists-p (real space)
  (exists (basis coordinates dimension)
    (and
     (natp dimension)
     (q1966978-orthonormal-basis-p
      real space basis coordinates dimension))))

(defun q1966978-finite-inner-product-space-p (real space)
  (and
   (q1966978-member-p space (q1966978-zero space))
   (q1966978-vector-space-laws-p real space)
   (q1966978-inner-product-laws-p real space)
   (q1966978-finite-basis-exists-p real space)))

;; Extensional sets, metric balls, sigma algebras, and the Borel sigma algebra.

(defun q1966978-distance (real space x y)
  (q1966978-norm
   real space (q1966978-subtract space x y)))

(defun-sk q1966978-countable-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q1966978-set-member-p
      (q1966978-sequence-at sequence n) x))))

(defun-sk q1966978-set-constructor-laws-p (real space)
  (forall (set sequence center radius x)
    (and
     (iff
      (q1966978-set-member-p
       (q1966978-empty-set space) x)
      nil)
     (iff
      (q1966978-set-member-p
       (q1966978-full-set space) x)
      (q1966978-member-p space x))
     (iff
      (q1966978-set-member-p
       (q1966978-complement-set space set) x)
      (and
       (q1966978-member-p space x)
       (not (q1966978-set-member-p set x))))
     (iff
      (q1966978-set-member-p
       (q1966978-countable-union-set space sequence) x)
      (and
       (q1966978-member-p space x)
       (q1966978-countable-union-member-p sequence x)))
     (implies
      (and
       (q1966978-member-p space center)
       (q1966978-positive-p real radius))
      (iff
       (q1966978-set-member-p
        (q1966978-open-ball-set
         real space center radius)
        x)
       (and
        (q1966978-member-p space x)
        (q1966978-less
         real
         (q1966978-distance real space x center)
         radius)))))))

(defun-sk q1966978-valid-set-p (space set)
  (forall (x)
    (implies
     (q1966978-set-member-p set x)
     (q1966978-member-p space x))))

(defun-sk q1966978-sets-equal-p (space left right)
  (forall (x)
    (implies
     (q1966978-member-p space x)
     (iff
      (q1966978-set-member-p left x)
      (q1966978-set-member-p right x)))))

(defun-sk q1966978-family-valid-p (space family)
  (forall (set)
    (implies
     (q1966978-family-member-p family set)
     (q1966978-valid-set-p space set))))

(defun-sk q1966978-family-extensional-p (space family)
  (forall (left right)
    (implies
     (and
      (q1966978-family-member-p family left)
      (q1966978-sets-equal-p space left right))
     (q1966978-family-member-p family right))))

(defun-sk q1966978-measurable-sequence-p (family sequence)
  (forall (n)
    (implies
     (natp n)
     (q1966978-family-member-p
      family (q1966978-sequence-at sequence n)))))

(defun-sk q1966978-sigma-closure-p (space family)
  (forall (set sequence)
    (and
     (q1966978-family-member-p
      family (q1966978-empty-set space))
     (q1966978-family-member-p
      family (q1966978-full-set space))
     (implies
      (q1966978-family-member-p family set)
      (q1966978-family-member-p
       family (q1966978-complement-set space set)))
     (implies
      (q1966978-measurable-sequence-p family sequence)
      (q1966978-family-member-p
       family
       (q1966978-countable-union-set space sequence))))))

(defun q1966978-sigma-algebra-p (space family)
  (and
   (q1966978-family-valid-p space family)
   (q1966978-family-extensional-p space family)
   (q1966978-sigma-closure-p space family)))

(defun-sk q1966978-balls-measurable-p (real space family)
  (forall (center radius)
    (implies
     (and
      (q1966978-member-p space center)
      (q1966978-positive-p real radius))
     (q1966978-family-member-p
      family
      (q1966978-open-ball-set
       real space center radius)))))

(defun-sk q1966978-family-subset-p (left right)
  (forall (set)
    (implies
     (q1966978-family-member-p left set)
     (q1966978-family-member-p right set))))

(defun-sk q1966978-borel-minimal-p (real space borel)
  (forall (candidate)
    (implies
     (and
      (q1966978-sigma-algebra-p space candidate)
      (q1966978-balls-measurable-p
       real space candidate))
     (q1966978-family-subset-p borel candidate))))

(defun q1966978-borel-space-p (real space borel)
  (and
   (q1966978-sigma-algebra-p space borel)
   (q1966978-balls-measurable-p real space borel)
   (q1966978-borel-minimal-p real space borel)))

;; Sequential convergence in the real field.

(defun-sk q1966978-real-convergence-tail-p
    (real sequence limit epsilon start)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp start)
      (<= start n))
     (q1966978-less
      real
      (q1966978-absolute-value
       real
       (q1966978-subtract
        real
        (q1966978-sequence-at sequence n)
        limit))
      epsilon))))

(defun-sk q1966978-real-convergence-start-p
    (real sequence limit epsilon)
  (exists (start)
    (and
     (natp start)
     (q1966978-real-convergence-tail-p
      real sequence limit epsilon start))))

(defun-sk q1966978-real-converges-p
    (real sequence limit)
  (forall (epsilon)
    (implies
     (q1966978-positive-p real epsilon)
     (q1966978-real-convergence-start-p
      real sequence limit epsilon))))

;; The standard sine and cosine are fixed by their everywhere-convergent power
;; series.  Their usual bounds are included as redundant consequences so that
;; bounded integrability is explicit in the statement model.

(defstub q1966978-cosine-partial-sequence (real x) t)
(defstub q1966978-sine-partial-sequence (real x) t)

(defun-sk q1966978-trigonometric-sequence-laws-p (real)
  (forall (x n)
    (implies
     (and
      (q1966978-member-p real x)
      (natp n))
     (and
      (equal
       (q1966978-sequence-at
        (q1966978-cosine-partial-sequence real x) n)
       (q1966978-cosine-partial-sum real n x))
      (equal
       (q1966978-sequence-at
        (q1966978-sine-partial-sequence real x) n)
       (q1966978-sine-partial-sum real n x))))))

(defun-sk q1966978-trigonometric-laws-p (real)
  (forall (x)
    (implies
     (q1966978-member-p real x)
     (and
      (q1966978-member-p
       real (q1966978-cosine real x))
      (q1966978-member-p
       real (q1966978-sine real x))
      (q1966978-real-converges-p
       real
       (q1966978-cosine-partial-sequence real x)
       (q1966978-cosine real x))
      (q1966978-real-converges-p
       real
       (q1966978-sine-partial-sequence real x)
       (q1966978-sine real x))
      (q1966978-leq
       real
       (q1966978-absolute-value
        real (q1966978-cosine real x))
       (q1966978-one real))
      (q1966978-leq
       real
       (q1966978-absolute-value
        real (q1966978-sine real x))
       (q1966978-one real))))))

;; Countably additive real-valued probability measures.  Since every measure
;; here has total mass one, countable sums are finite real limits rather than
;; an approximation by rational or floating-point values.

(defun q1966978-measure-partial-sum
    (real measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q1966978-zero real)
    (q1966978-add
     real
     (q1966978-measure-partial-sum
      real measure sequence (- count 1))
     (q1966978-measure-value
      measure
      (q1966978-sequence-at sequence (- count 1))))))

(defun-sk q1966978-measure-sum-tail-p
    (real measure sequence total epsilon start)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp start)
      (<= start n))
     (q1966978-less
      real
      (q1966978-absolute-value
       real
       (q1966978-subtract
        real
        (q1966978-measure-partial-sum
         real measure sequence n)
        total))
      epsilon))))

(defun-sk q1966978-measure-sum-start-p
    (real measure sequence total epsilon)
  (exists (start)
    (and
     (natp start)
     (q1966978-measure-sum-tail-p
      real measure sequence total epsilon start))))

(defun-sk q1966978-measure-sum-converges-p
    (real measure sequence total)
  (forall (epsilon)
    (implies
     (q1966978-positive-p real epsilon)
     (q1966978-measure-sum-start-p
      real measure sequence total epsilon))))

(defun-sk q1966978-pairwise-disjoint-p (sequence)
  (forall (m n x)
    (implies
     (and
      (natp m)
      (natp n)
      (not (equal m n)))
     (not
      (and
       (q1966978-set-member-p
        (q1966978-sequence-at sequence m) x)
       (q1966978-set-member-p
        (q1966978-sequence-at sequence n) x))))))

(defun-sk q1966978-measure-extensional-p
    (space measure)
  (forall (left right)
    (implies
     (q1966978-sets-equal-p space left right)
     (equal
      (q1966978-measure-value measure left)
      (q1966978-measure-value measure right)))))

(defun-sk q1966978-measure-values-p
    (real family measure)
  (forall (set)
    (implies
     (q1966978-family-member-p family set)
     (q1966978-nonnegative-p
      real (q1966978-measure-value measure set)))))

(defun-sk q1966978-countable-additivity-p
    (real space family measure)
  (forall (sequence)
    (implies
     (and
      (q1966978-measurable-sequence-p family sequence)
      (q1966978-pairwise-disjoint-p sequence))
     (q1966978-measure-sum-converges-p
      real measure sequence
      (q1966978-measure-value
       measure
       (q1966978-countable-union-set
        space sequence))))))

(defun q1966978-probability-measure-p
    (real space family measure)
  (and
   (q1966978-measure-extensional-p space measure)
   (q1966978-measure-values-p real family measure)
   (equal
    (q1966978-measure-value
     measure (q1966978-empty-set space))
    (q1966978-zero real))
   (equal
    (q1966978-measure-value
     measure (q1966978-full-set space))
    (q1966978-one real))
   (q1966978-countable-additivity-p
    real space family measure)))

(defun-sk q1966978-probability-measure-sequence-p
    (real space family measure-sequence)
  (forall (n)
    (implies
     (natp n)
     (q1966978-probability-measure-p
      real space family
      (q1966978-measure-at measure-sequence n)))))

;; Real-valued functions, Borel measurability, boundedness, and continuity.

(defun-sk q1966978-real-function-p
    (real space function)
  (forall (x)
    (implies
     (q1966978-member-p space x)
     (q1966978-member-p
      real (q1966978-function-at function x)))))

(defun-sk q1966978-upper-ray-constructor-laws-p
    (real space)
  (forall (function threshold x)
    (iff
     (q1966978-set-member-p
      (q1966978-upper-ray-preimage-set
       real space function threshold)
      x)
     (and
      (q1966978-member-p space x)
      (q1966978-less
       real threshold
       (q1966978-function-at function x))))))

(defun-sk q1966978-measurable-function-p
    (real space family function)
  (forall (threshold)
    (and
     (q1966978-real-function-p real space function)
     (implies
      (q1966978-member-p real threshold)
      (q1966978-family-member-p
       family
       (q1966978-upper-ray-preimage-set
        real space function threshold))))))

(defun-sk q1966978-bounded-by-p
    (real space function bound)
  (forall (x)
    (implies
     (q1966978-member-p space x)
     (q1966978-leq
      real
      (q1966978-absolute-value
       real (q1966978-function-at function x))
      bound))))

(defun-sk q1966978-bounded-function-p
    (real space function)
  (exists (bound)
    (and
     (q1966978-nonnegative-p real bound)
     (q1966978-bounded-by-p
      real space function bound))))

(defun-sk q1966978-continuity-ball-p
    (real space function x epsilon radius)
  (forall (y)
    (implies
     (and
      (q1966978-member-p space y)
      (q1966978-less
       real
       (q1966978-distance real space y x)
       radius))
     (q1966978-less
      real
      (q1966978-absolute-value
       real
       (q1966978-subtract
        real
        (q1966978-function-at function y)
        (q1966978-function-at function x)))
      epsilon))))

(defun-sk q1966978-continuity-radius-p
    (real space function x epsilon)
  (exists (radius)
    (and
     (q1966978-positive-p real radius)
     (q1966978-continuity-ball-p
      real space function x epsilon radius))))

(defun-sk q1966978-continuous-function-p
    (real space function)
  (forall (x epsilon)
    (implies
     (and
      (q1966978-member-p space x)
      (q1966978-positive-p real epsilon))
     (q1966978-continuity-radius-p
      real space function x epsilon))))

(defun q1966978-bounded-continuous-p
    (real space family function)
  (and
   (q1966978-real-function-p real space function)
   (q1966978-bounded-function-p real space function)
   (q1966978-continuous-function-p real space function)
   (q1966978-measurable-function-p
    real space family function)))

;; Exact bounded Lebesgue integration.  A nonnegative bounded measurable
;; function is integrated as the supremum of the integrals of all measurable
;; finite-range nonnegative simple functions below it.  Signed integrals are
;; the difference of the positive- and negative-part lower integrals.

(defun q1966978-values-nonnegative-p (real values)
  (if (consp values)
      (and
       (q1966978-nonnegative-p real (car values))
       (q1966978-values-nonnegative-p real (cdr values)))
    (equal values nil)))

(defun-sk q1966978-range-in-values-p
    (space function values)
  (forall (x)
    (implies
     (q1966978-member-p space x)
     (member-equal
      (q1966978-function-at function x)
      values))))

(defun q1966978-simple-function-p
    (real space family function values)
  (and
   (true-listp values)
   (no-duplicatesp-equal values)
   (q1966978-values-nonnegative-p real values)
   (q1966978-real-function-p real space function)
   (q1966978-measurable-function-p
    real space family function)
   (q1966978-range-in-values-p
    space function values)))

(defun-sk q1966978-fiber-constructor-laws-p (space)
  (forall (function value x)
    (iff
     (q1966978-set-member-p
      (q1966978-fiber-set space function value)
      x)
     (and
      (q1966978-member-p space x)
      (equal
       (q1966978-function-at function x)
       value)))))

(defun q1966978-simple-integral
    (real space measure function values)
  (if (consp values)
      (q1966978-add
       real
       (q1966978-multiply
        real
        (car values)
        (q1966978-measure-value
         measure
         (q1966978-fiber-set
          space function (car values))))
       (q1966978-simple-integral
        real space measure function (cdr values)))
    (q1966978-zero real)))

(defun-sk q1966978-simple-below-p
    (real space simple function)
  (forall (x)
    (implies
     (q1966978-member-p space x)
     (q1966978-leq
      real
      (q1966978-function-at simple x)
      (q1966978-function-at function x)))))

(defun-sk q1966978-nonnegative-function-p
    (real space function)
  (forall (x)
    (implies
     (q1966978-member-p space x)
     (q1966978-nonnegative-p
      real (q1966978-function-at function x)))))

(defun q1966978-nonnegative-bounded-measurable-p
    (real space family function)
  (and
   (q1966978-real-function-p real space function)
   (q1966978-nonnegative-function-p real space function)
   (q1966978-bounded-function-p real space function)
   (q1966978-measurable-function-p
    real space family function)))

(defun-sk q1966978-lintegral-upper-bound-p
    (real space family measure function bound)
  (forall (simple values)
    (implies
     (and
      (q1966978-simple-function-p
       real space family simple values)
      (q1966978-simple-below-p
       real space simple function))
     (q1966978-leq
      real
      (q1966978-simple-integral
       real space measure simple values)
      bound))))

(defun-sk q1966978-lintegral-least-p
    (real space family measure function value)
  (forall (bound)
    (implies
     (and
      (q1966978-member-p real bound)
      (q1966978-lintegral-upper-bound-p
       real space family measure function bound))
     (q1966978-leq real value bound))))

(defun q1966978-lintegral-value-p
    (real space family measure function value)
  (and
   (q1966978-nonnegative-bounded-measurable-p
    real space family function)
   (q1966978-nonnegative-p real value)
   (q1966978-lintegral-upper-bound-p
    real space family measure function value)
   (q1966978-lintegral-least-p
    real space family measure function value)))

(defun-sk q1966978-lintegral-operation-p
    (real space family measure)
  (forall (function)
    (implies
     (q1966978-nonnegative-bounded-measurable-p
      real space family function)
     (q1966978-lintegral-value-p
      real space family measure function
      (q1966978-lintegral-value measure function)))))

(defun-sk q1966978-function-constructor-laws-p
    (real space)
  (forall (function frequency x)
    (and
     (implies
      (q1966978-member-p space x)
      (equal
       (q1966978-function-at
        (q1966978-zero-function real space) x)
       (q1966978-zero real)))
     (implies
      (q1966978-member-p space x)
      (equal
       (q1966978-function-at
        (q1966978-positive-part-function real function) x)
       (let ((value
              (q1966978-function-at function x)))
         (if (q1966978-less
              real value (q1966978-zero real))
             (q1966978-zero real)
           value))))
     (implies
      (q1966978-member-p space x)
      (equal
       (q1966978-function-at
        (q1966978-negative-part-function real function) x)
       (let ((value
              (q1966978-function-at function x)))
         (if (q1966978-less
              real value (q1966978-zero real))
             (q1966978-negate real value)
           (q1966978-zero real)))))
     (implies
      (and
       (q1966978-member-p space frequency)
       (q1966978-member-p space x))
      (equal
       (q1966978-function-at
        (q1966978-cos-inner-function
         real space frequency)
        x)
       (q1966978-cosine
        real
        (q1966978-inner real space x frequency))))
     (implies
      (and
       (q1966978-member-p space frequency)
       (q1966978-member-p space x))
      (equal
       (q1966978-function-at
        (q1966978-sin-inner-function
         real space frequency)
        x)
       (q1966978-sine
        real
        (q1966978-inner real space x frequency)))))))

(defun-sk q1966978-positive-negative-valid-p
    (real space family)
  (forall (function)
    (implies
     (and
      (q1966978-real-function-p real space function)
      (q1966978-bounded-function-p real space function)
      (q1966978-measurable-function-p
       real space family function))
     (and
      (q1966978-nonnegative-bounded-measurable-p
       real space family
       (q1966978-positive-part-function real function))
      (q1966978-nonnegative-bounded-measurable-p
       real space family
       (q1966978-negative-part-function real function))))))

(defun q1966978-real-integral-value (real measure function)
  (q1966978-subtract
   real
   (q1966978-lintegral-value
    measure
    (q1966978-positive-part-function real function))
   (q1966978-lintegral-value
    measure
    (q1966978-negative-part-function real function))))

(defun-sk q1966978-sequence-lintegral-operation-p
    (real space family measure-sequence)
  (forall (n)
    (implies
     (natp n)
     (q1966978-lintegral-operation-p
      real space family
      (q1966978-measure-at measure-sequence n)))))

;; The real and imaginary parts of Mathlib's
;;   charFun μ t = integral x, exp(inner x t * I) dμ
;; are respectively the integrals of cos(inner x t) and sin(inner x t).

(defun q1966978-charfun-real
    (real space measure frequency)
  (q1966978-real-integral-value
   real measure
   (q1966978-cos-inner-function
    real space frequency)))

(defun q1966978-charfun-imag
    (real space measure frequency)
  (q1966978-real-integral-value
   real measure
   (q1966978-sin-inner-function
    real space frequency)))

(defun-sk q1966978-character-integrands-valid-p
    (real space family)
  (forall (frequency)
    (implies
     (q1966978-member-p space frequency)
     (and
      (q1966978-real-function-p
       real space
       (q1966978-cos-inner-function
        real space frequency))
      (q1966978-bounded-function-p
       real space
       (q1966978-cos-inner-function
        real space frequency))
      (q1966978-measurable-function-p
       real space family
       (q1966978-cos-inner-function
        real space frequency))
      (q1966978-real-function-p
       real space
       (q1966978-sin-inner-function
        real space frequency))
      (q1966978-bounded-function-p
       real space
       (q1966978-sin-inner-function
        real space frequency))
      (q1966978-measurable-function-p
       real space family
       (q1966978-sin-inner-function
        real space frequency))))))

;; Weak convergence is the standard bounded-continuous-test-function
;; characterization of the weak topology on probability measures.

(defun-sk q1966978-integral-convergence-tail-p
    (real measure-sequence limit-measure function epsilon start)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp start)
      (<= start n))
     (q1966978-less
      real
      (q1966978-absolute-value
       real
       (q1966978-subtract
        real
        (q1966978-real-integral-value
         real
         (q1966978-measure-at measure-sequence n)
         function)
        (q1966978-real-integral-value
         real limit-measure function)))
      epsilon))))

(defun-sk q1966978-integral-convergence-start-p
    (real measure-sequence limit-measure function epsilon)
  (exists (start)
    (and
     (natp start)
     (q1966978-integral-convergence-tail-p
      real measure-sequence limit-measure
      function epsilon start))))

(defun-sk q1966978-integral-converges-p
    (real measure-sequence limit-measure function)
  (forall (epsilon)
    (implies
     (q1966978-positive-p real epsilon)
     (q1966978-integral-convergence-start-p
      real measure-sequence limit-measure
      function epsilon))))

(defun-sk q1966978-weak-convergence-p
    (real space family measure-sequence limit-measure)
  (forall (function)
    (implies
     (q1966978-bounded-continuous-p
      real space family function)
     (q1966978-integral-converges-p
      real measure-sequence limit-measure function))))

;; Complex convergence is represented by simultaneous convergence of real and
;; imaginary coordinates.  This is exactly the product/Euclidean topology on
;; C, not a replacement of C by a proper subdomain.

(defun-sk q1966978-charfun-convergence-tail-p
    (real space measure-sequence limit-measure
     frequency epsilon start)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp start)
      (<= start n))
     (and
      (q1966978-less
       real
       (q1966978-absolute-value
        real
        (q1966978-subtract
         real
         (q1966978-charfun-real
          real space
          (q1966978-measure-at measure-sequence n)
          frequency)
         (q1966978-charfun-real
          real space limit-measure frequency)))
       epsilon)
      (q1966978-less
       real
       (q1966978-absolute-value
        real
        (q1966978-subtract
         real
         (q1966978-charfun-imag
          real space
          (q1966978-measure-at measure-sequence n)
          frequency)
         (q1966978-charfun-imag
          real space limit-measure frequency)))
       epsilon)))))

(defun-sk q1966978-charfun-convergence-start-p
    (real space measure-sequence limit-measure frequency epsilon)
  (exists (start)
    (and
     (natp start)
     (q1966978-charfun-convergence-tail-p
      real space measure-sequence limit-measure
      frequency epsilon start))))

(defun-sk q1966978-charfun-converges-p
    (real space measure-sequence limit-measure frequency)
  (forall (epsilon)
    (implies
     (q1966978-positive-p real epsilon)
     (q1966978-charfun-convergence-start-p
      real space measure-sequence limit-measure
      frequency epsilon))))

(defun-sk q1966978-pointwise-charfun-convergence-p
    (real space measure-sequence limit-measure)
  (forall (frequency)
    (implies
     (q1966978-member-p space frequency)
     (q1966978-charfun-converges-p
      real space measure-sequence limit-measure frequency))))

(defun q1966978-canonical-context-p
    (real space borel measure-sequence limit-measure)
  (and
   (q1966978-real-structure-p real)
   (q1966978-finite-inner-product-space-p real space)
   (q1966978-set-constructor-laws-p real space)
   (q1966978-borel-space-p real space borel)
   (q1966978-upper-ray-constructor-laws-p real space)
   (q1966978-fiber-constructor-laws-p space)
   (q1966978-function-constructor-laws-p real space)
   (q1966978-positive-negative-valid-p real space borel)
   (q1966978-trigonometric-sequence-laws-p real)
   (q1966978-trigonometric-laws-p real)
   (q1966978-character-integrands-valid-p
    real space borel)
   (q1966978-probability-measure-p
    real space borel limit-measure)
   (q1966978-probability-measure-sequence-p
    real space borel measure-sequence)
   (q1966978-lintegral-operation-p
    real space borel limit-measure)
   (q1966978-sequence-lintegral-operation-p
    real space borel measure-sequence)))

(defun thousand-theorems-q1966978-canonical-statement
    (real space borel measure-sequence limit-measure)
  (implies
   (q1966978-canonical-context-p
    real space borel measure-sequence limit-measure)
   (iff
    (q1966978-weak-convergence-p
     real space borel measure-sequence limit-measure)
    (q1966978-pointwise-charfun-convergence-p
     real space measure-sequence limit-measure))))

(value-triple :itpeval-statement-checked)
:q
