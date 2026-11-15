;; Statement-only formalization of thousand-theorems corpus artifact Q966837,
;; "Cramér–Wold theorem": convergence in distribution in a finite-dimensional
;; real inner-product space is equivalent to convergence in distribution of
;; every scalar inner-product projection. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; The source theorem is generic over two probability spaces and a
;; finite-dimensional real inner-product space.  The conservative interfaces
;; below represent arbitrary carriers, subsets, functions, sigma-algebras,
;; and measures.  Their mathematical laws are explicit in the statement
;; predicate; no carrier, set, function, or measure is replaced by a finite
;; table.

;; Carriers, arbitrary subsets, and arbitrary functions.

(defstub q966837-member-p (space value) t)
(defstub q966837-set-member-p (space set value) t)
(defstub q966837-empty-set (space) t)
(defstub q966837-full-set (space) t)
(defstub q966837-complement-set (space set) t)
(defstub q966837-set-sequence-value (sequence index) t)
(defstub q966837-countable-union-set (space sequence) t)

(defstub q966837-function-value (function argument) t)
(defstub q966837-sequence-function (sequence index) t)
(defstub q966837-preimage-set
  (source-space target-space function target-set)
  t)
(defstub q966837-disagreement-set
  (source-space target-space left-function right-function)
  t)

(defun-sk q966837-valid-set-p (space set)
  (forall (x)
    (implies
     (q966837-set-member-p space set x)
     (q966837-member-p space x))))

(defun-sk q966837-set-ext-equal-p (space left right)
  (forall (x)
    (iff
     (q966837-set-member-p space left x)
     (q966837-set-member-p space right x))))

(defun-sk q966837-subset-p (space left right)
  (forall (x)
    (implies
     (q966837-set-member-p space left x)
     (q966837-set-member-p space right x))))

(defun-sk q966837-union-member-exists-p
    (space sequence value)
  (exists (index)
    (and
     (natp index)
     (q966837-set-member-p
      space
      (q966837-set-sequence-value sequence index)
      value))))

(defun-sk q966837-set-sequence-valid-p (space sequence)
  (forall (index)
    (implies
     (natp index)
     (q966837-valid-set-p
      space
      (q966837-set-sequence-value sequence index)))))

(defun-sk q966837-function-p
    (source-space target-space function)
  (forall (x)
    (implies
     (q966837-member-p source-space x)
     (q966837-member-p
      target-space
      (q966837-function-value function x)))))

(defun-sk q966837-functions-ext-equal-p
    (source-space left-function right-function)
  (forall (x)
    (implies
     (q966837-member-p source-space x)
     (equal
      (q966837-function-value left-function x)
      (q966837-function-value right-function x)))))

(defun-sk q966837-set-representation-laws-p ()
  (forall (space set left right sequence value)
    (and
     (q966837-valid-set-p
      space (q966837-empty-set space))
     (q966837-valid-set-p
      space (q966837-full-set space))
     (q966837-valid-set-p
      space (q966837-complement-set space set))
     (q966837-valid-set-p
      space (q966837-countable-union-set space sequence))
     (not
      (q966837-set-member-p
       space (q966837-empty-set space) value))
     (iff
      (q966837-set-member-p
       space (q966837-full-set space) value)
      (q966837-member-p space value))
     (iff
      (q966837-set-member-p
       space (q966837-complement-set space set) value)
      (and
       (q966837-member-p space value)
       (not (q966837-set-member-p space set value))))
     (iff
      (q966837-set-member-p
       space (q966837-countable-union-set space sequence) value)
      (and
       (q966837-member-p space value)
       (q966837-union-member-exists-p
        space sequence value)))
     (implies
      (q966837-set-ext-equal-p space left right)
      (equal left right)))))

(defun-sk q966837-function-representation-laws-p ()
  (forall
      (source-space target-space function target-set
       left-function right-function value)
    (and
     (iff
      (q966837-set-member-p
       source-space
       (q966837-preimage-set
        source-space target-space function target-set)
       value)
      (and
       (q966837-member-p source-space value)
       (q966837-set-member-p
        target-space target-set
        (q966837-function-value function value))))
     (iff
      (q966837-set-member-p
       source-space
       (q966837-disagreement-set
        source-space target-space
        left-function right-function)
       value)
      (and
       (q966837-member-p source-space value)
       (not
        (equal
         (q966837-function-value left-function value)
         (q966837-function-value right-function value)))))
     (implies
      (q966837-functions-ext-equal-p
       source-space left-function right-function)
      (equal left-function right-function)))))

;; A Dedekind-complete ordered field presents the real numbers.

(defstub q966837-r-zero (real) t)
(defstub q966837-r-one (real) t)
(defstub q966837-r-add (real left right) t)
(defstub q966837-r-multiply (real left right) t)
(defstub q966837-r-negate (real value) t)
(defstub q966837-r-inverse (real value) t)
(defstub q966837-r-less (real left right) t)

(defun q966837-r-subtract (real left right)
  (q966837-r-add
   real left (q966837-r-negate real right)))

(defun q966837-r-leq (real left right)
  (not (q966837-r-less real right left)))

(defun q966837-r-positive-p (real value)
  (and
   (q966837-member-p real value)
   (q966837-r-less
    real (q966837-r-zero real) value)))

(defun q966837-r-abs (real value)
  (if (q966837-r-less
       real value (q966837-r-zero real))
      (q966837-r-negate real value)
    value))

(defun q966837-r-distance (real left right)
  (q966837-r-abs
   real (q966837-r-subtract real left right)))

(defun-sk q966837-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q966837-member-p real x)
      (q966837-member-p real y)
      (q966837-member-p real z))
     (let* ((zero (q966837-r-zero real))
            (one (q966837-r-one real))
            (xy-add (q966837-r-add real x y))
            (yz-add (q966837-r-add real y z))
            (xy-mul (q966837-r-multiply real x y))
            (yz-mul (q966837-r-multiply real y z))
            (neg-x (q966837-r-negate real x))
            (inv-x (q966837-r-inverse real x)))
       (and
        (q966837-member-p real xy-add)
        (q966837-member-p real xy-mul)
        (q966837-member-p real neg-x)
        (q966837-member-p real inv-x)
        (equal
         (q966837-r-add real xy-add z)
         (q966837-r-add real x yz-add))
        (equal xy-add (q966837-r-add real y x))
        (equal (q966837-r-add real x zero) x)
        (equal (q966837-r-add real x neg-x) zero)
        (equal
         (q966837-r-multiply real xy-mul z)
         (q966837-r-multiply real x yz-mul))
        (equal xy-mul (q966837-r-multiply real y x))
        (equal (q966837-r-multiply real x one) x)
        (equal (q966837-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q966837-r-multiply real x inv-x)
          one))
        (equal
         (q966837-r-multiply
          real x (q966837-r-add real y z))
         (q966837-r-add
          real
          (q966837-r-multiply real x y)
          (q966837-r-multiply real x z))))))))

(defun-sk q966837-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q966837-member-p real x)
      (q966837-member-p real y)
      (q966837-member-p real z))
     (let ((zero (q966837-r-zero real)))
       (and
        (not (q966837-r-less real x x))
        (or
         (equal x y)
         (q966837-r-less real x y)
         (q966837-r-less real y x))
        (implies
         (and
          (q966837-r-less real x y)
          (q966837-r-less real y z))
         (q966837-r-less real x z))
        (implies
         (q966837-r-less real x y)
         (q966837-r-less
          real
          (q966837-r-add real x z)
          (q966837-r-add real y z)))
        (implies
         (and
          (q966837-r-less real zero x)
          (q966837-r-less real zero y))
         (q966837-r-less
          real zero
          (q966837-r-multiply real x y))))))))

(defun-sk q966837-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q966837-member-p real x)
     (q966837-set-member-p real set x))))

(defun-sk q966837-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q966837-member-p real x)
      (q966837-set-member-p real set x))
     (q966837-r-leq real x bound))))

(defun-sk q966837-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q966837-member-p real bound)
     (q966837-r-upper-bound-p real set bound))))

(defun-sk q966837-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q966837-member-p real supremum)
     (q966837-r-upper-bound-p real set supremum)
     (implies
      (and
       (q966837-member-p real bound)
       (q966837-r-upper-bound-p real set bound))
      (q966837-r-leq real supremum bound)))))

(defun-sk q966837-r-supremum-exists-p (real set)
  (exists (supremum)
    (q966837-r-supremum-p real set supremum)))

(defun-sk q966837-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q966837-valid-set-p real set)
      (q966837-r-set-nonempty-p real set)
      (q966837-r-bounded-above-p real set))
     (q966837-r-supremum-exists-p real set))))

(defun q966837-real-field-p (real)
  (let ((zero (q966837-r-zero real))
        (one (q966837-r-one real)))
    (and
     (q966837-member-p real zero)
     (q966837-member-p real one)
     (not (equal zero one))
     (q966837-r-field-laws-p real)
     (q966837-r-order-laws-p real)
     (q966837-r-less real zero one)
     (q966837-r-dedekind-complete-p real))))

;; A normed real inner-product space.

(defstub q966837-v-zero (space) t)
(defstub q966837-v-add (space left right) t)
(defstub q966837-v-negate (space value) t)
(defstub q966837-v-smul (real space scalar vector) t)
(defstub q966837-v-inner (real space left right) t)
(defstub q966837-v-norm (real space vector) t)

(defun q966837-v-subtract (space left right)
  (q966837-v-add
   space left (q966837-v-negate space right)))

(defun q966837-v-distance (real space left right)
  (q966837-v-norm
   real space (q966837-v-subtract space left right)))

(defun-sk q966837-vector-add-norm-inner-laws-p (real space)
  (forall (x y z)
    (implies
     (and
      (q966837-member-p space x)
      (q966837-member-p space y)
      (q966837-member-p space z))
     (let* ((zero-v (q966837-v-zero space))
            (zero-r (q966837-r-zero real))
            (xy-add (q966837-v-add space x y))
            (yz-add (q966837-v-add space y z))
            (neg-x (q966837-v-negate space x))
            (norm-x (q966837-v-norm real space x))
            (norm-y (q966837-v-norm real space y))
            (inner-xx (q966837-v-inner real space x x)))
       (and
        (q966837-member-p space xy-add)
        (q966837-member-p space neg-x)
        (q966837-member-p real norm-x)
        (q966837-member-p real norm-y)
        (q966837-member-p real inner-xx)
        (q966837-member-p
         real
         (q966837-v-inner real space x y))
        (equal
         (q966837-v-add space xy-add z)
         (q966837-v-add space x yz-add))
        (equal xy-add (q966837-v-add space y x))
        (equal (q966837-v-add space x zero-v) x)
        (equal (q966837-v-add space x neg-x) zero-v)
        (q966837-r-leq real zero-r norm-x)
        (iff (equal norm-x zero-r)
             (equal x zero-v))
        (equal
         (q966837-v-norm real space neg-x)
         norm-x)
        (q966837-r-leq
         real
         (q966837-v-norm real space xy-add)
         (q966837-r-add real norm-x norm-y))
        (q966837-r-leq real zero-r inner-xx)
        (iff (equal inner-xx zero-r)
             (equal x zero-v))
        (equal
         (q966837-r-multiply real norm-x norm-x)
         inner-xx)
        (equal
         (q966837-v-inner real space x y)
         (q966837-v-inner real space y x))
        (equal
         (q966837-v-inner
          real space (q966837-v-add space x y) z)
         (q966837-r-add
          real
          (q966837-v-inner real space x z)
          (q966837-v-inner real space y z))))))))

(defun-sk q966837-vector-scalar-inner-laws-p (real space)
  (forall (a b x y)
    (implies
     (and
      (q966837-member-p real a)
      (q966837-member-p real b)
      (q966837-member-p space x)
      (q966837-member-p space y))
     (let ((zero-r (q966837-r-zero real))
           (one-r (q966837-r-one real))
           (zero-v (q966837-v-zero space)))
       (and
        (q966837-member-p
         space (q966837-v-smul real space a x))
        (equal
         (q966837-v-smul real space one-r x)
         x)
        (equal
         (q966837-v-smul
          real space
          (q966837-r-multiply real a b)
          x)
         (q966837-v-smul
          real space a
          (q966837-v-smul real space b x)))
        (equal
         (q966837-v-smul
          real space
          (q966837-r-add real a b)
          x)
         (q966837-v-add
          space
          (q966837-v-smul real space a x)
          (q966837-v-smul real space b x)))
        (equal
         (q966837-v-smul
          real space a
          (q966837-v-add space x y))
         (q966837-v-add
          space
          (q966837-v-smul real space a x)
          (q966837-v-smul real space a y)))
        (equal
         (q966837-v-smul real space zero-r x)
         zero-v)
        (equal
         (q966837-v-smul real space a zero-v)
         zero-v)
        (equal
         (q966837-v-inner
          real space
          (q966837-v-smul real space a x)
          y)
         (q966837-r-multiply
          real a
          (q966837-v-inner real space x y)))
        (equal
         (q966837-v-norm
          real space
          (q966837-v-smul real space a x))
         (q966837-r-multiply
          real
          (q966837-r-abs real a)
          (q966837-v-norm real space x))))))))

(defun q966837-real-inner-product-space-p (real space)
  (and
   (q966837-member-p
    space (q966837-v-zero space))
   (q966837-vector-add-norm-inner-laws-p real space)
   (q966837-vector-scalar-inner-laws-p real space)))

;; Finite dimensionality is represented by an arbitrary finite spanning
;; coordinate family, not by making the vector carrier finite.

(defstub q966837-basis-vector (space basis index) t)
(defstub q966837-coordinate
  (real space basis vector index)
  t)

(defun q966837-linear-combination
    (real space basis vector count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q966837-v-zero space)
    (let ((index (- count 1)))
      (q966837-v-add
       space
       (q966837-linear-combination
        real space basis vector index)
       (q966837-v-smul
        real space
        (q966837-coordinate
         real space basis vector index)
        (q966837-basis-vector
         space basis index))))))

(defun-sk q966837-spanning-family-typed-p
    (real space dimension basis)
  (forall (index vector)
    (and
     (implies
      (and
       (natp index)
       (< index dimension))
      (q966837-member-p
       space
       (q966837-basis-vector space basis index)))
     (implies
      (and
       (q966837-member-p space vector)
       (natp index)
       (< index dimension))
      (q966837-member-p
       real
       (q966837-coordinate
        real space basis vector index))))))

(defun-sk q966837-spanning-family-expands-p
    (real space dimension basis)
  (forall (vector)
    (implies
     (q966837-member-p space vector)
     (equal
      (q966837-linear-combination
       real space basis vector dimension)
      vector))))

(defun q966837-finite-spanning-family-p
    (real space dimension basis)
  (and
   (natp dimension)
   (q966837-spanning-family-typed-p
    real space dimension basis)
   (q966837-spanning-family-expands-p
    real space dimension basis)))

(defun-sk q966837-finite-dimensional-p (real space)
  (exists (dimension basis)
    (q966837-finite-spanning-family-p
     real space dimension basis)))

;; Metric open sets, sigma-algebras, and the Borel measurable structures.

(defstub q966837-measurable-set-p (sigma set) t)

(defun-sk q966837-r-ball-contained-p
    (real set center radius)
  (forall (point)
    (implies
     (and
      (q966837-member-p real point)
      (q966837-r-less
       real
       (q966837-r-distance real point center)
       radius))
     (q966837-set-member-p real set point))))

(defun-sk q966837-r-open-radius-exists-p
    (real set center)
  (exists (radius)
    (and
     (q966837-r-positive-p real radius)
     (q966837-r-ball-contained-p
      real set center radius))))

(defun-sk q966837-r-open-set-p (real set)
  (forall (center)
    (implies
     (q966837-set-member-p real set center)
     (q966837-r-open-radius-exists-p
      real set center))))

(defun-sk q966837-v-ball-contained-p
    (real space set center radius)
  (forall (point)
    (implies
     (and
      (q966837-member-p space point)
      (q966837-r-less
       real
       (q966837-v-distance real space point center)
       radius))
     (q966837-set-member-p space set point))))

(defun-sk q966837-v-open-radius-exists-p
    (real space set center)
  (exists (radius)
    (and
     (q966837-r-positive-p real radius)
     (q966837-v-ball-contained-p
      real space set center radius))))

(defun-sk q966837-v-open-set-p (real space set)
  (forall (center)
    (implies
     (q966837-set-member-p space set center)
     (q966837-v-open-radius-exists-p
      real space set center))))

(defun q966837-r-closed-set-p (real set)
  (and
   (q966837-valid-set-p real set)
   (q966837-r-open-set-p
    real (q966837-complement-set real set))))

(defun q966837-v-closed-set-p (real space set)
  (and
   (q966837-valid-set-p space set)
   (q966837-v-open-set-p
    real space
    (q966837-complement-set space set))))

(defun-sk q966837-sigma-valid-p (space sigma)
  (forall (set)
    (implies
     (q966837-measurable-set-p sigma set)
     (q966837-valid-set-p space set))))

(defun-sk q966837-sigma-complement-closed-p
    (space sigma)
  (forall (set)
    (implies
     (q966837-measurable-set-p sigma set)
     (q966837-measurable-set-p
      sigma
      (q966837-complement-set space set)))))

(defun-sk q966837-measurable-set-sequence-p
    (sigma sequence)
  (forall (index)
    (implies
     (natp index)
     (q966837-measurable-set-p
      sigma
      (q966837-set-sequence-value sequence index)))))

(defun-sk q966837-sigma-union-closed-p (space sigma)
  (forall (sequence)
    (implies
     (q966837-measurable-set-sequence-p sigma sequence)
     (q966837-measurable-set-p
      sigma
      (q966837-countable-union-set space sequence)))))

(defun q966837-sigma-algebra-p (space sigma)
  (and
   (q966837-sigma-valid-p space sigma)
   (q966837-measurable-set-p
    sigma (q966837-empty-set space))
   (q966837-sigma-complement-closed-p space sigma)
   (q966837-sigma-union-closed-p space sigma)))

(defun-sk q966837-sigma-contains-r-opens-p
    (real sigma)
  (forall (set)
    (implies
     (and
      (q966837-valid-set-p real set)
      (q966837-r-open-set-p real set))
     (q966837-measurable-set-p sigma set))))

(defun-sk q966837-sigma-contains-v-opens-p
    (real space sigma)
  (forall (set)
    (implies
     (and
      (q966837-valid-set-p space set)
      (q966837-v-open-set-p real space set))
     (q966837-measurable-set-p sigma set))))

(defun-sk q966837-r-borel-minimal-p
    (real borel)
  (forall (alternate set)
    (implies
     (and
      (q966837-sigma-algebra-p real alternate)
      (q966837-sigma-contains-r-opens-p
       real alternate)
      (q966837-measurable-set-p borel set))
     (q966837-measurable-set-p alternate set))))

(defun-sk q966837-v-borel-minimal-p
    (real space borel)
  (forall (alternate set)
    (implies
     (and
      (q966837-sigma-algebra-p space alternate)
      (q966837-sigma-contains-v-opens-p
       real space alternate)
      (q966837-measurable-set-p borel set))
     (q966837-measurable-set-p alternate set))))

(defun q966837-r-borel-space-p (real borel)
  (and
   (q966837-sigma-algebra-p real borel)
   (q966837-sigma-contains-r-opens-p real borel)
   (q966837-r-borel-minimal-p real borel)))

(defun q966837-v-borel-space-p
    (real space borel)
  (and
   (q966837-sigma-algebra-p space borel)
   (q966837-sigma-contains-v-opens-p
    real space borel)
   (q966837-v-borel-minimal-p
    real space borel)))

;; Probability measures are real-valued because every probability measure is
;; finite. Countable additivity is expressed by convergence of finite partial
;; sums, exactly preserving arbitrary countable measurable unions.

(defstub q966837-measure-value (real measure set) t)

(defun q966837-finite-measure-sum
    (real measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q966837-r-zero real)
    (let ((index (- count 1)))
      (q966837-r-add
       real
       (q966837-finite-measure-sum
        real measure sequence index)
       (q966837-measure-value
        real measure
        (q966837-set-sequence-value
         sequence index))))))

(defun-sk q966837-set-sequence-pairwise-disjoint-p
    (space sequence)
  (forall (left-index right-index value)
    (implies
     (and
      (natp left-index)
      (natp right-index)
      (not (equal left-index right-index)))
     (not
      (and
       (q966837-set-member-p
        space
        (q966837-set-sequence-value
         sequence left-index)
        value)
       (q966837-set-member-p
        space
        (q966837-set-sequence-value
         sequence right-index)
        value))))))

(defun-sk q966837-measure-values-p
    (real space measure)
  (forall (set)
    (implies
     (q966837-valid-set-p space set)
     (let ((value
            (q966837-measure-value real measure set)))
       (and
        (q966837-member-p real value)
        (q966837-r-leq
         real (q966837-r-zero real) value)
        (q966837-r-leq
         real value (q966837-r-one real)))))))

(defun-sk q966837-measure-monotone-p
    (real space measure)
  (forall (left right)
    (implies
     (and
      (q966837-valid-set-p space left)
      (q966837-valid-set-p space right)
      (q966837-subset-p space left right))
     (q966837-r-leq
      real
      (q966837-measure-value real measure left)
      (q966837-measure-value real measure right)))))

(defun-sk q966837-measurable-hull-exists-p
    (real space sigma measure set)
  (exists (hull)
    (and
     (q966837-measurable-set-p sigma hull)
     (q966837-subset-p space set hull)
     (equal
      (q966837-measure-value real measure set)
      (q966837-measure-value real measure hull)))))

(defun-sk q966837-measure-trimmed-p
    (real space sigma measure)
  (forall (set)
    (implies
     (q966837-valid-set-p space set)
     (q966837-measurable-hull-exists-p
      real space sigma measure set))))

(defun-sk q966837-measure-sum-tail-p
    (real measure sequence total epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (natp cutoff)
      (<= cutoff count))
     (q966837-r-less
      real
      (q966837-r-distance
       real
       (q966837-finite-measure-sum
        real measure sequence count)
       total)
      epsilon))))

(defun-sk q966837-measure-sum-cutoff-exists-p
    (real measure sequence total epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q966837-measure-sum-tail-p
      real measure sequence total epsilon cutoff))))

(defun-sk q966837-measure-series-converges-p
    (real measure sequence total)
  (forall (epsilon)
    (implies
     (q966837-r-positive-p real epsilon)
     (q966837-measure-sum-cutoff-exists-p
      real measure sequence total epsilon))))

(defun-sk q966837-measure-countably-additive-p
    (real space sigma measure)
  (forall (sequence)
    (implies
     (and
      (q966837-measurable-set-sequence-p
       sigma sequence)
      (q966837-set-sequence-pairwise-disjoint-p
       space sequence))
     (q966837-measure-series-converges-p
      real measure sequence
      (q966837-measure-value
       real measure
       (q966837-countable-union-set
        space sequence))))))

(defun q966837-probability-measure-p
    (real space sigma measure)
  (and
   (q966837-sigma-algebra-p space sigma)
   (q966837-measure-values-p real space measure)
   (equal
    (q966837-measure-value
     real measure (q966837-empty-set space))
    (q966837-r-zero real))
   (equal
    (q966837-measure-value
     real measure (q966837-full-set space))
    (q966837-r-one real))
   (q966837-measure-monotone-p
    real space measure)
   ;; Values on arbitrary sets are the induced outer measure: every set has
   ;; a measurable hull of exactly the same mass.
   (q966837-measure-trimmed-p
    real space sigma measure)
   (q966837-measure-countably-additive-p
    real space sigma measure)))

;; Measurable and almost-everywhere measurable functions.

(defun-sk q966837-measurable-function-p
    (source-space source-sigma
     target-space target-sigma function)
  (forall (set)
    (and
     (q966837-function-p
      source-space target-space function)
     (implies
      (q966837-measurable-set-p target-sigma set)
      (q966837-measurable-set-p
       source-sigma
       (q966837-preimage-set
        source-space target-space function set))))))

(defun q966837-ae-equal-p
    (real source-space target-space measure
     left-function right-function)
  (equal
   (q966837-measure-value
    real measure
    (q966837-disagreement-set
     source-space target-space
     left-function right-function))
   (q966837-r-zero real)))

(defun-sk q966837-aemeasurable-p
    (real source-space source-sigma measure
     target-space target-sigma function)
  (exists (measurable-version)
    (and
     (q966837-function-p
      source-space target-space function)
     (q966837-measurable-function-p
      source-space source-sigma
      target-space target-sigma
      measurable-version)
     (q966837-ae-equal-p
      real source-space target-space measure
      function measurable-version))))

(defun-sk q966837-sequence-functions-p
    (source-space target-space sequence)
  (forall (index)
    (implies
     (natp index)
     (q966837-function-p
      source-space target-space
      (q966837-sequence-function
       sequence index)))))

(defun-sk q966837-sequence-aemeasurable-p
    (real source-space source-sigma measure
     target-space target-sigma sequence)
  (forall (index)
    (implies
     (natp index)
     (q966837-aemeasurable-p
      real source-space source-sigma measure
      target-space target-sigma
      (q966837-sequence-function
       sequence index)))))

;; Scalar projections x |-> <x,t>.

(defstub q966837-projection-function
  (real space function vector)
  t)
(defstub q966837-projection-sequence
  (real space sequence vector)
  t)

(defun-sk q966837-projection-representation-laws-p
    (real space)
  (forall
      (source-space function sequence vector argument index)
    (and
     (implies
      (and
       (q966837-function-p source-space space function)
       (q966837-member-p space vector)
       (q966837-member-p source-space argument))
      (equal
       (q966837-function-value
        (q966837-projection-function
         real space function vector)
        argument)
       (q966837-v-inner
        real space
        (q966837-function-value function argument)
        vector)))
     (implies
      (and
       (natp index)
       (q966837-member-p space vector))
      (equal
       (q966837-sequence-function
        (q966837-projection-sequence
         real space sequence vector)
        index)
       (q966837-projection-function
        real space
        (q966837-sequence-function sequence index)
        vector))))))

;; Portmanteau closed-set convergence.  For probability measures on the
;; finite-dimensional metric spaces above, this is bidirectionally equivalent
;; to Mathlib's weak topology on ProbabilityMeasure and hence to the source
;; TendstoInDistribution structure.

(defun-sk q966837-portmanteau-tail-p
    (real source-space target-space source-measure
     limit-source-space limit-measure sequence limit-function
     closed-set epsilon cutoff)
  (forall (index)
    (implies
     (and
      (natp index)
      (natp cutoff)
      (<= cutoff index))
     (q966837-r-leq
      real
      (q966837-measure-value
       real source-measure
       (q966837-preimage-set
        source-space target-space
        (q966837-sequence-function sequence index)
        closed-set))
      (q966837-r-add
       real
       (q966837-measure-value
        real limit-measure
        (q966837-preimage-set
         limit-source-space target-space
         limit-function closed-set))
       epsilon)))))

(defun-sk q966837-portmanteau-cutoff-exists-p
    (real source-space target-space source-measure
     limit-source-space limit-measure sequence limit-function
     closed-set epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q966837-portmanteau-tail-p
      real source-space target-space source-measure
      limit-source-space limit-measure sequence limit-function
      closed-set epsilon cutoff))))

(defun-sk q966837-v-weak-convergence-p
    (real source-space target-space source-measure
     limit-source-space limit-measure sequence limit-function)
  (forall (closed-set epsilon)
    (implies
     (and
      (q966837-v-closed-set-p
       real target-space closed-set)
      (q966837-r-positive-p real epsilon))
     (q966837-portmanteau-cutoff-exists-p
      real source-space target-space source-measure
      limit-source-space limit-measure sequence limit-function
      closed-set epsilon))))

(defun-sk q966837-r-weak-convergence-p
    (real source-space source-measure
     limit-source-space limit-measure sequence limit-function)
  (forall (closed-set epsilon)
    (implies
     (and
      (q966837-r-closed-set-p real closed-set)
      (q966837-r-positive-p real epsilon))
     (q966837-portmanteau-cutoff-exists-p
      real source-space real source-measure
      limit-source-space limit-measure sequence limit-function
      closed-set epsilon))))

(defun q966837-v-tendsto-in-distribution-p
    (real source-space source-sigma source-measure
     target-space target-borel
     limit-source-space limit-source-sigma limit-measure
     sequence limit-function)
  (and
   (q966837-sequence-aemeasurable-p
    real source-space source-sigma source-measure
    target-space target-borel sequence)
   (q966837-aemeasurable-p
    real limit-source-space limit-source-sigma limit-measure
    target-space target-borel limit-function)
   (q966837-v-weak-convergence-p
    real source-space target-space source-measure
    limit-source-space limit-measure sequence limit-function)))

(defun q966837-r-tendsto-in-distribution-p
    (real real-borel
     source-space source-sigma source-measure
     limit-source-space limit-source-sigma limit-measure
     sequence limit-function)
  (and
   (q966837-sequence-aemeasurable-p
    real source-space source-sigma source-measure
    real real-borel sequence)
   (q966837-aemeasurable-p
    real limit-source-space limit-source-sigma limit-measure
    real real-borel limit-function)
   (q966837-r-weak-convergence-p
    real source-space source-measure
    limit-source-space limit-measure sequence limit-function)))

(defun-sk q966837-all-projections-converge-p
    (real real-borel source-space source-sigma source-measure
     target-space
     limit-source-space limit-source-sigma limit-measure
     sequence limit-function)
  (forall (vector)
    (implies
     (q966837-member-p target-space vector)
     (q966837-r-tendsto-in-distribution-p
      real real-borel
      source-space source-sigma source-measure
      limit-source-space limit-source-sigma limit-measure
      (q966837-projection-sequence
       real target-space sequence vector)
      (q966837-projection-function
       real target-space limit-function vector)))))

(defun-sk
    thousand-theorems-q966837-cramer-wold-theorem-statement
    ()
  (forall
      (real real-borel
       vector-space vector-borel
       sample-space sample-sigma probability
       limit-sample-space limit-sample-sigma limit-probability
       random-sequence limit-random-variable)
    (implies
     (and
      (q966837-set-representation-laws-p)
      (q966837-function-representation-laws-p)
      (q966837-real-field-p real)
      (q966837-r-borel-space-p real real-borel)
      (q966837-real-inner-product-space-p
       real vector-space)
      (q966837-finite-dimensional-p
       real vector-space)
      (q966837-v-borel-space-p
       real vector-space vector-borel)
      (q966837-sigma-algebra-p
       sample-space sample-sigma)
      (q966837-sigma-algebra-p
       limit-sample-space limit-sample-sigma)
      (q966837-probability-measure-p
       real sample-space sample-sigma probability)
      (q966837-probability-measure-p
       real limit-sample-space limit-sample-sigma
       limit-probability)
      (q966837-sequence-functions-p
       sample-space vector-space random-sequence)
      (q966837-function-p
       limit-sample-space vector-space
       limit-random-variable)
      (q966837-projection-representation-laws-p
       real vector-space)
      ;; These are exactly hX and hX' in the canonical Lean declaration.
      (q966837-sequence-aemeasurable-p
       real sample-space sample-sigma probability
       vector-space vector-borel random-sequence)
      (q966837-aemeasurable-p
       real
       limit-sample-space limit-sample-sigma limit-probability
       vector-space vector-borel limit-random-variable))
     (iff
      (q966837-v-tendsto-in-distribution-p
       real sample-space sample-sigma probability
       vector-space vector-borel
       limit-sample-space limit-sample-sigma limit-probability
       random-sequence limit-random-variable)
      (q966837-all-projections-converge-p
       real real-borel
       sample-space sample-sigma probability
       vector-space
       limit-sample-space limit-sample-sigma limit-probability
       random-sequence limit-random-variable)))))

(value-triple :itpeval-statement-checked)
:q
