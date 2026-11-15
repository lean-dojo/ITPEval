;; Statement-only formalization of thousand-theorems corpus artifact Q1050932,
;; "Hartogs's theorem": a function from complex two-space to a separable
;; complex Banach space that is analytic in each variable separately on an
;; open set is jointly analytic there. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Conservative interfaces present arbitrary carriers, operations, sets,
;; functions, sequences, and continuous linear maps. A Dedekind-complete
;; ordered field presents the reals, and real/imaginary coordinates present
;; the complex field. All algebraic, normed-space, completeness, separability,
;; openness, differentiability, and typing laws used by the statement are
;; explicit below.

;; The real numbers.

(defstub q1050932-r-member-p (real value) t)
(defstub q1050932-r-zero (real) t)
(defstub q1050932-r-one (real) t)
(defstub q1050932-r-add (real left right) t)
(defstub q1050932-r-multiply (real left right) t)
(defstub q1050932-r-negate (real value) t)
(defstub q1050932-r-inverse (real value) t)
(defstub q1050932-r-less (real left right) t)
(defstub q1050932-r-set-member-p (real set value) t)

(defun q1050932-r-leq (real left right)
  (not (q1050932-r-less real right left)))

(defun q1050932-r-positive-p (real value)
  (and
   (q1050932-r-member-p real value)
   (q1050932-r-less
    real (q1050932-r-zero real) value)))

(defun q1050932-r-max (real left right)
  (if (q1050932-r-less real left right)
      right
    left))

(defun-sk q1050932-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q1050932-r-member-p real x)
      (q1050932-r-member-p real y)
      (q1050932-r-member-p real z))
     (let* ((zero (q1050932-r-zero real))
            (one (q1050932-r-one real))
            (xy-add (q1050932-r-add real x y))
            (yz-add (q1050932-r-add real y z))
            (xy-mul (q1050932-r-multiply real x y))
            (yz-mul (q1050932-r-multiply real y z))
            (neg-x (q1050932-r-negate real x))
            (inv-x (q1050932-r-inverse real x)))
       (and
        (q1050932-r-member-p real xy-add)
        (q1050932-r-member-p real xy-mul)
        (q1050932-r-member-p real neg-x)
        (q1050932-r-member-p real inv-x)
        (equal
         (q1050932-r-add real xy-add z)
         (q1050932-r-add real x yz-add))
        (equal xy-add (q1050932-r-add real y x))
        (equal (q1050932-r-add real x zero) x)
        (equal (q1050932-r-add real x neg-x) zero)
        (equal
         (q1050932-r-multiply real xy-mul z)
         (q1050932-r-multiply real x yz-mul))
        (equal xy-mul (q1050932-r-multiply real y x))
        (equal (q1050932-r-multiply real x one) x)
        (equal (q1050932-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q1050932-r-multiply real x inv-x)
          one))
        (equal
         (q1050932-r-multiply
          real x (q1050932-r-add real y z))
         (q1050932-r-add
          real
          (q1050932-r-multiply real x y)
          (q1050932-r-multiply real x z))))))))

(defun-sk q1050932-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q1050932-r-member-p real x)
      (q1050932-r-member-p real y)
      (q1050932-r-member-p real z))
     (let ((zero (q1050932-r-zero real)))
       (and
        (not (q1050932-r-less real x x))
        (or
         (equal x y)
         (q1050932-r-less real x y)
         (q1050932-r-less real y x))
        (implies
         (and
          (q1050932-r-less real x y)
          (q1050932-r-less real y z))
         (q1050932-r-less real x z))
        (implies
         (q1050932-r-less real x y)
         (q1050932-r-less
          real
          (q1050932-r-add real x z)
          (q1050932-r-add real y z)))
        (implies
         (and
          (q1050932-r-less real zero x)
          (q1050932-r-less real zero y))
         (q1050932-r-less
          real zero
          (q1050932-r-multiply real x y))))))))

(defun-sk q1050932-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q1050932-r-member-p real x)
     (q1050932-r-set-member-p real set x))))

(defun-sk q1050932-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q1050932-r-member-p real x)
      (q1050932-r-set-member-p real set x))
     (q1050932-r-leq real x bound))))

(defun-sk q1050932-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q1050932-r-member-p real bound)
     (q1050932-r-upper-bound-p real set bound))))

(defun-sk q1050932-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q1050932-r-member-p real supremum)
     (q1050932-r-upper-bound-p real set supremum)
     (implies
      (and
       (q1050932-r-member-p real bound)
       (q1050932-r-upper-bound-p real set bound))
      (q1050932-r-leq real supremum bound)))))

(defun-sk q1050932-r-has-supremum-p (real set)
  (exists (supremum)
    (q1050932-r-supremum-p real set supremum)))

(defun-sk q1050932-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q1050932-r-set-nonempty-p real set)
      (q1050932-r-bounded-above-p real set))
     (q1050932-r-has-supremum-p real set))))

(defun q1050932-real-field-p (real)
  (let ((zero (q1050932-r-zero real))
        (one (q1050932-r-one real)))
    (and
     (q1050932-r-member-p real zero)
     (q1050932-r-member-p real one)
     (not (equal zero one))
     (q1050932-r-field-laws-p real)
     (q1050932-r-order-laws-p real)
     (q1050932-r-less real zero one)
     (q1050932-r-dedekind-complete-p real))))

;; The complex numbers as an isometric real-coordinate field.

(defstub q1050932-c-member-p (complex value) t)
(defstub q1050932-c-zero (complex) t)
(defstub q1050932-c-one (complex) t)
(defstub q1050932-c-add (complex left right) t)
(defstub q1050932-c-multiply (complex left right) t)
(defstub q1050932-c-negate (complex value) t)
(defstub q1050932-c-inverse (complex value) t)
(defstub q1050932-c-norm (real complex value) t)
(defstub q1050932-c-of-real (real complex value) t)
(defstub q1050932-c-re (real complex value) t)
(defstub q1050932-c-im (real complex value) t)
(defstub q1050932-c-I (complex) t)

(defun q1050932-c-subtract (complex left right)
  (q1050932-c-add
   complex left (q1050932-c-negate complex right)))

(defun-sk q1050932-c-field-laws-p (complex)
  (forall (x y z)
    (implies
     (and
      (q1050932-c-member-p complex x)
      (q1050932-c-member-p complex y)
      (q1050932-c-member-p complex z))
     (let* ((zero (q1050932-c-zero complex))
            (one (q1050932-c-one complex))
            (xy-add (q1050932-c-add complex x y))
            (yz-add (q1050932-c-add complex y z))
            (xy-mul (q1050932-c-multiply complex x y))
            (yz-mul (q1050932-c-multiply complex y z))
            (neg-x (q1050932-c-negate complex x))
            (inv-x (q1050932-c-inverse complex x)))
       (and
        (q1050932-c-member-p complex xy-add)
        (q1050932-c-member-p complex xy-mul)
        (q1050932-c-member-p complex neg-x)
        (q1050932-c-member-p complex inv-x)
        (equal
         (q1050932-c-add complex xy-add z)
         (q1050932-c-add complex x yz-add))
        (equal xy-add (q1050932-c-add complex y x))
        (equal (q1050932-c-add complex x zero) x)
        (equal (q1050932-c-add complex x neg-x) zero)
        (equal
         (q1050932-c-multiply complex xy-mul z)
         (q1050932-c-multiply complex x yz-mul))
        (equal xy-mul (q1050932-c-multiply complex y x))
        (equal (q1050932-c-multiply complex x one) x)
        (equal (q1050932-c-inverse complex zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q1050932-c-multiply complex x inv-x)
          one))
        (equal
         (q1050932-c-multiply
          complex x (q1050932-c-add complex y z))
         (q1050932-c-add
          complex
          (q1050932-c-multiply complex x y)
          (q1050932-c-multiply complex x z))))))))

(defun-sk q1050932-c-norm-laws-p (real complex)
  (forall (x y)
    (implies
     (and
      (q1050932-c-member-p complex x)
      (q1050932-c-member-p complex y))
     (let ((zero-c (q1050932-c-zero complex))
           (zero-r (q1050932-r-zero real))
           (norm-x (q1050932-c-norm real complex x))
           (norm-y (q1050932-c-norm real complex y)))
       (and
        (q1050932-r-member-p real norm-x)
        (q1050932-r-member-p real norm-y)
        (q1050932-r-leq real zero-r norm-x)
        (iff (equal norm-x zero-r)
             (equal x zero-c))
        (equal
         (q1050932-c-norm
          real complex (q1050932-c-negate complex x))
         norm-x)
        (q1050932-r-leq
         real
         (q1050932-c-norm
          real complex (q1050932-c-add complex x y))
         (q1050932-r-add real norm-x norm-y))
        (equal
         (q1050932-c-norm
          real complex (q1050932-c-multiply complex x y))
         (q1050932-r-multiply real norm-x norm-y)))))))

(defun-sk q1050932-c-coordinate-laws-p (real complex)
  (forall (a b z)
    (implies
     (and
      (q1050932-r-member-p real a)
      (q1050932-r-member-p real b)
      (q1050932-c-member-p complex z))
     (let* ((zero-r (q1050932-r-zero real))
            (one-r (q1050932-r-one real))
            (zero-c (q1050932-c-zero complex))
            (one-c (q1050932-c-one complex))
            (imaginary-unit (q1050932-c-I complex))
            (of-a (q1050932-c-of-real real complex a))
            (of-b (q1050932-c-of-real real complex b))
            (re-z (q1050932-c-re real complex z))
            (im-z (q1050932-c-im real complex z))
            (norm-z (q1050932-c-norm real complex z)))
       (and
        (q1050932-c-member-p complex imaginary-unit)
        (q1050932-c-member-p complex of-a)
        (q1050932-r-member-p real re-z)
        (q1050932-r-member-p real im-z)
        (equal
         (q1050932-c-of-real real complex zero-r)
         zero-c)
        (equal
         (q1050932-c-of-real real complex one-r)
         one-c)
        (equal
         (q1050932-c-of-real
          real complex (q1050932-r-add real a b))
         (q1050932-c-add complex of-a of-b))
        (equal
         (q1050932-c-of-real
          real complex (q1050932-r-multiply real a b))
         (q1050932-c-multiply complex of-a of-b))
        (equal
         (q1050932-c-of-real
          real complex (q1050932-r-negate real a))
         (q1050932-c-negate complex of-a))
        (equal
         (q1050932-c-re real complex of-a)
         a)
        (equal
         (q1050932-c-im real complex of-a)
         zero-r)
        (equal
         (q1050932-c-re real complex imaginary-unit)
         zero-r)
        (equal
         (q1050932-c-im real complex imaginary-unit)
         one-r)
        (equal
         (q1050932-c-multiply
          complex imaginary-unit imaginary-unit)
         (q1050932-c-negate complex one-c))
        (equal
         z
         (q1050932-c-add
          complex
          (q1050932-c-of-real real complex re-z)
          (q1050932-c-multiply
           complex
           (q1050932-c-of-real real complex im-z)
           imaginary-unit)))
        (equal
         (q1050932-r-multiply real norm-z norm-z)
         (q1050932-r-add
          real
          (q1050932-r-multiply real re-z re-z)
          (q1050932-r-multiply real im-z im-z))))))))

(defun q1050932-complex-field-p (real complex)
  (let ((zero (q1050932-c-zero complex))
        (one (q1050932-c-one complex)))
    (and
     (q1050932-real-field-p real)
     (q1050932-c-member-p complex zero)
     (q1050932-c-member-p complex one)
     (not (equal zero one))
     (q1050932-c-field-laws-p complex)
     (q1050932-c-norm-laws-p real complex)
     (q1050932-c-coordinate-laws-p real complex))))

;; An arbitrary normed vector space over the represented complex field.

(defstub q1050932-e-member-p (space value) t)
(defstub q1050932-e-zero (space) t)
(defstub q1050932-e-add (space left right) t)
(defstub q1050932-e-negate (space value) t)
(defstub q1050932-e-smul (complex space scalar vector) t)
(defstub q1050932-e-norm (real space value) t)

(defun q1050932-e-subtract (space left right)
  (q1050932-e-add
   space left (q1050932-e-negate space right)))

(defun-sk q1050932-normed-space-laws-p
    (real complex space)
  (forall (x y z a b)
    (and
     (implies
      (and
       (q1050932-e-member-p space x)
       (q1050932-e-member-p space y)
       (q1050932-e-member-p space z))
      (let* ((zero-e (q1050932-e-zero space))
             (zero-r (q1050932-r-zero real))
             (xy-add (q1050932-e-add space x y))
             (yz-add (q1050932-e-add space y z))
             (neg-x (q1050932-e-negate space x))
             (norm-x (q1050932-e-norm real space x))
             (norm-y (q1050932-e-norm real space y)))
        (and
         (q1050932-e-member-p space xy-add)
         (q1050932-e-member-p space neg-x)
         (q1050932-r-member-p real norm-x)
         (q1050932-r-member-p real norm-y)
         (equal
          (q1050932-e-add space xy-add z)
          (q1050932-e-add space x yz-add))
         (equal xy-add (q1050932-e-add space y x))
         (equal (q1050932-e-add space x zero-e) x)
         (equal (q1050932-e-add space x neg-x) zero-e)
         (q1050932-r-leq real zero-r norm-x)
         (iff (equal norm-x zero-r)
              (equal x zero-e))
         (equal
          (q1050932-e-norm real space neg-x)
          norm-x)
         (q1050932-r-leq
          real
          (q1050932-e-norm real space xy-add)
          (q1050932-r-add real norm-x norm-y)))))
     (implies
      (and
       (q1050932-c-member-p complex a)
       (q1050932-c-member-p complex b)
       (q1050932-e-member-p space x)
       (q1050932-e-member-p space y))
      (let ((zero-c (q1050932-c-zero complex))
            (one-c (q1050932-c-one complex))
            (zero-e (q1050932-e-zero space)))
        (and
         (q1050932-e-member-p
          space (q1050932-e-smul complex space a x))
         (equal
          (q1050932-e-smul complex space one-c x)
          x)
         (equal
          (q1050932-e-smul
           complex space
           (q1050932-c-multiply complex a b) x)
          (q1050932-e-smul
           complex space a
           (q1050932-e-smul complex space b x)))
         (equal
          (q1050932-e-smul
           complex space
           (q1050932-c-add complex a b) x)
          (q1050932-e-add
           space
           (q1050932-e-smul complex space a x)
           (q1050932-e-smul complex space b x)))
         (equal
          (q1050932-e-smul
           complex space a
           (q1050932-e-add space x y))
          (q1050932-e-add
           space
           (q1050932-e-smul complex space a x)
           (q1050932-e-smul complex space a y)))
         (equal
          (q1050932-e-smul complex space zero-c x)
          zero-e)
         (equal
          (q1050932-e-smul complex space a zero-e)
          zero-e)
         (equal
          (q1050932-e-norm
           real space
           (q1050932-e-smul complex space a x))
          (q1050932-r-multiply
           real
           (q1050932-c-norm real complex a)
           (q1050932-e-norm real space x)))))))))

(defun q1050932-normed-complex-space-p
    (real complex space)
  (and
   (q1050932-e-member-p
    space (q1050932-e-zero space))
   (q1050932-normed-space-laws-p
    real complex space)))

;; Completeness and second countability. For metric spaces, the existence of
;; a countable dense sequence is equivalent to second countability.

(defstub q1050932-sequence-value (sequence index) t)

(defun q1050932-e-distance (real space left right)
  (q1050932-e-norm
   real space
   (q1050932-e-subtract space left right)))

(defun-sk q1050932-sequence-typed-p (space sequence)
  (forall (n)
    (implies
     (natp n)
     (q1050932-e-member-p
      space (q1050932-sequence-value sequence n)))))

(defun-sk q1050932-cauchy-tail-p
    (real space sequence epsilon cutoff)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (natp cutoff)
      (<= cutoff m)
      (<= cutoff n))
     (q1050932-r-less
      real
      (q1050932-e-distance
       real space
       (q1050932-sequence-value sequence m)
       (q1050932-sequence-value sequence n))
      epsilon))))

(defun-sk q1050932-cauchy-cutoff-exists-p
    (real space sequence epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q1050932-cauchy-tail-p
      real space sequence epsilon cutoff))))

(defun-sk q1050932-cauchy-p (real space sequence)
  (forall (epsilon)
    (implies
     (q1050932-r-positive-p real epsilon)
     (q1050932-cauchy-cutoff-exists-p
      real space sequence epsilon))))

(defun-sk q1050932-convergence-tail-p
    (real space sequence limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (q1050932-r-less
      real
      (q1050932-e-distance
       real space
       (q1050932-sequence-value sequence n)
       limit)
      epsilon))))

(defun-sk q1050932-convergence-cutoff-exists-p
    (real space sequence limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q1050932-convergence-tail-p
      real space sequence limit epsilon cutoff))))

(defun-sk q1050932-converges-p
    (real space sequence limit)
  (forall (epsilon)
    (implies
     (q1050932-r-positive-p real epsilon)
     (q1050932-convergence-cutoff-exists-p
      real space sequence limit epsilon))))

(defun-sk q1050932-limit-exists-p
    (real space sequence)
  (exists (limit)
    (and
     (q1050932-e-member-p space limit)
     (q1050932-converges-p
      real space sequence limit))))

(defun-sk q1050932-complete-space-p (real space)
  (forall (sequence)
    (implies
     (and
      (q1050932-sequence-typed-p space sequence)
      (q1050932-cauchy-p real space sequence))
     (q1050932-limit-exists-p
      real space sequence))))

(defun-sk q1050932-dense-sequence-point-p
    (real space sequence point epsilon)
  (exists (n)
    (and
     (natp n)
     (q1050932-r-less
      real
      (q1050932-e-distance
       real space
       (q1050932-sequence-value sequence n)
       point)
      epsilon))))

(defun-sk q1050932-dense-sequence-p
    (real space sequence)
  (forall (point epsilon)
    (implies
     (and
      (q1050932-e-member-p space point)
      (q1050932-r-positive-p real epsilon))
     (q1050932-dense-sequence-point-p
      real space sequence point epsilon))))

(defun-sk q1050932-second-countable-p (real space)
  (exists (sequence)
    (and
     (q1050932-sequence-typed-p space sequence)
     (q1050932-dense-sequence-p
      real space sequence))))

;; Arbitrary subsets of C x C and functions C x C -> E.

(defstub q1050932-set-member-p (set z0 z1) t)
(defstub q1050932-function-value (function z0 z1) t)

(defun-sk q1050932-valid-set-p (complex set)
  (forall (z0 z1)
    (implies
     (q1050932-set-member-p set z0 z1)
     (and
      (q1050932-c-member-p complex z0)
      (q1050932-c-member-p complex z1)))))

(defun-sk q1050932-function-p
    (complex space function)
  (forall (z0 z1)
    (implies
     (and
      (q1050932-c-member-p complex z0)
      (q1050932-c-member-p complex z1))
     (q1050932-e-member-p
      space
      (q1050932-function-value function z0 z1)))))

(defun q1050932-pair-distance
    (real complex z0 z1 w0 w1)
  (q1050932-r-max
   real
   (q1050932-c-norm
    real complex
    (q1050932-c-subtract complex z0 w0))
   (q1050932-c-norm
    real complex
    (q1050932-c-subtract complex z1 w1))))

;; Openness in the product norm topology on C x C.

(defun-sk q1050932-pair-ball-contained-p
    (real complex set c0 c1 radius)
  (forall (z0 z1)
    (implies
     (and
      (q1050932-c-member-p complex z0)
      (q1050932-c-member-p complex z1)
      (q1050932-r-less
       real
       (q1050932-pair-distance
        real complex z0 z1 c0 c1)
       radius))
     (q1050932-set-member-p set z0 z1))))

(defun-sk q1050932-open-radius-exists-p
    (real complex set c0 c1)
  (exists (radius)
    (and
     (q1050932-r-positive-p real radius)
     (q1050932-pair-ball-contained-p
      real complex set c0 c1 radius))))

(defun-sk q1050932-open-set-p
    (real complex set)
  (forall (c0 c1)
    (implies
     (q1050932-set-member-p set c0 c1)
     (q1050932-open-radius-exists-p
      real complex set c0 c1))))

;; Continuous complex-linear maps C -> E and C x C -> E.

(defstub q1050932-unary-linear-value (linear-map z) t)
(defstub q1050932-pair-linear-value (linear-map z0 z1) t)

(defun-sk q1050932-unary-linear-laws-p
    (complex space linear-map)
  (forall (a x y)
    (implies
     (and
      (q1050932-c-member-p complex a)
      (q1050932-c-member-p complex x)
      (q1050932-c-member-p complex y))
     (and
      (q1050932-e-member-p
       space
       (q1050932-unary-linear-value linear-map x))
      (equal
       (q1050932-unary-linear-value
        linear-map
        (q1050932-c-add complex x y))
       (q1050932-e-add
        space
        (q1050932-unary-linear-value linear-map x)
        (q1050932-unary-linear-value linear-map y)))
      (equal
       (q1050932-unary-linear-value
        linear-map
        (q1050932-c-multiply complex a x))
       (q1050932-e-smul
        complex space a
        (q1050932-unary-linear-value linear-map x)))))))

(defun-sk q1050932-unary-linear-bound-p
    (real complex space linear-map bound)
  (forall (x)
    (implies
     (q1050932-c-member-p complex x)
     (q1050932-r-leq
      real
      (q1050932-e-norm
       real space
       (q1050932-unary-linear-value linear-map x))
      (q1050932-r-multiply
       real bound
       (q1050932-c-norm real complex x))))))

(defun-sk q1050932-unary-linear-bound-exists-p
    (real complex space linear-map)
  (exists (bound)
    (and
     (q1050932-r-member-p real bound)
     (q1050932-r-leq
      real (q1050932-r-zero real) bound)
     (q1050932-unary-linear-bound-p
      real complex space linear-map bound))))

(defun q1050932-continuous-unary-linear-map-p
    (real complex space linear-map)
  (and
   (q1050932-unary-linear-laws-p
    complex space linear-map)
   (q1050932-unary-linear-bound-exists-p
    real complex space linear-map)))

(defun-sk q1050932-pair-linear-laws-p
    (complex space linear-map)
  (forall (a x0 x1 y0 y1)
    (implies
     (and
      (q1050932-c-member-p complex a)
      (q1050932-c-member-p complex x0)
      (q1050932-c-member-p complex x1)
      (q1050932-c-member-p complex y0)
      (q1050932-c-member-p complex y1))
     (and
      (q1050932-e-member-p
       space
       (q1050932-pair-linear-value
        linear-map x0 x1))
      (equal
       (q1050932-pair-linear-value
        linear-map
        (q1050932-c-add complex x0 y0)
        (q1050932-c-add complex x1 y1))
       (q1050932-e-add
        space
        (q1050932-pair-linear-value
         linear-map x0 x1)
        (q1050932-pair-linear-value
         linear-map y0 y1)))
      (equal
       (q1050932-pair-linear-value
        linear-map
        (q1050932-c-multiply complex a x0)
        (q1050932-c-multiply complex a x1))
       (q1050932-e-smul
        complex space a
        (q1050932-pair-linear-value
         linear-map x0 x1)))))))

(defun-sk q1050932-pair-linear-bound-p
    (real complex space linear-map bound)
  (forall (x0 x1)
    (implies
     (and
      (q1050932-c-member-p complex x0)
      (q1050932-c-member-p complex x1))
     (q1050932-r-leq
      real
      (q1050932-e-norm
       real space
       (q1050932-pair-linear-value
        linear-map x0 x1))
      (q1050932-r-multiply
       real bound
       (q1050932-r-max
        real
        (q1050932-c-norm real complex x0)
        (q1050932-c-norm real complex x1)))))))

(defun-sk q1050932-pair-linear-bound-exists-p
    (real complex space linear-map)
  (exists (bound)
    (and
     (q1050932-r-member-p real bound)
     (q1050932-r-leq
      real (q1050932-r-zero real) bound)
     (q1050932-pair-linear-bound-p
      real complex space linear-map bound))))

(defun q1050932-continuous-pair-linear-map-p
    (real complex space linear-map)
  (and
   (q1050932-pair-linear-laws-p
    complex space linear-map)
   (q1050932-pair-linear-bound-exists-p
    real complex space linear-map)))

;; Complex Fréchet differentiability. Analyticity at a point is represented by
;; differentiability throughout some neighborhood of that point. For maps
;; between complex normed spaces with complete codomain, this is equivalent in
;; both directions to local power-series analyticity.

(defun-sk q1050932-slice0-derivative-nearby-p
    (real complex space function fixed center
     linear-map epsilon radius)
  (forall (z)
    (implies
     (and
      (q1050932-c-member-p complex z)
      (q1050932-r-less
       real
       (q1050932-c-norm
        real complex
        (q1050932-c-subtract complex z center))
       radius))
     (q1050932-r-leq
      real
      (q1050932-e-norm
       real space
       (q1050932-e-subtract
        space
        (q1050932-e-subtract
         space
         (q1050932-function-value function z fixed)
         (q1050932-function-value function center fixed))
        (q1050932-unary-linear-value
         linear-map
         (q1050932-c-subtract complex z center))))
      (q1050932-r-multiply
       real epsilon
       (q1050932-c-norm
        real complex
        (q1050932-c-subtract complex z center)))))))

(defun-sk q1050932-slice0-derivative-radius-exists-p
    (real complex space function fixed center linear-map epsilon)
  (exists (radius)
    (and
     (q1050932-r-positive-p real radius)
     (q1050932-slice0-derivative-nearby-p
      real complex space function fixed center
      linear-map epsilon radius))))

(defun-sk q1050932-slice0-has-derivative-at-p
    (real complex space function fixed center linear-map)
  (forall (epsilon)
    (implies
     (q1050932-r-positive-p real epsilon)
     (q1050932-slice0-derivative-radius-exists-p
      real complex space function fixed center
      linear-map epsilon))))

(defun-sk q1050932-slice0-differentiable-at-p
    (real complex space function fixed center)
  (exists (linear-map)
    (and
     (q1050932-continuous-unary-linear-map-p
      real complex space linear-map)
     (q1050932-slice0-has-derivative-at-p
      real complex space function fixed center linear-map))))

(defun-sk q1050932-slice0-differentiable-near-p
    (real complex space function fixed center radius)
  (forall (z)
    (implies
     (and
      (q1050932-c-member-p complex z)
      (q1050932-r-less
       real
       (q1050932-c-norm
        real complex
        (q1050932-c-subtract complex z center))
       radius))
     (q1050932-slice0-differentiable-at-p
      real complex space function fixed z))))

(defun-sk q1050932-slice0-analytic-at-p
    (real complex space function fixed center)
  (exists (radius)
    (and
     (q1050932-r-positive-p real radius)
     (q1050932-slice0-differentiable-near-p
      real complex space function fixed center radius))))

(defun-sk q1050932-slice1-derivative-nearby-p
    (real complex space function fixed center
     linear-map epsilon radius)
  (forall (z)
    (implies
     (and
      (q1050932-c-member-p complex z)
      (q1050932-r-less
       real
       (q1050932-c-norm
        real complex
        (q1050932-c-subtract complex z center))
       radius))
     (q1050932-r-leq
      real
      (q1050932-e-norm
       real space
       (q1050932-e-subtract
        space
        (q1050932-e-subtract
         space
         (q1050932-function-value function fixed z)
         (q1050932-function-value function fixed center))
        (q1050932-unary-linear-value
         linear-map
         (q1050932-c-subtract complex z center))))
      (q1050932-r-multiply
       real epsilon
       (q1050932-c-norm
        real complex
        (q1050932-c-subtract complex z center)))))))

(defun-sk q1050932-slice1-derivative-radius-exists-p
    (real complex space function fixed center linear-map epsilon)
  (exists (radius)
    (and
     (q1050932-r-positive-p real radius)
     (q1050932-slice1-derivative-nearby-p
      real complex space function fixed center
      linear-map epsilon radius))))

(defun-sk q1050932-slice1-has-derivative-at-p
    (real complex space function fixed center linear-map)
  (forall (epsilon)
    (implies
     (q1050932-r-positive-p real epsilon)
     (q1050932-slice1-derivative-radius-exists-p
      real complex space function fixed center
      linear-map epsilon))))

(defun-sk q1050932-slice1-differentiable-at-p
    (real complex space function fixed center)
  (exists (linear-map)
    (and
     (q1050932-continuous-unary-linear-map-p
      real complex space linear-map)
     (q1050932-slice1-has-derivative-at-p
      real complex space function fixed center linear-map))))

(defun-sk q1050932-slice1-differentiable-near-p
    (real complex space function fixed center radius)
  (forall (z)
    (implies
     (and
      (q1050932-c-member-p complex z)
      (q1050932-r-less
       real
       (q1050932-c-norm
        real complex
        (q1050932-c-subtract complex z center))
       radius))
     (q1050932-slice1-differentiable-at-p
      real complex space function fixed z))))

(defun-sk q1050932-slice1-analytic-at-p
    (real complex space function fixed center)
  (exists (radius)
    (and
     (q1050932-r-positive-p real radius)
     (q1050932-slice1-differentiable-near-p
      real complex space function fixed center radius))))

(defun-sk q1050932-joint-derivative-nearby-p
    (real complex space function c0 c1
     linear-map epsilon radius)
  (forall (z0 z1)
    (implies
     (and
      (q1050932-c-member-p complex z0)
      (q1050932-c-member-p complex z1)
      (q1050932-r-less
       real
       (q1050932-pair-distance
        real complex z0 z1 c0 c1)
       radius))
     (q1050932-r-leq
      real
      (q1050932-e-norm
       real space
       (q1050932-e-subtract
        space
        (q1050932-e-subtract
         space
         (q1050932-function-value function z0 z1)
         (q1050932-function-value function c0 c1))
        (q1050932-pair-linear-value
         linear-map
         (q1050932-c-subtract complex z0 c0)
         (q1050932-c-subtract complex z1 c1))))
      (q1050932-r-multiply
       real epsilon
       (q1050932-pair-distance
        real complex z0 z1 c0 c1))))))

(defun-sk q1050932-joint-derivative-radius-exists-p
    (real complex space function c0 c1 linear-map epsilon)
  (exists (radius)
    (and
     (q1050932-r-positive-p real radius)
     (q1050932-joint-derivative-nearby-p
      real complex space function c0 c1
      linear-map epsilon radius))))

(defun-sk q1050932-joint-has-derivative-at-p
    (real complex space function c0 c1 linear-map)
  (forall (epsilon)
    (implies
     (q1050932-r-positive-p real epsilon)
     (q1050932-joint-derivative-radius-exists-p
      real complex space function c0 c1
      linear-map epsilon))))

(defun-sk q1050932-joint-differentiable-at-p
    (real complex space function c0 c1)
  (exists (linear-map)
    (and
     (q1050932-continuous-pair-linear-map-p
      real complex space linear-map)
     (q1050932-joint-has-derivative-at-p
      real complex space function c0 c1 linear-map))))

(defun-sk q1050932-joint-differentiable-near-p
    (real complex space function c0 c1 radius)
  (forall (z0 z1)
    (implies
     (and
      (q1050932-c-member-p complex z0)
      (q1050932-c-member-p complex z1)
      (q1050932-r-less
       real
       (q1050932-pair-distance
        real complex z0 z1 c0 c1)
       radius))
     (q1050932-joint-differentiable-at-p
      real complex space function z0 z1))))

(defun-sk q1050932-joint-analytic-at-p
    (real complex space function c0 c1)
  (exists (radius)
    (and
     (q1050932-r-positive-p real radius)
     (q1050932-joint-differentiable-near-p
      real complex space function c0 c1 radius))))

(defun-sk q1050932-separately-analytic-on-p
    (real complex space function set)
  (forall (c0 c1)
    (implies
     (q1050932-set-member-p set c0 c1)
     (and
      (q1050932-slice0-analytic-at-p
       real complex space function c1 c0)
      (q1050932-slice1-analytic-at-p
       real complex space function c0 c1)))))

(defun-sk q1050932-analytic-on-neighborhood-p
    (real complex space function set)
  (forall (c0 c1)
    (implies
     (q1050932-set-member-p set c0 c1)
     (q1050932-joint-analytic-at-p
      real complex space function c0 c1))))

(defun-sk
    thousand-theorems-q1050932-hartogs-s-theorem-statement
    ()
  (forall (real complex space set function)
    (implies
     (and
      (q1050932-complex-field-p real complex)
      (q1050932-normed-complex-space-p
       real complex space)
      (q1050932-complete-space-p real space)
      (q1050932-second-countable-p real space)
      (q1050932-valid-set-p complex set)
      (q1050932-function-p complex space function)
      (q1050932-open-set-p real complex set)
      (q1050932-separately-analytic-on-p
       real complex space function set))
     (q1050932-analytic-on-neighborhood-p
      real complex space function set))))

(value-triple :itpeval-statement-checked)
:q
