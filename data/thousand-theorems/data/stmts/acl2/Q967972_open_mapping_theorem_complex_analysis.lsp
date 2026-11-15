;; Statement-only formalization of thousand-theorems corpus artifact Q967972,
;; "Open mapping theorem (complex analysis)": a complex-analytic function from
;; a normed complex vector space to the complex numbers, on a preconnected set,
;; is constant there or maps every open subset of that set to an open set.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Conservative interfaces present arbitrary carriers, operations, subsets,
;; functions, and continuous linear maps.  A Dedekind-complete ordered field
;; presents the real numbers, and explicit real/imaginary coordinates present
;; the usual complex field with its Euclidean norm.  All algebraic, normed
;; vector-space, topological, differentiability, and typing laws used by the
;; source statement are explicit below.

;; The real numbers.

(defstub q967972-r-member-p (real value) t)
(defstub q967972-r-zero (real) t)
(defstub q967972-r-one (real) t)
(defstub q967972-r-add (real left right) t)
(defstub q967972-r-multiply (real left right) t)
(defstub q967972-r-negate (real value) t)
(defstub q967972-r-inverse (real value) t)
(defstub q967972-r-less (real left right) t)
(defstub q967972-r-set-member-p (real set value) t)

(defun q967972-r-leq (real left right)
  (not (q967972-r-less real right left)))

(defun q967972-r-positive-p (real value)
  (and
   (q967972-r-member-p real value)
   (q967972-r-less
    real (q967972-r-zero real) value)))

(defun-sk q967972-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q967972-r-member-p real x)
      (q967972-r-member-p real y)
      (q967972-r-member-p real z))
     (let* ((zero (q967972-r-zero real))
            (one (q967972-r-one real))
            (xy-add (q967972-r-add real x y))
            (yz-add (q967972-r-add real y z))
            (xy-mul (q967972-r-multiply real x y))
            (yz-mul (q967972-r-multiply real y z))
            (neg-x (q967972-r-negate real x))
            (inv-x (q967972-r-inverse real x)))
       (and
        (q967972-r-member-p real xy-add)
        (q967972-r-member-p real xy-mul)
        (q967972-r-member-p real neg-x)
        (q967972-r-member-p real inv-x)
        (equal
         (q967972-r-add real xy-add z)
         (q967972-r-add real x yz-add))
        (equal xy-add (q967972-r-add real y x))
        (equal (q967972-r-add real x zero) x)
        (equal (q967972-r-add real x neg-x) zero)
        (equal
         (q967972-r-multiply real xy-mul z)
         (q967972-r-multiply real x yz-mul))
        (equal xy-mul (q967972-r-multiply real y x))
        (equal (q967972-r-multiply real x one) x)
        (equal (q967972-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q967972-r-multiply real x inv-x)
          one))
        (equal
         (q967972-r-multiply
          real x (q967972-r-add real y z))
         (q967972-r-add
          real
          (q967972-r-multiply real x y)
          (q967972-r-multiply real x z))))))))

(defun-sk q967972-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q967972-r-member-p real x)
      (q967972-r-member-p real y)
      (q967972-r-member-p real z))
     (let ((zero (q967972-r-zero real)))
       (and
        (not (q967972-r-less real x x))
        (or
         (equal x y)
         (q967972-r-less real x y)
         (q967972-r-less real y x))
        (implies
         (and
          (q967972-r-less real x y)
          (q967972-r-less real y z))
         (q967972-r-less real x z))
        (implies
         (q967972-r-less real x y)
         (q967972-r-less
          real
          (q967972-r-add real x z)
          (q967972-r-add real y z)))
        (implies
         (and
          (q967972-r-less real zero x)
          (q967972-r-less real zero y))
         (q967972-r-less
          real zero
          (q967972-r-multiply real x y))))))))

(defun-sk q967972-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q967972-r-member-p real x)
     (q967972-r-set-member-p real set x))))

(defun-sk q967972-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q967972-r-member-p real x)
      (q967972-r-set-member-p real set x))
     (q967972-r-leq real x bound))))

(defun-sk q967972-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q967972-r-member-p real bound)
     (q967972-r-upper-bound-p real set bound))))

(defun-sk q967972-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q967972-r-member-p real supremum)
     (q967972-r-upper-bound-p real set supremum)
     (implies
      (and
       (q967972-r-member-p real bound)
       (q967972-r-upper-bound-p real set bound))
      (q967972-r-leq real supremum bound)))))

(defun-sk q967972-r-has-supremum-p (real set)
  (exists (supremum)
    (q967972-r-supremum-p real set supremum)))

(defun-sk q967972-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q967972-r-set-nonempty-p real set)
      (q967972-r-bounded-above-p real set))
     (q967972-r-has-supremum-p real set))))

(defun q967972-real-field-p (real)
  (let ((zero (q967972-r-zero real))
        (one (q967972-r-one real)))
    (and
     (q967972-r-member-p real zero)
     (q967972-r-member-p real one)
     (not (equal zero one))
     (q967972-r-field-laws-p real)
     (q967972-r-order-laws-p real)
     (q967972-r-less real zero one)
     (q967972-r-dedekind-complete-p real))))

;; The complex numbers as an isometric real-coordinate field.

(defstub q967972-c-member-p (complex value) t)
(defstub q967972-c-zero (complex) t)
(defstub q967972-c-one (complex) t)
(defstub q967972-c-add (complex left right) t)
(defstub q967972-c-multiply (complex left right) t)
(defstub q967972-c-negate (complex value) t)
(defstub q967972-c-inverse (complex value) t)
(defstub q967972-c-norm (real complex value) t)
(defstub q967972-c-of-real (real complex value) t)
(defstub q967972-c-re (real complex value) t)
(defstub q967972-c-im (real complex value) t)
(defstub q967972-c-I (complex) t)

(defun q967972-c-subtract (complex left right)
  (q967972-c-add
   complex left (q967972-c-negate complex right)))

(defun-sk q967972-c-field-laws-p (complex)
  (forall (x y z)
    (implies
     (and
      (q967972-c-member-p complex x)
      (q967972-c-member-p complex y)
      (q967972-c-member-p complex z))
     (let* ((zero (q967972-c-zero complex))
            (one (q967972-c-one complex))
            (xy-add (q967972-c-add complex x y))
            (yz-add (q967972-c-add complex y z))
            (xy-mul (q967972-c-multiply complex x y))
            (yz-mul (q967972-c-multiply complex y z))
            (neg-x (q967972-c-negate complex x))
            (inv-x (q967972-c-inverse complex x)))
       (and
        (q967972-c-member-p complex xy-add)
        (q967972-c-member-p complex xy-mul)
        (q967972-c-member-p complex neg-x)
        (q967972-c-member-p complex inv-x)
        (equal
         (q967972-c-add complex xy-add z)
         (q967972-c-add complex x yz-add))
        (equal xy-add (q967972-c-add complex y x))
        (equal (q967972-c-add complex x zero) x)
        (equal (q967972-c-add complex x neg-x) zero)
        (equal
         (q967972-c-multiply complex xy-mul z)
         (q967972-c-multiply complex x yz-mul))
        (equal xy-mul (q967972-c-multiply complex y x))
        (equal (q967972-c-multiply complex x one) x)
        (equal (q967972-c-inverse complex zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q967972-c-multiply complex x inv-x)
          one))
        (equal
         (q967972-c-multiply
          complex x (q967972-c-add complex y z))
         (q967972-c-add
          complex
          (q967972-c-multiply complex x y)
          (q967972-c-multiply complex x z))))))))

(defun-sk q967972-c-norm-laws-p (real complex)
  (forall (x y)
    (implies
     (and
      (q967972-c-member-p complex x)
      (q967972-c-member-p complex y))
     (let ((zero-c (q967972-c-zero complex))
           (zero-r (q967972-r-zero real))
           (norm-x (q967972-c-norm real complex x))
           (norm-y (q967972-c-norm real complex y)))
       (and
        (q967972-r-member-p real norm-x)
        (q967972-r-member-p real norm-y)
        (q967972-r-leq real zero-r norm-x)
        (iff (equal norm-x zero-r)
             (equal x zero-c))
        (equal
         (q967972-c-norm
          real complex (q967972-c-negate complex x))
         norm-x)
        (q967972-r-leq
         real
         (q967972-c-norm
          real complex (q967972-c-add complex x y))
         (q967972-r-add real norm-x norm-y))
        (equal
         (q967972-c-norm
          real complex (q967972-c-multiply complex x y))
         (q967972-r-multiply real norm-x norm-y)))))))

(defun-sk q967972-c-coordinate-laws-p (real complex)
  (forall (a b z)
    (implies
     (and
      (q967972-r-member-p real a)
      (q967972-r-member-p real b)
      (q967972-c-member-p complex z))
     (let* ((zero-r (q967972-r-zero real))
            (one-r (q967972-r-one real))
            (zero-c (q967972-c-zero complex))
            (one-c (q967972-c-one complex))
            (imaginary-unit (q967972-c-I complex))
            (of-a (q967972-c-of-real real complex a))
            (of-b (q967972-c-of-real real complex b))
            (re-z (q967972-c-re real complex z))
            (im-z (q967972-c-im real complex z))
            (norm-z (q967972-c-norm real complex z)))
       (and
        (q967972-c-member-p complex imaginary-unit)
        (q967972-c-member-p complex of-a)
        (q967972-r-member-p real re-z)
        (q967972-r-member-p real im-z)
        (equal
         (q967972-c-of-real real complex zero-r)
         zero-c)
        (equal
         (q967972-c-of-real real complex one-r)
         one-c)
        (equal
         (q967972-c-of-real
          real complex (q967972-r-add real a b))
         (q967972-c-add complex of-a of-b))
        (equal
         (q967972-c-of-real
          real complex (q967972-r-multiply real a b))
         (q967972-c-multiply complex of-a of-b))
        (equal
         (q967972-c-of-real
          real complex (q967972-r-negate real a))
         (q967972-c-negate complex of-a))
        (equal
         (q967972-c-re real complex of-a)
         a)
        (equal
         (q967972-c-im real complex of-a)
         zero-r)
        (equal
         (q967972-c-re real complex imaginary-unit)
         zero-r)
        (equal
         (q967972-c-im real complex imaginary-unit)
         one-r)
        (equal
         (q967972-c-multiply
          complex imaginary-unit imaginary-unit)
         (q967972-c-negate complex one-c))
        (equal
         z
         (q967972-c-add
          complex
          (q967972-c-of-real real complex re-z)
          (q967972-c-multiply
           complex
           (q967972-c-of-real real complex im-z)
           imaginary-unit)))
        (equal
         (q967972-r-multiply real norm-z norm-z)
         (q967972-r-add
          real
          (q967972-r-multiply real re-z re-z)
          (q967972-r-multiply real im-z im-z))))))))

(defun q967972-complex-field-p (real complex)
  (let ((zero (q967972-c-zero complex))
        (one (q967972-c-one complex)))
    (and
     (q967972-real-field-p real)
     (q967972-c-member-p complex zero)
     (q967972-c-member-p complex one)
     (not (equal zero one))
     (q967972-c-field-laws-p complex)
     (q967972-c-norm-laws-p real complex)
     (q967972-c-coordinate-laws-p real complex))))

;; An arbitrary normed vector space over the represented complex field.

(defstub q967972-e-member-p (space value) t)
(defstub q967972-e-zero (space) t)
(defstub q967972-e-add (space left right) t)
(defstub q967972-e-negate (space value) t)
(defstub q967972-e-smul (complex space scalar vector) t)
(defstub q967972-e-norm (real space value) t)

(defun q967972-e-subtract (space left right)
  (q967972-e-add
   space left (q967972-e-negate space right)))

(defun-sk q967972-normed-space-laws-p
    (real complex space)
  (forall (x y z a b)
    (and
     (implies
      (and
       (q967972-e-member-p space x)
       (q967972-e-member-p space y)
       (q967972-e-member-p space z))
      (let* ((zero-e (q967972-e-zero space))
             (zero-r (q967972-r-zero real))
             (xy-add (q967972-e-add space x y))
             (yz-add (q967972-e-add space y z))
             (neg-x (q967972-e-negate space x))
             (norm-x (q967972-e-norm real space x))
             (norm-y (q967972-e-norm real space y)))
        (and
         (q967972-e-member-p space xy-add)
         (q967972-e-member-p space neg-x)
         (q967972-r-member-p real norm-x)
         (q967972-r-member-p real norm-y)
         (equal
          (q967972-e-add space xy-add z)
          (q967972-e-add space x yz-add))
         (equal xy-add (q967972-e-add space y x))
         (equal (q967972-e-add space x zero-e) x)
         (equal (q967972-e-add space x neg-x) zero-e)
         (q967972-r-leq real zero-r norm-x)
         (iff (equal norm-x zero-r)
              (equal x zero-e))
         (equal
          (q967972-e-norm real space neg-x)
          norm-x)
         (q967972-r-leq
          real
          (q967972-e-norm real space xy-add)
          (q967972-r-add real norm-x norm-y)))))
     (implies
      (and
       (q967972-c-member-p complex a)
       (q967972-c-member-p complex b)
       (q967972-e-member-p space x)
       (q967972-e-member-p space y))
      (let ((zero-c (q967972-c-zero complex))
            (one-c (q967972-c-one complex))
            (zero-e (q967972-e-zero space)))
        (and
         (q967972-e-member-p
          space (q967972-e-smul complex space a x))
         (equal
          (q967972-e-smul complex space one-c x)
          x)
         (equal
          (q967972-e-smul
           complex space
           (q967972-c-multiply complex a b) x)
          (q967972-e-smul
           complex space a
           (q967972-e-smul complex space b x)))
         (equal
          (q967972-e-smul
           complex space
           (q967972-c-add complex a b) x)
          (q967972-e-add
           space
           (q967972-e-smul complex space a x)
           (q967972-e-smul complex space b x)))
         (equal
          (q967972-e-smul
           complex space a
           (q967972-e-add space x y))
          (q967972-e-add
           space
           (q967972-e-smul complex space a x)
           (q967972-e-smul complex space a y)))
         (equal
          (q967972-e-smul complex space zero-c x)
          zero-e)
         (equal
          (q967972-e-smul complex space a zero-e)
          zero-e)
         (equal
          (q967972-e-norm
           real space
           (q967972-e-smul complex space a x))
          (q967972-r-multiply
           real
           (q967972-c-norm real complex a)
           (q967972-e-norm real space x)))))))))

(defun q967972-normed-complex-space-p
    (real complex space)
  (and
   (q967972-e-member-p
    space (q967972-e-zero space))
   (q967972-normed-space-laws-p
    real complex space)))

;; Arbitrary subsets, functions E -> C, and continuous C-linear maps E -> C.

(defstub q967972-set-member-p (set value) t)
(defstub q967972-function-value (function argument) t)
(defstub q967972-linear-value (linear-map argument) t)

(defun-sk q967972-valid-e-set-p (space set)
  (forall (x)
    (implies
     (q967972-set-member-p set x)
     (q967972-e-member-p space x))))

(defun-sk q967972-function-p
    (space complex function)
  (forall (x)
    (implies
     (q967972-e-member-p space x)
     (q967972-c-member-p
      complex
      (q967972-function-value function x)))))

(defun-sk q967972-linear-laws-p
    (complex space linear-map)
  (forall (a x y)
    (implies
     (and
      (q967972-c-member-p complex a)
      (q967972-e-member-p space x)
      (q967972-e-member-p space y))
     (and
      (q967972-c-member-p
       complex (q967972-linear-value linear-map x))
      (equal
       (q967972-linear-value
        linear-map (q967972-e-add space x y))
       (q967972-c-add
        complex
        (q967972-linear-value linear-map x)
        (q967972-linear-value linear-map y)))
      (equal
       (q967972-linear-value
        linear-map
        (q967972-e-smul complex space a x))
       (q967972-c-multiply
        complex a
        (q967972-linear-value linear-map x)))))))

(defun-sk q967972-linear-bound-p
    (real complex space linear-map bound)
  (forall (x)
    (implies
     (q967972-e-member-p space x)
     (q967972-r-leq
      real
      (q967972-c-norm
       real complex
       (q967972-linear-value linear-map x))
      (q967972-r-multiply
       real bound
       (q967972-e-norm real space x))))))

(defun-sk q967972-linear-bound-exists-p
    (real complex space linear-map)
  (exists (bound)
    (and
     (q967972-r-member-p real bound)
     (q967972-r-leq
      real (q967972-r-zero real) bound)
     (q967972-linear-bound-p
      real complex space linear-map bound))))

(defun q967972-continuous-linear-map-p
    (real complex space linear-map)
  (and
   (q967972-linear-laws-p
    complex space linear-map)
   (q967972-linear-bound-exists-p
    real complex space linear-map)))

;; Over a complex normed domain with complete codomain C, analyticity at a
;; point is equivalent to complex Frechet differentiability throughout some
;; neighborhood of that point.  The next predicates use this bidirectionally
;; equivalent characterization of AnalyticAt and AnalyticOnNhd.

(defun-sk q967972-derivative-nearby-p
    (real complex space function center linear-map epsilon radius)
  (forall (y)
    (implies
     (and
      (q967972-e-member-p space y)
      (q967972-r-less
       real
       (q967972-e-norm
        real space
        (q967972-e-subtract space y center))
       radius))
     (q967972-r-leq
      real
      (q967972-c-norm
       real complex
       (q967972-c-subtract
        complex
        (q967972-c-subtract
         complex
         (q967972-function-value function y)
         (q967972-function-value function center))
        (q967972-linear-value
         linear-map
         (q967972-e-subtract space y center))))
      (q967972-r-multiply
       real epsilon
       (q967972-e-norm
        real space
        (q967972-e-subtract space y center)))))))

(defun-sk q967972-derivative-radius-exists-p
    (real complex space function center linear-map epsilon)
  (exists (radius)
    (and
     (q967972-r-positive-p real radius)
     (q967972-derivative-nearby-p
      real complex space function center
      linear-map epsilon radius))))

(defun-sk q967972-has-derivative-at-p
    (real complex space function center linear-map)
  (forall (epsilon)
    (implies
     (q967972-r-positive-p real epsilon)
     (q967972-derivative-radius-exists-p
      real complex space function center
      linear-map epsilon))))

(defun-sk q967972-differentiable-at-p
    (real complex space function center)
  (exists (linear-map)
    (and
     (q967972-continuous-linear-map-p
      real complex space linear-map)
     (q967972-has-derivative-at-p
      real complex space function center linear-map))))

(defun-sk q967972-differentiable-on-ball-p
    (real complex space function center radius)
  (forall (point)
    (implies
     (and
      (q967972-e-member-p space point)
      (q967972-r-less
       real
       (q967972-e-norm
        real space
        (q967972-e-subtract space point center))
       radius))
     (q967972-differentiable-at-p
      real complex space function point))))

(defun-sk q967972-analytic-radius-exists-p
    (real complex space function center)
  (exists (radius)
    (and
     (q967972-r-positive-p real radius)
     (q967972-differentiable-on-ball-p
      real complex space function center radius))))

(defun-sk q967972-analytic-on-neighborhood-p
    (real complex space function set)
  (forall (center)
    (implies
     (q967972-set-member-p set center)
     (q967972-analytic-radius-exists-p
      real complex space function center))))

;; Norm topologies and preconnectedness of U.

(defun-sk q967972-e-ball-contained-p
    (real space set center radius)
  (forall (point)
    (implies
     (and
      (q967972-e-member-p space point)
      (q967972-r-less
       real
       (q967972-e-norm
        real space
        (q967972-e-subtract space point center))
       radius))
     (q967972-set-member-p set point))))

(defun-sk q967972-e-open-radius-exists-p
    (real space set center)
  (exists (radius)
    (and
     (q967972-r-positive-p real radius)
     (q967972-e-ball-contained-p
      real space set center radius))))

(defun-sk q967972-e-open-p (real space set)
  (forall (center)
    (implies
     (q967972-set-member-p set center)
     (q967972-e-open-radius-exists-p
      real space set center))))

(defun-sk q967972-cover-p (set left right)
  (forall (x)
    (implies
     (q967972-set-member-p set x)
     (or
      (q967972-set-member-p left x)
      (q967972-set-member-p right x)))))

(defun-sk q967972-intersects-p (left right)
  (exists (x)
    (and
     (q967972-set-member-p left x)
     (q967972-set-member-p right x))))

(defun-sk q967972-triple-intersects-p
    (set left right)
  (exists (x)
    (and
     (q967972-set-member-p set x)
     (q967972-set-member-p left x)
     (q967972-set-member-p right x))))

(defun-sk q967972-preconnected-p
    (real space set)
  (forall (left right)
    (implies
     (and
      (q967972-valid-e-set-p space left)
      (q967972-valid-e-set-p space right)
      (q967972-e-open-p real space left)
      (q967972-e-open-p real space right)
      (q967972-cover-p set left right)
      (q967972-intersects-p set left)
      (q967972-intersects-p set right))
     (q967972-triple-intersects-p
      set left right))))

;; The two alternatives in the source conclusion.

(defun-sk q967972-constant-on-p
    (set function value)
  (forall (z)
    (implies
     (q967972-set-member-p set z)
     (equal
      (q967972-function-value function z)
      value))))

(defun-sk q967972-constant-value-exists-p
    (complex set function)
  (exists (value)
    (and
     (q967972-c-member-p complex value)
     (q967972-constant-on-p
      set function value))))

(defun-sk q967972-subset-p (left right)
  (forall (x)
    (implies
     (q967972-set-member-p left x)
     (q967972-set-member-p right x))))

(defun-sk q967972-image-preimage-exists-p
    (space set function value)
  (exists (x)
    (and
     (q967972-e-member-p space x)
     (q967972-set-member-p set x)
     (equal
      (q967972-function-value function x)
      value))))

(defun-sk q967972-image-ball-covered-p
    (real complex space set function center radius)
  (forall (value)
    (implies
     (and
      (q967972-c-member-p complex value)
      (q967972-r-less
       real
       (q967972-c-norm
        real complex
        (q967972-c-subtract complex value center))
       radius))
     (q967972-image-preimage-exists-p
      space set function value))))

(defun-sk q967972-image-open-radius-exists-p
    (real complex space set function center)
  (exists (radius)
    (and
     (q967972-r-positive-p real radius)
     (q967972-image-ball-covered-p
      real complex space set function center radius))))

(defun-sk q967972-image-open-p
    (real complex space set function)
  (forall (center)
    (implies
     (and
      (q967972-c-member-p complex center)
      (q967972-image-preimage-exists-p
       space set function center))
     (q967972-image-open-radius-exists-p
      real complex space set function center))))

(defun-sk q967972-open-on-subsets-p
    (real complex space set function)
  (forall (subset)
    (implies
     (and
      (q967972-valid-e-set-p space subset)
      (q967972-subset-p subset set)
      (q967972-e-open-p real space subset))
     (q967972-image-open-p
      real complex space subset function))))

(defun-sk
    thousand-theorems-q967972-open-mapping-theorem-complex-analysis-statement
    ()
  (forall (real complex space set function)
    (implies
     (and
      (q967972-complex-field-p real complex)
      (q967972-normed-complex-space-p
       real complex space)
      (q967972-valid-e-set-p space set)
      (q967972-function-p space complex function)
      (q967972-analytic-on-neighborhood-p
       real complex space function set)
      (q967972-preconnected-p real space set))
     (or
      (q967972-constant-value-exists-p
       complex set function)
      (q967972-open-on-subsets-p
       real complex space set function)))))

(value-triple :itpeval-statement-checked)
:q
