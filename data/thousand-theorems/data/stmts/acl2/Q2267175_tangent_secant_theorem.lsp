;; Statement-only formalization of thousand-theorems corpus artifact Q2267175,
;; "Tangent-secant theorem": in an arbitrary real inner-product affine space,
;; the squared tangent length equals the product of the two secant lengths.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative symbols present the source's real scalar field, arbitrary
;; real inner-product vector space, and arbitrary affine torsor. All carrier
;; and structure laws are explicit; no carrier is finite-coded or restricted
;; to ACL2's rational numbers.

(defstub q2267175-r-member-p (real x) t)
(defstub q2267175-r-set-member-p (real set x) t)
(defstub q2267175-v-member-p (vector-space x) t)
(defstub q2267175-p-member-p (point-space x) t)

(defstub q2267175-r-zero (real) t)
(defstub q2267175-r-one (real) t)
(defstub q2267175-r-add (real x y) t)
(defstub q2267175-r-mul (real x y) t)
(defstub q2267175-r-neg (real x) t)
(defstub q2267175-r-inv (real x) t)
(defstub q2267175-r-less (real x y) t)

(defstub q2267175-v-zero (real vector-space) t)
(defstub q2267175-v-add (real vector-space x y) t)
(defstub q2267175-v-neg (real vector-space x) t)
(defstub q2267175-v-smul (real vector-space scalar vector) t)
(defstub q2267175-inner (real vector-space x y) t)

(defstub q2267175-vadd
  (real vector-space point-space vector point)
  t)
(defstub q2267175-vsub
  (real vector-space point-space left-point right-point)
  t)

(defun q2267175-r-leq (real x y)
  (not (q2267175-r-less real y x)))

(defun-sk q2267175-real-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q2267175-r-member-p real x)
      (q2267175-r-member-p real y)
      (q2267175-r-member-p real z))
     (let ((zero (q2267175-r-zero real))
           (one (q2267175-r-one real)))
       (and
        (q2267175-r-member-p real (q2267175-r-add real x y))
        (q2267175-r-member-p real (q2267175-r-mul real x y))
        (q2267175-r-member-p real (q2267175-r-neg real x))
        (q2267175-r-member-p real (q2267175-r-inv real x))

        (equal
         (q2267175-r-add real (q2267175-r-add real x y) z)
         (q2267175-r-add real x (q2267175-r-add real y z)))
        (equal
         (q2267175-r-add real x y)
         (q2267175-r-add real y x))
        (equal (q2267175-r-add real x zero) x)
        (equal
         (q2267175-r-add real x (q2267175-r-neg real x))
         zero)

        (equal
         (q2267175-r-mul real (q2267175-r-mul real x y) z)
         (q2267175-r-mul real x (q2267175-r-mul real y z)))
        (equal
         (q2267175-r-mul real x y)
         (q2267175-r-mul real y x))
        (equal (q2267175-r-mul real x one) x)
        (equal (q2267175-r-mul real x zero) zero)
        (equal
         (q2267175-r-mul real x (q2267175-r-add real y z))
         (q2267175-r-add
          real
          (q2267175-r-mul real x y)
          (q2267175-r-mul real x z)))
        (implies
         (not (equal x zero))
         (equal
          (q2267175-r-mul real x (q2267175-r-inv real x))
          one))

        (not (q2267175-r-less real x x))
        (or
         (equal x y)
         (q2267175-r-less real x y)
         (q2267175-r-less real y x))
        (implies
         (and
          (q2267175-r-less real x y)
          (q2267175-r-less real y z))
         (q2267175-r-less real x z))
        (implies
         (q2267175-r-less real x y)
         (q2267175-r-less
          real
          (q2267175-r-add real x z)
          (q2267175-r-add real y z)))
        (implies
         (and
          (q2267175-r-less real zero x)
          (q2267175-r-less real zero y))
         (q2267175-r-less
          real zero (q2267175-r-mul real x y))))))))

(defun-sk q2267175-r-set-valid-p (real set)
  (forall (x)
    (implies
     (q2267175-r-set-member-p real set x)
     (q2267175-r-member-p real x))))

(defun-sk q2267175-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q2267175-r-member-p real x)
     (q2267175-r-set-member-p real set x))))

(defun-sk q2267175-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q2267175-r-member-p real x)
      (q2267175-r-set-member-p real set x))
     (q2267175-r-leq real x bound))))

(defun-sk q2267175-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q2267175-r-member-p real bound)
     (q2267175-r-upper-bound-p real set bound))))

(defun-sk q2267175-r-least-upper-bound-p
    (real set supremum)
  (forall (bound)
    (implies
     (and
      (q2267175-r-member-p real bound)
      (q2267175-r-upper-bound-p real set bound))
     (q2267175-r-leq real supremum bound))))

(defun q2267175-r-supremum-p (real set supremum)
  (and
   (q2267175-r-member-p real supremum)
   (q2267175-r-upper-bound-p real set supremum)
   (q2267175-r-least-upper-bound-p real set supremum)))

(defun-sk q2267175-r-supremum-exists-p (real set)
  (exists (supremum)
    (q2267175-r-supremum-p real set supremum)))

(defun-sk q2267175-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q2267175-r-set-valid-p real set)
      (q2267175-r-set-nonempty-p real set)
      (q2267175-r-bounded-above-p real set))
     (q2267175-r-supremum-exists-p real set))))

(defun q2267175-real-p (real)
  (let ((zero (q2267175-r-zero real))
        (one (q2267175-r-one real)))
    (and
     (q2267175-r-member-p real zero)
     (q2267175-r-member-p real one)
     (not (equal zero one))
     (q2267175-r-less real zero one)
     (q2267175-real-field-laws-p real)
     (q2267175-r-dedekind-complete-p real))))

(defun-sk q2267175-vector-space-laws-p (real vector-space)
  (forall (a b u v w)
    (implies
     (and
      (q2267175-r-member-p real a)
      (q2267175-r-member-p real b)
      (q2267175-v-member-p vector-space u)
      (q2267175-v-member-p vector-space v)
      (q2267175-v-member-p vector-space w))
     (let ((zero-v (q2267175-v-zero real vector-space))
           (one (q2267175-r-one real)))
       (and
        (q2267175-v-member-p
         vector-space (q2267175-v-add real vector-space u v))
        (q2267175-v-member-p
         vector-space (q2267175-v-neg real vector-space u))
        (q2267175-v-member-p
         vector-space (q2267175-v-smul real vector-space a u))

        (equal
         (q2267175-v-add
          real vector-space
          (q2267175-v-add real vector-space u v)
          w)
         (q2267175-v-add
          real vector-space
          u
          (q2267175-v-add real vector-space v w)))
        (equal
         (q2267175-v-add real vector-space u v)
         (q2267175-v-add real vector-space v u))
        (equal (q2267175-v-add real vector-space u zero-v) u)
        (equal
         (q2267175-v-add
          real vector-space u (q2267175-v-neg real vector-space u))
         zero-v)

        (equal
         (q2267175-v-smul real vector-space one u)
         u)
        (equal
         (q2267175-v-smul
          real vector-space (q2267175-r-mul real a b) u)
         (q2267175-v-smul
          real vector-space
          a
          (q2267175-v-smul real vector-space b u)))
        (equal
         (q2267175-v-smul
          real vector-space (q2267175-r-add real a b) u)
         (q2267175-v-add
          real vector-space
          (q2267175-v-smul real vector-space a u)
          (q2267175-v-smul real vector-space b u)))
        (equal
         (q2267175-v-smul
          real vector-space
          a
          (q2267175-v-add real vector-space u v))
         (q2267175-v-add
          real vector-space
          (q2267175-v-smul real vector-space a u)
          (q2267175-v-smul real vector-space a v))))))))

(defun-sk q2267175-inner-product-laws-p (real vector-space)
  (forall (a u v w)
    (implies
     (and
      (q2267175-r-member-p real a)
      (q2267175-v-member-p vector-space u)
      (q2267175-v-member-p vector-space v)
      (q2267175-v-member-p vector-space w))
     (let ((zero-r (q2267175-r-zero real))
           (zero-v (q2267175-v-zero real vector-space)))
       (and
        (q2267175-r-member-p
         real (q2267175-inner real vector-space u v))
        (equal
         (q2267175-inner
          real vector-space
          (q2267175-v-add real vector-space u v)
          w)
         (q2267175-r-add
          real
          (q2267175-inner real vector-space u w)
          (q2267175-inner real vector-space v w)))
        (equal
         (q2267175-inner
          real vector-space
          (q2267175-v-smul real vector-space a u)
          v)
         (q2267175-r-mul
          real a (q2267175-inner real vector-space u v)))
        (equal
         (q2267175-inner real vector-space u v)
         (q2267175-inner real vector-space v u))
        (q2267175-r-leq
         real zero-r (q2267175-inner real vector-space u u))
        (iff
         (equal
          (q2267175-inner real vector-space u u)
          zero-r)
         (equal u zero-v)))))))

(defun-sk q2267175-point-space-nonempty-p (point-space)
  (exists (point)
    (q2267175-p-member-p point-space point)))

(defun-sk q2267175-affine-torsor-laws-p
    (real vector-space point-space)
  (forall (u v p q r)
    (implies
     (and
      (q2267175-v-member-p vector-space u)
      (q2267175-v-member-p vector-space v)
      (q2267175-p-member-p point-space p)
      (q2267175-p-member-p point-space q)
      (q2267175-p-member-p point-space r))
     (let ((zero-v (q2267175-v-zero real vector-space)))
       (and
        (q2267175-p-member-p
         point-space
         (q2267175-vadd real vector-space point-space u p))
        (q2267175-v-member-p
         vector-space
         (q2267175-vsub real vector-space point-space p q))
        (equal
         (q2267175-vadd
          real vector-space point-space zero-v p)
         p)
        (equal
         (q2267175-vadd
          real vector-space point-space
          (q2267175-v-add real vector-space u v)
          p)
         (q2267175-vadd
          real vector-space point-space
          u
          (q2267175-vadd
           real vector-space point-space v p)))
        (equal
         (q2267175-vadd
          real vector-space point-space
          (q2267175-vsub
           real vector-space point-space p q)
          q)
         p)
        (equal
         (q2267175-vsub
          real vector-space point-space
          (q2267175-vadd
           real vector-space point-space u p)
          p)
         u)
        (equal
         (q2267175-vsub real vector-space point-space p r)
         (q2267175-v-add
          real vector-space
          (q2267175-vsub
           real vector-space point-space p q)
          (q2267175-vsub
           real vector-space point-space q r))))))))

(defun q2267175-context-p (real vector-space point-space)
  (and
   (q2267175-real-p real)
   (q2267175-v-member-p
    vector-space (q2267175-v-zero real vector-space))
   (q2267175-vector-space-laws-p real vector-space)
   (q2267175-inner-product-laws-p real vector-space)
   (q2267175-point-space-nonempty-p point-space)
   (q2267175-affine-torsor-laws-p
    real vector-space point-space)))

(defun q2267175-squared-distance
    (real vector-space point-space left right)
  (let ((displacement
         (q2267175-vsub
          real vector-space point-space left right)))
    (q2267175-inner
     real vector-space displacement displacement)))

;; This is exactly membership in Mathlib's affine line through a and b. The
;; scalar witness remains internally existential, including the degenerate
;; case a=b.
(defun-sk q2267175-on-line-p
    (real vector-space point-space a b p)
  (exists (scale)
    (and
     (q2267175-r-member-p real scale)
     (equal
      p
      (q2267175-vadd
       real vector-space point-space
       (q2267175-v-smul
        real vector-space scale
        (q2267175-vsub
         real vector-space point-space b a))
       a)))))

;; For a nonnegative real radius, equality of squared distance and radius
;; squared is equivalent to Mathlib's metric-sphere membership equation.
(defun q2267175-sphere-member-p
    (real vector-space point-space center radius point)
  (and
   (q2267175-r-member-p real radius)
   (q2267175-r-leq real (q2267175-r-zero real) radius)
   (equal
    (q2267175-squared-distance
     real vector-space point-space point center)
    (q2267175-r-mul real radius radius))))

;; For line[p,t], Mathlib's IsTangentAt structure is equivalent to t lying on
;; the sphere and the line direction p-t being orthogonal to the radius t-c.
;; This also preserves the degenerate case p=t.
(defun q2267175-tangent-line-at-p
    (real vector-space point-space center radius p tangent-point)
  (and
   (q2267175-sphere-member-p
    real vector-space point-space center radius tangent-point)
   (equal
    (q2267175-inner
     real vector-space
     (q2267175-vsub
      real vector-space point-space p tangent-point)
     (q2267175-vsub
      real vector-space point-space tangent-point center))
    (q2267175-r-zero real))))

;; If A, B, and C are the squared distances p-t, p-a, and p-b, the source
;; equality A = sqrt(B)*sqrt(C) is equivalent over nonnegative reals to
;; A^2 = B*C. Thus this conclusion removes square roots but no solutions.
(defun q2267175-tangent-secant-conclusion-p
    (real vector-space point-space a b tangent-point p)
  (let ((a-square
         (q2267175-squared-distance
          real vector-space point-space p tangent-point))
        (b-square
         (q2267175-squared-distance
          real vector-space point-space p a))
        (c-square
         (q2267175-squared-distance
          real vector-space point-space p b)))
    (equal
     (q2267175-r-mul real a-square a-square)
     (q2267175-r-mul real b-square c-square))))

(defun-sk thousand-theorems-q2267175-tangent-secant-theorem-statement
    (real vector-space point-space)
  (forall (center radius a b tangent-point p)
    (implies
     (and
      (q2267175-context-p real vector-space point-space)
      (q2267175-p-member-p point-space center)
      (q2267175-r-member-p real radius)
      (q2267175-p-member-p point-space a)
      (q2267175-p-member-p point-space b)
      (q2267175-p-member-p point-space tangent-point)
      (q2267175-p-member-p point-space p)
      (q2267175-sphere-member-p
       real vector-space point-space center radius a)
      (q2267175-sphere-member-p
       real vector-space point-space center radius b)
      (q2267175-on-line-p
       real vector-space point-space a b p)
      (q2267175-tangent-line-at-p
       real vector-space point-space center radius p tangent-point))
     (q2267175-tangent-secant-conclusion-p
      real vector-space point-space a b tangent-point p))))

(value-triple :itpeval-statement-checked)
:q
