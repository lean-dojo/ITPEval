;; Statement-only formalization of thousand-theorems corpus artifact Q2226868,
;; "Geometric mean theorem": in an arbitrary real inner-product affine space,
;; the altitude to the hypotenuse of a right triangle has squared length equal
;; to the product of the two hypotenuse-segment lengths. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative symbols present the source's real scalar field, arbitrary
;; real inner-product vector space, and arbitrary affine torsor. All carrier
;; restrictions and structural laws are explicit; no carrier is finite-coded
;; or restricted to ACL2's rational numbers.

(defstub q2226868-r-member-p (real x) t)
(defstub q2226868-r-set-member-p (real set x) t)
(defstub q2226868-v-member-p (vector-space x) t)
(defstub q2226868-p-member-p (point-space x) t)

(defstub q2226868-r-zero (real) t)
(defstub q2226868-r-one (real) t)
(defstub q2226868-r-add (real x y) t)
(defstub q2226868-r-mul (real x y) t)
(defstub q2226868-r-neg (real x) t)
(defstub q2226868-r-inv (real x) t)
(defstub q2226868-r-less (real x y) t)

(defstub q2226868-v-zero (real vector-space) t)
(defstub q2226868-v-add (real vector-space x y) t)
(defstub q2226868-v-neg (real vector-space x) t)
(defstub q2226868-v-smul (real vector-space scalar vector) t)
(defstub q2226868-inner (real vector-space x y) t)

(defstub q2226868-vadd
  (real vector-space point-space vector point)
  t)
(defstub q2226868-vsub
  (real vector-space point-space left-point right-point)
  t)

(defun q2226868-r-leq (real x y)
  (not (q2226868-r-less real y x)))

(defun-sk q2226868-real-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q2226868-r-member-p real x)
      (q2226868-r-member-p real y)
      (q2226868-r-member-p real z))
     (let ((zero (q2226868-r-zero real))
           (one (q2226868-r-one real)))
       (and
        (q2226868-r-member-p real (q2226868-r-add real x y))
        (q2226868-r-member-p real (q2226868-r-mul real x y))
        (q2226868-r-member-p real (q2226868-r-neg real x))
        (q2226868-r-member-p real (q2226868-r-inv real x))

        (equal
         (q2226868-r-add real (q2226868-r-add real x y) z)
         (q2226868-r-add real x (q2226868-r-add real y z)))
        (equal (q2226868-r-add real x y)
               (q2226868-r-add real y x))
        (equal (q2226868-r-add real x zero) x)
        (equal
         (q2226868-r-add real x (q2226868-r-neg real x))
         zero)

        (equal
         (q2226868-r-mul real (q2226868-r-mul real x y) z)
         (q2226868-r-mul real x (q2226868-r-mul real y z)))
        (equal (q2226868-r-mul real x y)
               (q2226868-r-mul real y x))
        (equal (q2226868-r-mul real x one) x)
        (equal (q2226868-r-mul real x zero) zero)
        (equal
         (q2226868-r-mul real x (q2226868-r-add real y z))
         (q2226868-r-add
          real
          (q2226868-r-mul real x y)
          (q2226868-r-mul real x z)))
        (implies
         (not (equal x zero))
         (equal
          (q2226868-r-mul real x (q2226868-r-inv real x))
          one))

        (not (q2226868-r-less real x x))
        (or (equal x y)
            (q2226868-r-less real x y)
            (q2226868-r-less real y x))
        (implies
         (and
          (q2226868-r-less real x y)
          (q2226868-r-less real y z))
         (q2226868-r-less real x z))
        (implies
         (q2226868-r-less real x y)
         (q2226868-r-less
          real
          (q2226868-r-add real x z)
          (q2226868-r-add real y z)))
        (implies
         (and
          (q2226868-r-less real zero x)
          (q2226868-r-less real zero y))
         (q2226868-r-less
          real zero (q2226868-r-mul real x y))))))))

(defun-sk q2226868-r-set-valid-p (real set)
  (forall (x)
    (implies
     (q2226868-r-set-member-p real set x)
     (q2226868-r-member-p real x))))

(defun-sk q2226868-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q2226868-r-member-p real x)
     (q2226868-r-set-member-p real set x))))

(defun-sk q2226868-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q2226868-r-member-p real x)
      (q2226868-r-set-member-p real set x))
     (q2226868-r-leq real x bound))))

(defun-sk q2226868-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q2226868-r-member-p real bound)
     (q2226868-r-upper-bound-p real set bound))))

(defun-sk q2226868-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q2226868-r-member-p real supremum)
     (q2226868-r-upper-bound-p real set supremum)
     (implies
      (and
       (q2226868-r-member-p real bound)
       (q2226868-r-upper-bound-p real set bound))
      (q2226868-r-leq real supremum bound)))))

(defun-sk q2226868-r-supremum-exists-p (real set)
  (exists (supremum)
    (q2226868-r-supremum-p real set supremum)))

(defun-sk q2226868-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q2226868-r-set-valid-p real set)
      (q2226868-r-set-nonempty-p real set)
      (q2226868-r-bounded-above-p real set))
     (q2226868-r-supremum-exists-p real set))))

(defun q2226868-real-p (real)
  (let ((zero (q2226868-r-zero real))
        (one (q2226868-r-one real)))
    (and
     (q2226868-r-member-p real zero)
     (q2226868-r-member-p real one)
     (not (equal zero one))
     (q2226868-r-less real zero one)
     (q2226868-real-field-laws-p real)
     (q2226868-r-dedekind-complete-p real))))

(defun-sk q2226868-vector-space-laws-p (real vector-space)
  (forall (a b u v w)
    (implies
     (and
      (q2226868-r-member-p real a)
      (q2226868-r-member-p real b)
      (q2226868-v-member-p vector-space u)
      (q2226868-v-member-p vector-space v)
      (q2226868-v-member-p vector-space w))
     (let ((zero-v (q2226868-v-zero real vector-space))
           (one-r (q2226868-r-one real)))
       (and
        (q2226868-v-member-p
         vector-space (q2226868-v-add real vector-space u v))
        (q2226868-v-member-p
         vector-space (q2226868-v-neg real vector-space u))
        (q2226868-v-member-p
         vector-space (q2226868-v-smul real vector-space a u))

        (equal
         (q2226868-v-add
          real vector-space
          (q2226868-v-add real vector-space u v)
          w)
         (q2226868-v-add
          real vector-space
          u
          (q2226868-v-add real vector-space v w)))
        (equal
         (q2226868-v-add real vector-space u v)
         (q2226868-v-add real vector-space v u))
        (equal
         (q2226868-v-add real vector-space u zero-v)
         u)
        (equal
         (q2226868-v-add
          real vector-space u
          (q2226868-v-neg real vector-space u))
         zero-v)

        (equal
         (q2226868-v-smul real vector-space one-r u)
         u)
        (equal
         (q2226868-v-smul
          real vector-space
          (q2226868-r-mul real a b)
          u)
         (q2226868-v-smul
          real vector-space
          a
          (q2226868-v-smul real vector-space b u)))
        (equal
         (q2226868-v-smul
          real vector-space
          (q2226868-r-add real a b)
          u)
         (q2226868-v-add
          real vector-space
          (q2226868-v-smul real vector-space a u)
          (q2226868-v-smul real vector-space b u)))
        (equal
         (q2226868-v-smul
          real vector-space
          a
          (q2226868-v-add real vector-space u v))
         (q2226868-v-add
          real vector-space
          (q2226868-v-smul real vector-space a u)
          (q2226868-v-smul real vector-space a v))))))))

(defun-sk q2226868-inner-product-laws-p (real vector-space)
  (forall (a u v w)
    (implies
     (and
      (q2226868-r-member-p real a)
      (q2226868-v-member-p vector-space u)
      (q2226868-v-member-p vector-space v)
      (q2226868-v-member-p vector-space w))
     (let ((zero-r (q2226868-r-zero real))
           (zero-v (q2226868-v-zero real vector-space)))
       (and
        (q2226868-r-member-p
         real (q2226868-inner real vector-space u v))
        (equal
         (q2226868-inner
          real vector-space
          (q2226868-v-add real vector-space u v)
          w)
         (q2226868-r-add
          real
          (q2226868-inner real vector-space u w)
          (q2226868-inner real vector-space v w)))
        (equal
         (q2226868-inner
          real vector-space
          (q2226868-v-smul real vector-space a u)
          v)
         (q2226868-r-mul
          real a (q2226868-inner real vector-space u v)))
        (equal
         (q2226868-inner real vector-space u v)
         (q2226868-inner real vector-space v u))
        (q2226868-r-leq
         real zero-r (q2226868-inner real vector-space u u))
        (iff
         (equal
          (q2226868-inner real vector-space u u)
          zero-r)
         (equal u zero-v)))))))

(defun-sk q2226868-point-space-nonempty-p (point-space)
  (exists (point)
    (q2226868-p-member-p point-space point)))

(defun-sk q2226868-affine-torsor-laws-p
    (real vector-space point-space)
  (forall (u v p q r)
    (implies
     (and
      (q2226868-v-member-p vector-space u)
      (q2226868-v-member-p vector-space v)
      (q2226868-p-member-p point-space p)
      (q2226868-p-member-p point-space q)
      (q2226868-p-member-p point-space r))
     (let ((zero-v (q2226868-v-zero real vector-space)))
       (and
        (q2226868-p-member-p
         point-space
         (q2226868-vadd real vector-space point-space u p))
        (q2226868-v-member-p
         vector-space
         (q2226868-vsub real vector-space point-space p q))
        (equal
         (q2226868-vadd
          real vector-space point-space zero-v p)
         p)
        (equal
         (q2226868-vadd
          real vector-space point-space
          (q2226868-v-add real vector-space u v)
          p)
         (q2226868-vadd
          real vector-space point-space u
          (q2226868-vadd
           real vector-space point-space v p)))
        (equal
         (q2226868-vadd
          real vector-space point-space
          (q2226868-vsub
           real vector-space point-space p q)
          q)
         p)
        (equal
         (q2226868-vsub
          real vector-space point-space
          (q2226868-vadd
           real vector-space point-space u p)
          p)
         u)
        (equal
         (q2226868-vsub real vector-space point-space p r)
         (q2226868-v-add
          real vector-space
          (q2226868-vsub
           real vector-space point-space p q)
          (q2226868-vsub
           real vector-space point-space q r))))))))

(defun q2226868-context-p (real vector-space point-space)
  (and
   (q2226868-real-p real)
   (q2226868-v-member-p
    vector-space (q2226868-v-zero real vector-space))
   (q2226868-vector-space-laws-p real vector-space)
   (q2226868-inner-product-laws-p real vector-space)
   (q2226868-point-space-nonempty-p point-space)
   (q2226868-affine-torsor-laws-p
    real vector-space point-space)))

(defun q2226868-distance-squared
    (real vector-space point-space p q)
  (let ((difference
         (q2226868-vsub
          real vector-space point-space p q)))
    (q2226868-inner
     real vector-space difference difference)))

;; Mathlib's unoriented angle is pi/2 exactly when the two displacement
;; vectors have zero inner product, including its degenerate-ray convention.
(defun q2226868-right-angle-p
    (real vector-space point-space first vertex third)
  (equal
   (q2226868-inner
    real vector-space
    (q2226868-vsub
     real vector-space point-space first vertex)
    (q2226868-vsub
     real vector-space point-space third vertex))
   (q2226868-r-zero real)))

;; This internal existential is exactly strict affine betweenness: p4 is the
;; line-map point p1 + ratio*(p3-p1), with 0 < ratio < 1 and p1 distinct from
;; p3. The witness is not exposed as an additional theorem parameter.
(defun-sk q2226868-strictly-between-p
    (real vector-space point-space p1 p4 p3)
  (exists (ratio)
    (and
     (q2226868-r-member-p real ratio)
     (q2226868-r-less real (q2226868-r-zero real) ratio)
     (q2226868-r-less real ratio (q2226868-r-one real))
     (not (equal p1 p3))
     (equal
      p4
      (q2226868-vadd
       real vector-space point-space
       (q2226868-v-smul
        real vector-space ratio
        (q2226868-vsub
         real vector-space point-space p3 p1))
       p1)))))

;; If A, B, and C are the squared distances p2-p4, p1-p4, and p3-p4,
;; respectively, the source equality A = sqrt(B)*sqrt(C) is equivalent over
;; the nonnegative reals to A^2 = B*C. Thus this removes only square roots.
(defun q2226868-geometric-mean-conclusion-p
    (real vector-space point-space p1 p2 p3 p4)
  (let ((a
         (q2226868-distance-squared
          real vector-space point-space p2 p4))
        (b
         (q2226868-distance-squared
          real vector-space point-space p1 p4))
        (c
         (q2226868-distance-squared
          real vector-space point-space p3 p4)))
    (equal
     (q2226868-r-mul real a a)
     (q2226868-r-mul real b c))))

(defun-sk thousand-theorems-q2226868-geometric-mean-theorem-statement
    (real vector-space point-space)
  (forall (p1 p2 p3 p4)
    (implies
     (and
      (q2226868-context-p real vector-space point-space)
      (q2226868-p-member-p point-space p1)
      (q2226868-p-member-p point-space p2)
      (q2226868-p-member-p point-space p3)
      (q2226868-p-member-p point-space p4)
      (q2226868-strictly-between-p
       real vector-space point-space p1 p4 p3)
      (q2226868-right-angle-p
       real vector-space point-space p1 p4 p2)
      (q2226868-right-angle-p
       real vector-space point-space p1 p2 p3))
     (q2226868-geometric-mean-conclusion-p
      real vector-space point-space p1 p2 p3 p4))))

(value-triple :itpeval-statement-checked)
:q
