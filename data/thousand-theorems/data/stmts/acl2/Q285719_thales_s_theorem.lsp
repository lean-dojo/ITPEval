;; Statement-only formalization of thousand-theorems corpus artifact Q285719,
;; "Thales's theorem": in an arbitrary real inner-product affine space,
;; diameter endpoints of a sphere determine a right angle at exactly the
;; points lying on that sphere. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative symbols present arbitrary real-scalar, vector, and affine
;; point carriers. All typing and structural laws used below are explicit;
;; no carrier is enumerated or restricted to ACL2's rational numbers.

(defstub q285719-r-member-p (real x) t)
(defstub q285719-v-member-p (vector-space x) t)
(defstub q285719-p-member-p (point-space x) t)

(defstub q285719-r-zero (real) t)
(defstub q285719-r-one (real) t)
(defstub q285719-r-add (real x y) t)
(defstub q285719-r-mul (real x y) t)
(defstub q285719-r-neg (real x) t)
(defstub q285719-r-inv (real x) t)
(defstub q285719-r-less (real x y) t)
(defstub q285719-r-set-member-p (real set x) t)

(defstub q285719-v-zero (real vector-space) t)
(defstub q285719-v-add (real vector-space x y) t)
(defstub q285719-v-neg (real vector-space x) t)
(defstub q285719-v-smul (real vector-space scalar vector) t)
(defstub q285719-inner (real vector-space x y) t)

(defstub q285719-vadd
  (real vector-space point-space vector point)
  t)
(defstub q285719-vsub
  (real vector-space point-space left-point right-point)
  t)

(defun q285719-r-leq (real x y)
  (not (q285719-r-less real y x)))

(defun-sk q285719-real-field-laws-p (real)
  (forall (x y z)
    (implies
     (and (q285719-r-member-p real x)
          (q285719-r-member-p real y)
          (q285719-r-member-p real z))
     (let ((zero (q285719-r-zero real))
           (one (q285719-r-one real)))
       (and
        (q285719-r-member-p real (q285719-r-add real x y))
        (q285719-r-member-p real (q285719-r-mul real x y))
        (q285719-r-member-p real (q285719-r-neg real x))
        (q285719-r-member-p real (q285719-r-inv real x))
        (equal (q285719-r-add real x y)
               (q285719-r-add real y x))
        (equal (q285719-r-add real (q285719-r-add real x y) z)
               (q285719-r-add real x (q285719-r-add real y z)))
        (equal (q285719-r-add real x zero) x)
        (equal (q285719-r-add real x (q285719-r-neg real x))
               zero)
        (equal (q285719-r-mul real x y)
               (q285719-r-mul real y x))
        (equal (q285719-r-mul real (q285719-r-mul real x y) z)
               (q285719-r-mul real x (q285719-r-mul real y z)))
        (equal (q285719-r-mul real x one) x)
        (equal (q285719-r-mul real x zero) zero)
        (equal
         (q285719-r-mul real x (q285719-r-add real y z))
         (q285719-r-add real
                        (q285719-r-mul real x y)
                        (q285719-r-mul real x z)))
        (implies
         (not (equal x zero))
         (equal (q285719-r-mul real x (q285719-r-inv real x))
                one))
        (not (q285719-r-less real x x))
        (or (equal x y)
            (q285719-r-less real x y)
            (q285719-r-less real y x))
        (implies
         (and (q285719-r-less real x y)
              (q285719-r-less real y z))
         (q285719-r-less real x z))
        (implies
         (q285719-r-less real x y)
         (q285719-r-less real
                         (q285719-r-add real x z)
                         (q285719-r-add real y z)))
        (implies
         (and (q285719-r-less real zero x)
              (q285719-r-less real zero y))
         (q285719-r-less real zero
                         (q285719-r-mul real x y))))))))

(defun-sk q285719-r-set-nonempty-p (real set)
  (exists (x)
    (and (q285719-r-member-p real x)
         (q285719-r-set-member-p real set x))))

(defun-sk q285719-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and (q285719-r-member-p real x)
          (q285719-r-set-member-p real set x))
     (q285719-r-leq real x bound))))

(defun-sk q285719-r-bounded-above-p (real set)
  (exists (bound)
    (and (q285719-r-member-p real bound)
         (q285719-r-upper-bound-p real set bound))))

(defun-sk q285719-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q285719-r-member-p real supremum)
     (q285719-r-upper-bound-p real set supremum)
     (implies
      (and (q285719-r-member-p real bound)
           (q285719-r-upper-bound-p real set bound))
      (q285719-r-leq real supremum bound)))))

(defun-sk q285719-r-supremum-exists-p (real set)
  (exists (supremum)
    (q285719-r-supremum-p real set supremum)))

(defun-sk q285719-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and (q285719-r-set-nonempty-p real set)
          (q285719-r-bounded-above-p real set))
     (q285719-r-supremum-exists-p real set))))

(defun q285719-real-p (real)
  (let ((zero (q285719-r-zero real))
        (one (q285719-r-one real)))
    (and
     (q285719-r-member-p real zero)
     (q285719-r-member-p real one)
     (not (equal zero one))
     (q285719-r-less real zero one)
     (q285719-real-field-laws-p real)
     (q285719-r-dedekind-complete-p real))))

(defun-sk q285719-vector-space-laws-p (real vector-space)
  (forall (a b u v w)
    (implies
     (and (q285719-r-member-p real a)
          (q285719-r-member-p real b)
          (q285719-v-member-p vector-space u)
          (q285719-v-member-p vector-space v)
          (q285719-v-member-p vector-space w))
     (let ((zero-v (q285719-v-zero real vector-space))
           (one (q285719-r-one real)))
       (and
        (q285719-v-member-p
         vector-space (q285719-v-add real vector-space u v))
        (q285719-v-member-p
         vector-space (q285719-v-neg real vector-space u))
        (q285719-v-member-p
         vector-space (q285719-v-smul real vector-space a u))
        (equal (q285719-v-add real vector-space u v)
               (q285719-v-add real vector-space v u))
        (equal
         (q285719-v-add
          real vector-space (q285719-v-add real vector-space u v) w)
         (q285719-v-add
          real vector-space u (q285719-v-add real vector-space v w)))
        (equal (q285719-v-add real vector-space u zero-v) u)
        (equal
         (q285719-v-add real vector-space
                        u (q285719-v-neg real vector-space u))
         zero-v)
        (equal
         (q285719-v-smul
          real vector-space a (q285719-v-add real vector-space u v))
         (q285719-v-add
          real vector-space
          (q285719-v-smul real vector-space a u)
          (q285719-v-smul real vector-space a v)))
        (equal
         (q285719-v-smul
          real vector-space (q285719-r-add real a b) u)
         (q285719-v-add
          real vector-space
          (q285719-v-smul real vector-space a u)
          (q285719-v-smul real vector-space b u)))
        (equal
         (q285719-v-smul
          real vector-space (q285719-r-mul real a b) u)
         (q285719-v-smul
          real vector-space a
          (q285719-v-smul real vector-space b u)))
        (equal (q285719-v-smul real vector-space one u) u))))))

(defun-sk q285719-inner-product-laws-p (real vector-space)
  (forall (a u v w)
    (implies
     (and (q285719-r-member-p real a)
          (q285719-v-member-p vector-space u)
          (q285719-v-member-p vector-space v)
          (q285719-v-member-p vector-space w))
     (let ((zero-r (q285719-r-zero real))
           (zero-v (q285719-v-zero real vector-space)))
       (and
        (q285719-r-member-p real
                            (q285719-inner real vector-space u v))
        (equal (q285719-inner real vector-space u v)
               (q285719-inner real vector-space v u))
        (equal
         (q285719-inner
          real vector-space (q285719-v-add real vector-space u v) w)
         (q285719-r-add
          real
          (q285719-inner real vector-space u w)
          (q285719-inner real vector-space v w)))
        (equal
         (q285719-inner
          real vector-space (q285719-v-smul real vector-space a u) v)
         (q285719-r-mul
          real a (q285719-inner real vector-space u v)))
        (q285719-r-leq
         real zero-r (q285719-inner real vector-space u u))
        (equal
         (equal (q285719-inner real vector-space u u) zero-r)
         (equal u zero-v)))))))

(defun-sk q285719-point-space-nonempty-p (point-space)
  (exists (point)
    (q285719-p-member-p point-space point)))

(defun-sk q285719-affine-torsor-laws-p
    (real vector-space point-space)
  (forall (u v p q r)
    (implies
     (and (q285719-v-member-p vector-space u)
          (q285719-v-member-p vector-space v)
          (q285719-p-member-p point-space p)
          (q285719-p-member-p point-space q)
          (q285719-p-member-p point-space r))
     (let ((zero-v (q285719-v-zero real vector-space)))
       (and
        (q285719-p-member-p
         point-space
         (q285719-vadd real vector-space point-space u p))
        (q285719-v-member-p
         vector-space
         (q285719-vsub real vector-space point-space p q))
        (equal
         (q285719-vadd real vector-space point-space zero-v p)
         p)
        (equal
         (q285719-vadd
          real vector-space point-space
          (q285719-v-add real vector-space u v) p)
         (q285719-vadd
          real vector-space point-space u
          (q285719-vadd real vector-space point-space v p)))
        (equal
         (q285719-vadd
          real vector-space point-space
          (q285719-vsub real vector-space point-space p q) q)
         p)
        (equal
         (q285719-vsub
          real vector-space point-space
          (q285719-vadd real vector-space point-space u p) p)
         u)
        (equal
         (q285719-vsub real vector-space point-space p r)
         (q285719-v-add
          real vector-space
          (q285719-vsub real vector-space point-space p q)
          (q285719-vsub real vector-space point-space q r))))))))

(defun q285719-context-p (real vector-space point-space)
  (and
   (q285719-real-p real)
   (q285719-v-member-p
    vector-space (q285719-v-zero real vector-space))
   (q285719-vector-space-laws-p real vector-space)
   (q285719-inner-product-laws-p real vector-space)
   (q285719-point-space-nonempty-p point-space)
   (q285719-affine-torsor-laws-p real vector-space point-space)))

(defun q285719-norm-squared (real vector-space vector)
  (q285719-inner real vector-space vector vector))

;; A metric-sphere membership equation is rendered without square roots.
;; Nonnegativity of the radius makes this exactly dist(point,center)=radius.
(defun q285719-sphere-member-p
    (real vector-space point-space center radius point)
  (let ((displacement
         (q285719-vsub
          real vector-space point-space point center)))
    (and
     (q285719-r-member-p real radius)
     (q285719-r-leq real (q285719-r-zero real) radius)
     (equal
      (q285719-norm-squared real vector-space displacement)
      (q285719-r-mul real radius radius)))))

;; Under the affine torsor laws, opposite center-displacement vectors are
;; equivalent to midpoint(p1,p3)=center. Together with left membership this
;; is exactly the source structure Sphere.IsDiameter.
(defun q285719-is-diameter-p
    (real vector-space point-space center radius p1 p3)
  (and
   (q285719-sphere-member-p
    real vector-space point-space center radius p1)
   (equal
    (q285719-vsub
     real vector-space point-space p1 center)
    (q285719-v-neg
     real vector-space
     (q285719-vsub
      real vector-space point-space p3 center)))))

;; Mathlib's angle is pi/2 exactly when the two rays have zero inner product,
;; including its degenerate zero-ray convention.
(defun q285719-right-angle-p
    (real vector-space point-space p1 p2 p3)
  (equal
   (q285719-inner
    real vector-space
    (q285719-vsub real vector-space point-space p1 p2)
    (q285719-vsub real vector-space point-space p3 p2))
   (q285719-r-zero real)))

(defun-sk thousand-theorems-q285719-thales-theorem-statement
    (real vector-space point-space)
  (forall (center radius p1 p2 p3)
    (implies
     (and
      (q285719-context-p real vector-space point-space)
      (q285719-p-member-p point-space center)
      (q285719-p-member-p point-space p1)
      (q285719-p-member-p point-space p2)
      (q285719-p-member-p point-space p3)
      (q285719-is-diameter-p
       real vector-space point-space center radius p1 p3))
     (iff
      (q285719-right-angle-p
       real vector-space point-space p1 p2 p3)
      (q285719-sphere-member-p
       real vector-space point-space center radius p2)))))

(value-triple :itpeval-statement-checked)
:q
