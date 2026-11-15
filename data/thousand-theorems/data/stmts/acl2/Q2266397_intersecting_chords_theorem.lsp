;; Statement-only formalization of thousand-theorems corpus artifact Q2266397,
;; "Intersecting chords theorem": cospherical endpoint pairs forming two
;; straight angles at a common point have equal products of distances in an
;; arbitrary real inner-product affine space. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative symbols present arbitrary real-scalar, vector, and affine
;; point carriers. All typing and structural laws used below are explicit;
;; no carrier is enumerated or restricted to ACL2's rational numbers.

(defstub q2266397-r-member-p (real x) t)
(defstub q2266397-v-member-p (vector-space x) t)
(defstub q2266397-p-member-p (point-space x) t)

(defstub q2266397-r-zero (real) t)
(defstub q2266397-r-one (real) t)
(defstub q2266397-r-add (real x y) t)
(defstub q2266397-r-mul (real x y) t)
(defstub q2266397-r-neg (real x) t)
(defstub q2266397-r-inv (real x) t)
(defstub q2266397-r-less (real x y) t)
(defstub q2266397-r-set-member-p (real set x) t)

(defstub q2266397-v-zero (real vector-space) t)
(defstub q2266397-v-add (real vector-space x y) t)
(defstub q2266397-v-neg (real vector-space x) t)
(defstub q2266397-v-smul (real vector-space scalar vector) t)
(defstub q2266397-inner (real vector-space x y) t)

(defstub q2266397-vadd
  (real vector-space point-space vector point)
  t)
(defstub q2266397-vsub
  (real vector-space point-space left-point right-point)
  t)

(defun q2266397-r-leq (real x y)
  (not (q2266397-r-less real y x)))

(defun-sk q2266397-real-field-laws-p (real)
  (forall (x y z)
    (implies
     (and (q2266397-r-member-p real x)
          (q2266397-r-member-p real y)
          (q2266397-r-member-p real z))
     (let ((zero (q2266397-r-zero real))
           (one (q2266397-r-one real)))
       (and
        (q2266397-r-member-p real (q2266397-r-add real x y))
        (q2266397-r-member-p real (q2266397-r-mul real x y))
        (q2266397-r-member-p real (q2266397-r-neg real x))
        (q2266397-r-member-p real (q2266397-r-inv real x))
        (equal (q2266397-r-add real x y)
               (q2266397-r-add real y x))
        (equal (q2266397-r-add real (q2266397-r-add real x y) z)
               (q2266397-r-add real x (q2266397-r-add real y z)))
        (equal (q2266397-r-add real x zero) x)
        (equal (q2266397-r-add real x (q2266397-r-neg real x))
               zero)
        (equal (q2266397-r-mul real x y)
               (q2266397-r-mul real y x))
        (equal (q2266397-r-mul real (q2266397-r-mul real x y) z)
               (q2266397-r-mul real x (q2266397-r-mul real y z)))
        (equal (q2266397-r-mul real x one) x)
        (equal (q2266397-r-mul real x zero) zero)
        (equal
         (q2266397-r-mul real x (q2266397-r-add real y z))
         (q2266397-r-add
          real
          (q2266397-r-mul real x y)
          (q2266397-r-mul real x z)))
        (implies
         (not (equal x zero))
         (equal (q2266397-r-mul real x (q2266397-r-inv real x))
                one))
        (not (q2266397-r-less real x x))
        (or (equal x y)
            (q2266397-r-less real x y)
            (q2266397-r-less real y x))
        (implies
         (and (q2266397-r-less real x y)
              (q2266397-r-less real y z))
         (q2266397-r-less real x z))
        (implies
         (q2266397-r-less real x y)
         (q2266397-r-less
          real
          (q2266397-r-add real x z)
          (q2266397-r-add real y z)))
        (implies
         (and (q2266397-r-less real zero x)
              (q2266397-r-less real zero y))
         (q2266397-r-less
          real zero (q2266397-r-mul real x y))))))))

(defun-sk q2266397-r-set-nonempty-p (real set)
  (exists (x)
    (and (q2266397-r-member-p real x)
         (q2266397-r-set-member-p real set x))))

(defun-sk q2266397-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and (q2266397-r-member-p real x)
          (q2266397-r-set-member-p real set x))
     (q2266397-r-leq real x bound))))

(defun-sk q2266397-r-bounded-above-p (real set)
  (exists (bound)
    (and (q2266397-r-member-p real bound)
         (q2266397-r-upper-bound-p real set bound))))

(defun-sk q2266397-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q2266397-r-member-p real supremum)
     (q2266397-r-upper-bound-p real set supremum)
     (implies
      (and (q2266397-r-member-p real bound)
           (q2266397-r-upper-bound-p real set bound))
      (q2266397-r-leq real supremum bound)))))

(defun-sk q2266397-r-supremum-exists-p (real set)
  (exists (supremum)
    (q2266397-r-supremum-p real set supremum)))

(defun-sk q2266397-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and (q2266397-r-set-nonempty-p real set)
          (q2266397-r-bounded-above-p real set))
     (q2266397-r-supremum-exists-p real set))))

(defun q2266397-real-p (real)
  (let ((zero (q2266397-r-zero real))
        (one (q2266397-r-one real)))
    (and
     (q2266397-r-member-p real zero)
     (q2266397-r-member-p real one)
     (not (equal zero one))
     (q2266397-r-less real zero one)
     (q2266397-real-field-laws-p real)
     (q2266397-r-dedekind-complete-p real))))

(defun-sk q2266397-vector-space-laws-p (real vector-space)
  (forall (a b u v w)
    (implies
     (and (q2266397-r-member-p real a)
          (q2266397-r-member-p real b)
          (q2266397-v-member-p vector-space u)
          (q2266397-v-member-p vector-space v)
          (q2266397-v-member-p vector-space w))
     (let ((zero-v (q2266397-v-zero real vector-space))
           (one (q2266397-r-one real)))
       (and
        (q2266397-v-member-p
         vector-space (q2266397-v-add real vector-space u v))
        (q2266397-v-member-p
         vector-space (q2266397-v-neg real vector-space u))
        (q2266397-v-member-p
         vector-space (q2266397-v-smul real vector-space a u))
        (equal (q2266397-v-add real vector-space u v)
               (q2266397-v-add real vector-space v u))
        (equal
         (q2266397-v-add
          real vector-space
          (q2266397-v-add real vector-space u v)
          w)
         (q2266397-v-add
          real vector-space
          u
          (q2266397-v-add real vector-space v w)))
        (equal (q2266397-v-add real vector-space u zero-v) u)
        (equal
         (q2266397-v-add
          real vector-space u (q2266397-v-neg real vector-space u))
         zero-v)
        (equal
         (q2266397-v-smul
          real vector-space a
          (q2266397-v-add real vector-space u v))
         (q2266397-v-add
          real vector-space
          (q2266397-v-smul real vector-space a u)
          (q2266397-v-smul real vector-space a v)))
        (equal
         (q2266397-v-smul
          real vector-space (q2266397-r-add real a b) u)
         (q2266397-v-add
          real vector-space
          (q2266397-v-smul real vector-space a u)
          (q2266397-v-smul real vector-space b u)))
        (equal
         (q2266397-v-smul
          real vector-space (q2266397-r-mul real a b) u)
         (q2266397-v-smul
          real vector-space
          a
          (q2266397-v-smul real vector-space b u)))
        (equal (q2266397-v-smul real vector-space one u) u))))))

(defun-sk q2266397-inner-product-laws-p (real vector-space)
  (forall (a u v w)
    (implies
     (and (q2266397-r-member-p real a)
          (q2266397-v-member-p vector-space u)
          (q2266397-v-member-p vector-space v)
          (q2266397-v-member-p vector-space w))
     (let ((zero-r (q2266397-r-zero real))
           (zero-v (q2266397-v-zero real vector-space)))
       (and
        (q2266397-r-member-p
         real (q2266397-inner real vector-space u v))
        (equal (q2266397-inner real vector-space u v)
               (q2266397-inner real vector-space v u))
        (equal
         (q2266397-inner
          real vector-space
          (q2266397-v-add real vector-space u v)
          w)
         (q2266397-r-add
          real
          (q2266397-inner real vector-space u w)
          (q2266397-inner real vector-space v w)))
        (equal
         (q2266397-inner
          real vector-space
          (q2266397-v-smul real vector-space a u)
          v)
         (q2266397-r-mul
          real a (q2266397-inner real vector-space u v)))
        (q2266397-r-leq
         real zero-r (q2266397-inner real vector-space u u))
        (equal
         (equal (q2266397-inner real vector-space u u) zero-r)
         (equal u zero-v)))))))

(defun-sk q2266397-point-space-nonempty-p (point-space)
  (exists (point)
    (q2266397-p-member-p point-space point)))

(defun-sk q2266397-affine-torsor-laws-p
    (real vector-space point-space)
  (forall (u v p q r)
    (implies
     (and (q2266397-v-member-p vector-space u)
          (q2266397-v-member-p vector-space v)
          (q2266397-p-member-p point-space p)
          (q2266397-p-member-p point-space q)
          (q2266397-p-member-p point-space r))
     (let ((zero-v (q2266397-v-zero real vector-space)))
       (and
        (q2266397-p-member-p
         point-space
         (q2266397-vadd real vector-space point-space u p))
        (q2266397-v-member-p
         vector-space
         (q2266397-vsub real vector-space point-space p q))
        (equal
         (q2266397-vadd real vector-space point-space zero-v p)
         p)
        (equal
         (q2266397-vadd
          real vector-space point-space
          (q2266397-v-add real vector-space u v)
          p)
         (q2266397-vadd
          real vector-space point-space u
          (q2266397-vadd real vector-space point-space v p)))
        (equal
         (q2266397-vadd
          real vector-space point-space
          (q2266397-vsub real vector-space point-space p q)
          q)
         p)
        (equal
         (q2266397-vsub
          real vector-space point-space
          (q2266397-vadd real vector-space point-space u p)
          p)
         u)
        (equal
         (q2266397-vsub real vector-space point-space p r)
         (q2266397-v-add
          real vector-space
          (q2266397-vsub real vector-space point-space p q)
          (q2266397-vsub real vector-space point-space q r))))))))

(defun q2266397-context-p (real vector-space point-space)
  (and
   (q2266397-real-p real)
   (q2266397-v-member-p
    vector-space (q2266397-v-zero real vector-space))
   (q2266397-vector-space-laws-p real vector-space)
   (q2266397-inner-product-laws-p real vector-space)
   (q2266397-point-space-nonempty-p point-space)
   (q2266397-affine-torsor-laws-p real vector-space point-space)))

(defun q2266397-squared-distance
    (real vector-space point-space left right)
  (let ((displacement
         (q2266397-vsub
          real vector-space point-space left right)))
    (q2266397-inner
     real vector-space displacement displacement)))

;; For a nonempty four-point set, a common center with equal squared
;; distances is equivalent to Mathlib's Cospherical predicate.
(defun-sk q2266397-cospherical-four-p
    (real vector-space point-space a b c d)
  (exists (center)
    (and
     (q2266397-p-member-p point-space center)
     (equal
      (q2266397-squared-distance
       real vector-space point-space a center)
      (q2266397-squared-distance
       real vector-space point-space b center))
     (equal
      (q2266397-squared-distance
       real vector-space point-space a center)
      (q2266397-squared-distance
       real vector-space point-space c center))
     (equal
      (q2266397-squared-distance
       real vector-space point-space a center)
      (q2266397-squared-distance
       real vector-space point-space d center)))))

;; Mathlib's unoriented angle at p is pi exactly when both displacement
;; vectors are nonzero and one is a negative scalar multiple of the other.
(defun-sk q2266397-angle-pi-p
    (real vector-space point-space left vertex right)
  (exists (scale)
    (let ((left-vector
           (q2266397-vsub
            real vector-space point-space left vertex))
          (right-vector
           (q2266397-vsub
            real vector-space point-space right vertex))
          (zero-v (q2266397-v-zero real vector-space)))
      (and
       (q2266397-r-member-p real scale)
       (q2266397-r-less real (q2266397-r-zero real) scale)
       (not (equal left-vector zero-v))
       (not (equal right-vector zero-v))
       (equal
        left-vector
        (q2266397-v-smul
         real vector-space
         (q2266397-r-neg real scale)
         right-vector))))))

;; Equality of products of squared distances is equivalent to equality of
;; the source products of distances because all distances are nonnegative.
(defun-sk
    thousand-theorems-q2266397-intersecting-chords-theorem-statement
    (real vector-space point-space)
  (forall (a b c d p)
    (implies
     (and
      (q2266397-context-p real vector-space point-space)
      (q2266397-p-member-p point-space a)
      (q2266397-p-member-p point-space b)
      (q2266397-p-member-p point-space c)
      (q2266397-p-member-p point-space d)
      (q2266397-p-member-p point-space p)
      (q2266397-cospherical-four-p
       real vector-space point-space a b c d)
      (q2266397-angle-pi-p
       real vector-space point-space a p b)
      (q2266397-angle-pi-p
       real vector-space point-space c p d))
     (equal
      (q2266397-r-mul
       real
       (q2266397-squared-distance
        real vector-space point-space a p)
       (q2266397-squared-distance
        real vector-space point-space b p))
      (q2266397-r-mul
       real
       (q2266397-squared-distance
        real vector-space point-space c p)
       (q2266397-squared-distance
        real vector-space point-space d p))))))

(value-triple :itpeval-statement-checked)
:q
