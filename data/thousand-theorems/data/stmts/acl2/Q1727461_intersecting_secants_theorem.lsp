;; Statement-only formalization of thousand-theorems corpus artifact Q1727461,
;; "Intersecting secants theorem": cospherical endpoint pairs lying on two
;; same-direction secants through a point have equal products of distances in
;; an arbitrary real inner-product affine space. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative symbols present arbitrary real-scalar, vector, and affine
;; point carriers. All typing and structural laws used below are explicit;
;; no carrier is enumerated or restricted to ACL2's rational numbers.

(defstub q1727461-r-member-p (real x) t)
(defstub q1727461-v-member-p (vector-space x) t)
(defstub q1727461-p-member-p (point-space x) t)

(defstub q1727461-r-zero (real) t)
(defstub q1727461-r-one (real) t)
(defstub q1727461-r-add (real x y) t)
(defstub q1727461-r-mul (real x y) t)
(defstub q1727461-r-neg (real x) t)
(defstub q1727461-r-inv (real x) t)
(defstub q1727461-r-less (real x y) t)
(defstub q1727461-r-set-member-p (real set x) t)

(defstub q1727461-v-zero (real vector-space) t)
(defstub q1727461-v-add (real vector-space x y) t)
(defstub q1727461-v-neg (real vector-space x) t)
(defstub q1727461-v-smul (real vector-space scalar vector) t)
(defstub q1727461-inner (real vector-space x y) t)

(defstub q1727461-vadd
  (real vector-space point-space vector point)
  t)
(defstub q1727461-vsub
  (real vector-space point-space left-point right-point)
  t)

(defun q1727461-r-leq (real x y)
  (not (q1727461-r-less real y x)))

(defun-sk q1727461-real-field-laws-p (real)
  (forall (x y z)
    (implies
     (and (q1727461-r-member-p real x)
          (q1727461-r-member-p real y)
          (q1727461-r-member-p real z))
     (let ((zero (q1727461-r-zero real))
           (one (q1727461-r-one real)))
       (and
        (q1727461-r-member-p real (q1727461-r-add real x y))
        (q1727461-r-member-p real (q1727461-r-mul real x y))
        (q1727461-r-member-p real (q1727461-r-neg real x))
        (q1727461-r-member-p real (q1727461-r-inv real x))
        (equal (q1727461-r-add real x y)
               (q1727461-r-add real y x))
        (equal (q1727461-r-add real (q1727461-r-add real x y) z)
               (q1727461-r-add real x (q1727461-r-add real y z)))
        (equal (q1727461-r-add real x zero) x)
        (equal (q1727461-r-add real x (q1727461-r-neg real x))
               zero)
        (equal (q1727461-r-mul real x y)
               (q1727461-r-mul real y x))
        (equal (q1727461-r-mul real (q1727461-r-mul real x y) z)
               (q1727461-r-mul real x (q1727461-r-mul real y z)))
        (equal (q1727461-r-mul real x one) x)
        (equal (q1727461-r-mul real x zero) zero)
        (equal
         (q1727461-r-mul real x (q1727461-r-add real y z))
         (q1727461-r-add
          real
          (q1727461-r-mul real x y)
          (q1727461-r-mul real x z)))
        (implies
         (not (equal x zero))
         (equal (q1727461-r-mul real x (q1727461-r-inv real x))
                one))
        (not (q1727461-r-less real x x))
        (or (equal x y)
            (q1727461-r-less real x y)
            (q1727461-r-less real y x))
        (implies
         (and (q1727461-r-less real x y)
              (q1727461-r-less real y z))
         (q1727461-r-less real x z))
        (implies
         (q1727461-r-less real x y)
         (q1727461-r-less
          real
          (q1727461-r-add real x z)
          (q1727461-r-add real y z)))
        (implies
         (and (q1727461-r-less real zero x)
              (q1727461-r-less real zero y))
         (q1727461-r-less
          real zero (q1727461-r-mul real x y))))))))

(defun-sk q1727461-r-set-nonempty-p (real set)
  (exists (x)
    (and (q1727461-r-member-p real x)
         (q1727461-r-set-member-p real set x))))

(defun-sk q1727461-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and (q1727461-r-member-p real x)
          (q1727461-r-set-member-p real set x))
     (q1727461-r-leq real x bound))))

(defun-sk q1727461-r-bounded-above-p (real set)
  (exists (bound)
    (and (q1727461-r-member-p real bound)
         (q1727461-r-upper-bound-p real set bound))))

(defun-sk q1727461-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q1727461-r-member-p real supremum)
     (q1727461-r-upper-bound-p real set supremum)
     (implies
      (and (q1727461-r-member-p real bound)
           (q1727461-r-upper-bound-p real set bound))
      (q1727461-r-leq real supremum bound)))))

(defun-sk q1727461-r-supremum-exists-p (real set)
  (exists (supremum)
    (q1727461-r-supremum-p real set supremum)))

(defun-sk q1727461-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and (q1727461-r-set-nonempty-p real set)
          (q1727461-r-bounded-above-p real set))
     (q1727461-r-supremum-exists-p real set))))

(defun q1727461-real-p (real)
  (let ((zero (q1727461-r-zero real))
        (one (q1727461-r-one real)))
    (and
     (q1727461-r-member-p real zero)
     (q1727461-r-member-p real one)
     (not (equal zero one))
     (q1727461-r-less real zero one)
     (q1727461-real-field-laws-p real)
     (q1727461-r-dedekind-complete-p real))))

(defun-sk q1727461-vector-space-laws-p (real vector-space)
  (forall (a b u v w)
    (implies
     (and (q1727461-r-member-p real a)
          (q1727461-r-member-p real b)
          (q1727461-v-member-p vector-space u)
          (q1727461-v-member-p vector-space v)
          (q1727461-v-member-p vector-space w))
     (let ((zero-v (q1727461-v-zero real vector-space))
           (one (q1727461-r-one real)))
       (and
        (q1727461-v-member-p
         vector-space (q1727461-v-add real vector-space u v))
        (q1727461-v-member-p
         vector-space (q1727461-v-neg real vector-space u))
        (q1727461-v-member-p
         vector-space (q1727461-v-smul real vector-space a u))
        (equal (q1727461-v-add real vector-space u v)
               (q1727461-v-add real vector-space v u))
        (equal
         (q1727461-v-add
          real vector-space
          (q1727461-v-add real vector-space u v)
          w)
         (q1727461-v-add
          real vector-space
          u
          (q1727461-v-add real vector-space v w)))
        (equal (q1727461-v-add real vector-space u zero-v) u)
        (equal
         (q1727461-v-add
          real vector-space u (q1727461-v-neg real vector-space u))
         zero-v)
        (equal
         (q1727461-v-smul
          real vector-space a
          (q1727461-v-add real vector-space u v))
         (q1727461-v-add
          real vector-space
          (q1727461-v-smul real vector-space a u)
          (q1727461-v-smul real vector-space a v)))
        (equal
         (q1727461-v-smul
          real vector-space (q1727461-r-add real a b) u)
         (q1727461-v-add
          real vector-space
          (q1727461-v-smul real vector-space a u)
          (q1727461-v-smul real vector-space b u)))
        (equal
         (q1727461-v-smul
          real vector-space (q1727461-r-mul real a b) u)
         (q1727461-v-smul
          real vector-space
          a
          (q1727461-v-smul real vector-space b u)))
        (equal (q1727461-v-smul real vector-space one u) u))))))

(defun-sk q1727461-inner-product-laws-p (real vector-space)
  (forall (a u v w)
    (implies
     (and (q1727461-r-member-p real a)
          (q1727461-v-member-p vector-space u)
          (q1727461-v-member-p vector-space v)
          (q1727461-v-member-p vector-space w))
     (let ((zero-r (q1727461-r-zero real))
           (zero-v (q1727461-v-zero real vector-space)))
       (and
        (q1727461-r-member-p
         real (q1727461-inner real vector-space u v))
        (equal (q1727461-inner real vector-space u v)
               (q1727461-inner real vector-space v u))
        (equal
         (q1727461-inner
          real vector-space
          (q1727461-v-add real vector-space u v)
          w)
         (q1727461-r-add
          real
          (q1727461-inner real vector-space u w)
          (q1727461-inner real vector-space v w)))
        (equal
         (q1727461-inner
          real vector-space
          (q1727461-v-smul real vector-space a u)
          v)
         (q1727461-r-mul
          real a (q1727461-inner real vector-space u v)))
        (q1727461-r-leq
         real zero-r (q1727461-inner real vector-space u u))
        (equal
         (equal (q1727461-inner real vector-space u u) zero-r)
         (equal u zero-v)))))))

(defun-sk q1727461-point-space-nonempty-p (point-space)
  (exists (point)
    (q1727461-p-member-p point-space point)))

(defun-sk q1727461-affine-torsor-laws-p
    (real vector-space point-space)
  (forall (u v p q r)
    (implies
     (and (q1727461-v-member-p vector-space u)
          (q1727461-v-member-p vector-space v)
          (q1727461-p-member-p point-space p)
          (q1727461-p-member-p point-space q)
          (q1727461-p-member-p point-space r))
     (let ((zero-v (q1727461-v-zero real vector-space)))
       (and
        (q1727461-p-member-p
         point-space
         (q1727461-vadd real vector-space point-space u p))
        (q1727461-v-member-p
         vector-space
         (q1727461-vsub real vector-space point-space p q))
        (equal
         (q1727461-vadd real vector-space point-space zero-v p)
         p)
        (equal
         (q1727461-vadd
          real vector-space point-space
          (q1727461-v-add real vector-space u v)
          p)
         (q1727461-vadd
          real vector-space point-space u
          (q1727461-vadd real vector-space point-space v p)))
        (equal
         (q1727461-vadd
          real vector-space point-space
          (q1727461-vsub real vector-space point-space p q)
          q)
         p)
        (equal
         (q1727461-vsub
          real vector-space point-space
          (q1727461-vadd real vector-space point-space u p)
          p)
         u)
        (equal
         (q1727461-vsub real vector-space point-space p r)
         (q1727461-v-add
          real vector-space
          (q1727461-vsub real vector-space point-space p q)
          (q1727461-vsub real vector-space point-space q r))))))))

(defun q1727461-context-p (real vector-space point-space)
  (and
   (q1727461-real-p real)
   (q1727461-v-member-p
    vector-space (q1727461-v-zero real vector-space))
   (q1727461-vector-space-laws-p real vector-space)
   (q1727461-inner-product-laws-p real vector-space)
   (q1727461-point-space-nonempty-p point-space)
   (q1727461-affine-torsor-laws-p real vector-space point-space)))

(defun q1727461-squared-distance
    (real vector-space point-space left right)
  (let ((displacement
         (q1727461-vsub
          real vector-space point-space left right)))
    (q1727461-inner
     real vector-space displacement displacement)))

;; For a nonempty four-point set, a common center with equal squared
;; distances is equivalent to Mathlib's Cospherical predicate.
(defun-sk q1727461-cospherical-four-p
    (real vector-space point-space a b c d)
  (exists (center)
    (and
     (q1727461-p-member-p point-space center)
     (equal
      (q1727461-squared-distance
       real vector-space point-space a center)
      (q1727461-squared-distance
       real vector-space point-space b center))
     (equal
      (q1727461-squared-distance
       real vector-space point-space a center)
      (q1727461-squared-distance
       real vector-space point-space c center))
     (equal
      (q1727461-squared-distance
       real vector-space point-space a center)
      (q1727461-squared-distance
       real vector-space point-space d center)))))

;; With distinct endpoints, Mathlib's unoriented angle at p is zero exactly
;; when both displacement vectors are nonzero positive scalar multiples.
(defun-sk q1727461-angle-zero-p
    (real vector-space point-space left vertex right)
  (exists (scale)
    (let ((left-vector
           (q1727461-vsub
            real vector-space point-space left vertex))
          (right-vector
           (q1727461-vsub
            real vector-space point-space right vertex))
          (zero-v (q1727461-v-zero real vector-space)))
      (and
       (q1727461-r-member-p real scale)
       (q1727461-r-less real (q1727461-r-zero real) scale)
       (not (equal left-vector zero-v))
       (not (equal right-vector zero-v))
       (equal
        left-vector
        (q1727461-v-smul
         real vector-space scale right-vector))))))

;; Equality of products of squared distances is equivalent to equality of
;; the source products of distances because all distances are nonnegative.
(defun-sk
    thousand-theorems-q1727461-intersecting-secants-theorem-statement
    (real vector-space point-space)
  (forall (a b c d p)
    (implies
     (and
      (q1727461-context-p real vector-space point-space)
      (q1727461-p-member-p point-space a)
      (q1727461-p-member-p point-space b)
      (q1727461-p-member-p point-space c)
      (q1727461-p-member-p point-space d)
      (q1727461-p-member-p point-space p)
      (q1727461-cospherical-four-p
       real vector-space point-space a b c d)
      (not (equal a b))
      (not (equal c d))
      (q1727461-angle-zero-p
       real vector-space point-space a p b)
      (q1727461-angle-zero-p
       real vector-space point-space c p d))
     (equal
      (q1727461-r-mul
       real
       (q1727461-squared-distance
        real vector-space point-space a p)
       (q1727461-squared-distance
        real vector-space point-space b p))
      (q1727461-r-mul
       real
       (q1727461-squared-distance
        real vector-space point-space c p)
       (q1727461-squared-distance
        real vector-space point-space d p))))))

(value-triple :itpeval-statement-checked)
:q
