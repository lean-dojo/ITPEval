;; Statement-only formalization of thousand-theorems corpus artifact Q877489,
;; "Apollonius's theorem": in an arbitrary real inner-product affine space,
;; the sum of the squared distances from a point to two endpoints equals twice
;; the sum of its squared distance to their midpoint and the squared half-length
;; of the segment. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative symbols present the source's real scalar field, arbitrary
;; real inner-product vector space, and arbitrary affine torsor. All carrier
;; restrictions and structural laws are explicit; no carrier is finite-coded
;; or restricted to ACL2's rational numbers.

(defstub q877489-r-member-p (real x) t)
(defstub q877489-r-set-member-p (real set x) t)
(defstub q877489-v-member-p (vector-space x) t)
(defstub q877489-p-member-p (point-space x) t)

(defstub q877489-r-zero (real) t)
(defstub q877489-r-one (real) t)
(defstub q877489-r-add (real x y) t)
(defstub q877489-r-mul (real x y) t)
(defstub q877489-r-neg (real x) t)
(defstub q877489-r-inv (real x) t)
(defstub q877489-r-less (real x y) t)

(defstub q877489-v-zero (real vector-space) t)
(defstub q877489-v-add (real vector-space x y) t)
(defstub q877489-v-neg (real vector-space x) t)
(defstub q877489-v-smul (real vector-space scalar vector) t)
(defstub q877489-inner (real vector-space x y) t)

(defstub q877489-vadd
  (real vector-space point-space vector point)
  t)
(defstub q877489-vsub
  (real vector-space point-space left-point right-point)
  t)

(defun q877489-r-leq (real x y)
  (not (q877489-r-less real y x)))

(defun-sk q877489-real-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q877489-r-member-p real x)
      (q877489-r-member-p real y)
      (q877489-r-member-p real z))
     (let ((zero (q877489-r-zero real))
           (one (q877489-r-one real)))
       (and
        (q877489-r-member-p real (q877489-r-add real x y))
        (q877489-r-member-p real (q877489-r-mul real x y))
        (q877489-r-member-p real (q877489-r-neg real x))
        (q877489-r-member-p real (q877489-r-inv real x))

        (equal
         (q877489-r-add real (q877489-r-add real x y) z)
         (q877489-r-add real x (q877489-r-add real y z)))
        (equal (q877489-r-add real x y)
               (q877489-r-add real y x))
        (equal (q877489-r-add real x zero) x)
        (equal
         (q877489-r-add real x (q877489-r-neg real x))
         zero)

        (equal
         (q877489-r-mul real (q877489-r-mul real x y) z)
         (q877489-r-mul real x (q877489-r-mul real y z)))
        (equal (q877489-r-mul real x y)
               (q877489-r-mul real y x))
        (equal (q877489-r-mul real x one) x)
        (equal (q877489-r-mul real x zero) zero)
        (equal
         (q877489-r-mul real x (q877489-r-add real y z))
         (q877489-r-add
          real
          (q877489-r-mul real x y)
          (q877489-r-mul real x z)))
        (implies
         (not (equal x zero))
         (equal
          (q877489-r-mul real x (q877489-r-inv real x))
          one))

        (not (q877489-r-less real x x))
        (or (equal x y)
            (q877489-r-less real x y)
            (q877489-r-less real y x))
        (implies
         (and
          (q877489-r-less real x y)
          (q877489-r-less real y z))
         (q877489-r-less real x z))
        (implies
         (q877489-r-less real x y)
         (q877489-r-less
          real
          (q877489-r-add real x z)
          (q877489-r-add real y z)))
        (implies
         (and
          (q877489-r-less real zero x)
          (q877489-r-less real zero y))
         (q877489-r-less
          real zero (q877489-r-mul real x y))))))))

(defun-sk q877489-r-set-valid-p (real set)
  (forall (x)
    (implies
     (q877489-r-set-member-p real set x)
     (q877489-r-member-p real x))))

(defun-sk q877489-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q877489-r-member-p real x)
     (q877489-r-set-member-p real set x))))

(defun-sk q877489-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q877489-r-member-p real x)
      (q877489-r-set-member-p real set x))
     (q877489-r-leq real x bound))))

(defun-sk q877489-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q877489-r-member-p real bound)
     (q877489-r-upper-bound-p real set bound))))

(defun-sk q877489-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q877489-r-member-p real supremum)
     (q877489-r-upper-bound-p real set supremum)
     (implies
      (and
       (q877489-r-member-p real bound)
       (q877489-r-upper-bound-p real set bound))
      (q877489-r-leq real supremum bound)))))

(defun-sk q877489-r-supremum-exists-p (real set)
  (exists (supremum)
    (q877489-r-supremum-p real set supremum)))

(defun-sk q877489-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q877489-r-set-valid-p real set)
      (q877489-r-set-nonempty-p real set)
      (q877489-r-bounded-above-p real set))
     (q877489-r-supremum-exists-p real set))))

(defun q877489-real-p (real)
  (let ((zero (q877489-r-zero real))
        (one (q877489-r-one real)))
    (and
     (q877489-r-member-p real zero)
     (q877489-r-member-p real one)
     (not (equal zero one))
     (q877489-r-less real zero one)
     (q877489-real-field-laws-p real)
     (q877489-r-dedekind-complete-p real))))

(defun-sk q877489-vector-space-laws-p (real vector-space)
  (forall (a b u v w)
    (implies
     (and
      (q877489-r-member-p real a)
      (q877489-r-member-p real b)
      (q877489-v-member-p vector-space u)
      (q877489-v-member-p vector-space v)
      (q877489-v-member-p vector-space w))
     (let ((zero-v (q877489-v-zero real vector-space))
           (one-r (q877489-r-one real)))
       (and
        (q877489-v-member-p
         vector-space (q877489-v-add real vector-space u v))
        (q877489-v-member-p
         vector-space (q877489-v-neg real vector-space u))
        (q877489-v-member-p
         vector-space (q877489-v-smul real vector-space a u))

        (equal
         (q877489-v-add
          real vector-space
          (q877489-v-add real vector-space u v)
          w)
         (q877489-v-add
          real vector-space
          u
          (q877489-v-add real vector-space v w)))
        (equal
         (q877489-v-add real vector-space u v)
         (q877489-v-add real vector-space v u))
        (equal
         (q877489-v-add real vector-space u zero-v)
         u)
        (equal
         (q877489-v-add
          real vector-space u
          (q877489-v-neg real vector-space u))
         zero-v)

        (equal
         (q877489-v-smul real vector-space one-r u)
         u)
        (equal
         (q877489-v-smul
          real vector-space
          (q877489-r-mul real a b)
          u)
         (q877489-v-smul
          real vector-space
          a
          (q877489-v-smul real vector-space b u)))
        (equal
         (q877489-v-smul
          real vector-space
          (q877489-r-add real a b)
          u)
         (q877489-v-add
          real vector-space
          (q877489-v-smul real vector-space a u)
          (q877489-v-smul real vector-space b u)))
        (equal
         (q877489-v-smul
          real vector-space
          a
          (q877489-v-add real vector-space u v))
         (q877489-v-add
          real vector-space
          (q877489-v-smul real vector-space a u)
          (q877489-v-smul real vector-space a v))))))))

(defun-sk q877489-inner-product-laws-p (real vector-space)
  (forall (a u v w)
    (implies
     (and
      (q877489-r-member-p real a)
      (q877489-v-member-p vector-space u)
      (q877489-v-member-p vector-space v)
      (q877489-v-member-p vector-space w))
     (let ((zero-r (q877489-r-zero real))
           (zero-v (q877489-v-zero real vector-space)))
       (and
        (q877489-r-member-p
         real (q877489-inner real vector-space u v))
        (equal
         (q877489-inner
          real vector-space
          (q877489-v-add real vector-space u v)
          w)
         (q877489-r-add
          real
          (q877489-inner real vector-space u w)
          (q877489-inner real vector-space v w)))
        (equal
         (q877489-inner
          real vector-space
          (q877489-v-smul real vector-space a u)
          v)
         (q877489-r-mul
          real a (q877489-inner real vector-space u v)))
        (equal
         (q877489-inner real vector-space u v)
         (q877489-inner real vector-space v u))
        (q877489-r-leq
         real zero-r (q877489-inner real vector-space u u))
        (iff
         (equal
          (q877489-inner real vector-space u u)
          zero-r)
         (equal u zero-v)))))))

(defun-sk q877489-point-space-nonempty-p (point-space)
  (exists (point)
    (q877489-p-member-p point-space point)))

(defun-sk q877489-affine-torsor-laws-p
    (real vector-space point-space)
  (forall (u v p q r)
    (implies
     (and
      (q877489-v-member-p vector-space u)
      (q877489-v-member-p vector-space v)
      (q877489-p-member-p point-space p)
      (q877489-p-member-p point-space q)
      (q877489-p-member-p point-space r))
     (let ((zero-v (q877489-v-zero real vector-space)))
       (and
        (q877489-p-member-p
         point-space
         (q877489-vadd real vector-space point-space u p))
        (q877489-v-member-p
         vector-space
         (q877489-vsub real vector-space point-space p q))
        (equal
         (q877489-vadd
          real vector-space point-space zero-v p)
         p)
        (equal
         (q877489-vadd
          real vector-space point-space
          (q877489-v-add real vector-space u v)
          p)
         (q877489-vadd
          real vector-space point-space u
          (q877489-vadd
           real vector-space point-space v p)))
        (equal
         (q877489-vadd
          real vector-space point-space
          (q877489-vsub
           real vector-space point-space p q)
          q)
         p)
        (equal
         (q877489-vsub
          real vector-space point-space
          (q877489-vadd
           real vector-space point-space u p)
          p)
         u)
        (equal
         (q877489-vsub real vector-space point-space p r)
         (q877489-v-add
          real vector-space
          (q877489-vsub
           real vector-space point-space p q)
          (q877489-vsub
           real vector-space point-space q r))))))))

(defun q877489-context-p (real vector-space point-space)
  (and
   (q877489-real-p real)
   (q877489-v-member-p
    vector-space (q877489-v-zero real vector-space))
   (q877489-vector-space-laws-p real vector-space)
   (q877489-inner-product-laws-p real vector-space)
   (q877489-point-space-nonempty-p point-space)
   (q877489-affine-torsor-laws-p
    real vector-space point-space)))

(defun q877489-distance-squared
    (real vector-space point-space p q)
  (let ((difference
         (q877489-vsub
          real vector-space point-space p q)))
    (q877489-inner
     real vector-space difference difference)))

(defun q877489-two (real)
  (q877489-r-add
   real
   (q877489-r-one real)
   (q877489-r-one real)))

(defun q877489-half (real)
  (q877489-r-inv real (q877489-two real)))

;; This is Mathlib's affine midpoint b + (1/2) • (c - b).
(defun q877489-midpoint
    (real vector-space point-space b c)
  (q877489-vadd
   real vector-space point-space
   (q877489-v-smul
    real vector-space
    (q877489-half real)
    (q877489-vsub
     real vector-space point-space c b))
   b))

;; Squared metric distances are inner products of displacement vectors.
;; Consequently (dist(b,c)/2)^2 is exactly (1/2)^2 times this value, so the
;; source's norm, distance, division, and square notation is only unfolded.
(defun q877489-half-distance-squared
    (real vector-space point-space b c)
  (q877489-r-mul
   real
   (q877489-r-mul
    real
    (q877489-half real)
    (q877489-half real))
   (q877489-distance-squared
    real vector-space point-space b c)))

(defun q877489-apollonius-identity-p
    (real vector-space point-space a b c)
  (equal
   (q877489-r-add
    real
    (q877489-distance-squared
     real vector-space point-space a b)
    (q877489-distance-squared
     real vector-space point-space a c))
   (q877489-r-mul
    real
    (q877489-two real)
    (q877489-r-add
     real
    (q877489-distance-squared
      real vector-space point-space
      a
      (q877489-midpoint
       real vector-space point-space b c))
     (q877489-half-distance-squared
      real vector-space point-space b c)))))

(defun-sk thousand-theorems-q877489-apollonius-s-theorem-statement
    (real vector-space point-space)
  (forall (a b c)
    (implies
     (and
      (q877489-context-p real vector-space point-space)
      (q877489-p-member-p point-space a)
      (q877489-p-member-p point-space b)
      (q877489-p-member-p point-space c))
     (q877489-apollonius-identity-p
      real vector-space point-space a b c))))

(value-triple :itpeval-statement-checked)
:q
