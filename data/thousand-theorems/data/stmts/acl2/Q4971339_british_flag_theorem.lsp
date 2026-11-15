;; Statement-only formalization of thousand-theorems corpus artifact Q4971339,
;; "British flag theorem": in an arbitrary real inner-product affine space,
;; a parallelogram with a right angle has equal sums of squared distances from
;; any point to its two pairs of opposite vertices. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative symbols present the source's real scalar field, arbitrary
;; real inner-product vector space, and arbitrary affine torsor. All carrier
;; restrictions and structural laws are explicit; no carrier is finite-coded
;; or restricted to ACL2's rational numbers.

(defstub q4971339-r-member-p (real x) t)
(defstub q4971339-r-set-member-p (real set x) t)
(defstub q4971339-v-member-p (vector-space x) t)
(defstub q4971339-p-member-p (point-space x) t)

(defstub q4971339-r-zero (real) t)
(defstub q4971339-r-one (real) t)
(defstub q4971339-r-add (real x y) t)
(defstub q4971339-r-mul (real x y) t)
(defstub q4971339-r-neg (real x) t)
(defstub q4971339-r-inv (real x) t)
(defstub q4971339-r-less (real x y) t)

(defstub q4971339-v-zero (real vector-space) t)
(defstub q4971339-v-add (real vector-space x y) t)
(defstub q4971339-v-neg (real vector-space x) t)
(defstub q4971339-v-smul (real vector-space scalar vector) t)
(defstub q4971339-inner (real vector-space x y) t)

(defstub q4971339-vadd
  (real vector-space point-space vector point)
  t)
(defstub q4971339-vsub
  (real vector-space point-space left-point right-point)
  t)

(defun q4971339-r-leq (real x y)
  (not (q4971339-r-less real y x)))

(defun-sk q4971339-real-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q4971339-r-member-p real x)
      (q4971339-r-member-p real y)
      (q4971339-r-member-p real z))
     (let ((zero (q4971339-r-zero real))
           (one (q4971339-r-one real)))
       (and
        (q4971339-r-member-p real (q4971339-r-add real x y))
        (q4971339-r-member-p real (q4971339-r-mul real x y))
        (q4971339-r-member-p real (q4971339-r-neg real x))
        (q4971339-r-member-p real (q4971339-r-inv real x))

        (equal
         (q4971339-r-add real (q4971339-r-add real x y) z)
         (q4971339-r-add real x (q4971339-r-add real y z)))
        (equal (q4971339-r-add real x y)
               (q4971339-r-add real y x))
        (equal (q4971339-r-add real x zero) x)
        (equal
         (q4971339-r-add real x (q4971339-r-neg real x))
         zero)

        (equal
         (q4971339-r-mul real (q4971339-r-mul real x y) z)
         (q4971339-r-mul real x (q4971339-r-mul real y z)))
        (equal (q4971339-r-mul real x y)
               (q4971339-r-mul real y x))
        (equal (q4971339-r-mul real x one) x)
        (equal (q4971339-r-mul real x zero) zero)
        (equal
         (q4971339-r-mul real x (q4971339-r-add real y z))
         (q4971339-r-add
          real
          (q4971339-r-mul real x y)
          (q4971339-r-mul real x z)))
        (implies
         (not (equal x zero))
         (equal
          (q4971339-r-mul real x (q4971339-r-inv real x))
          one))

        (not (q4971339-r-less real x x))
        (or (equal x y)
            (q4971339-r-less real x y)
            (q4971339-r-less real y x))
        (implies
         (and
          (q4971339-r-less real x y)
          (q4971339-r-less real y z))
         (q4971339-r-less real x z))
        (implies
         (q4971339-r-less real x y)
         (q4971339-r-less
          real
          (q4971339-r-add real x z)
          (q4971339-r-add real y z)))
        (implies
         (and
          (q4971339-r-less real zero x)
          (q4971339-r-less real zero y))
         (q4971339-r-less
          real zero (q4971339-r-mul real x y))))))))

(defun-sk q4971339-r-set-valid-p (real set)
  (forall (x)
    (implies
     (q4971339-r-set-member-p real set x)
     (q4971339-r-member-p real x))))

(defun-sk q4971339-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q4971339-r-member-p real x)
     (q4971339-r-set-member-p real set x))))

(defun-sk q4971339-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q4971339-r-member-p real x)
      (q4971339-r-set-member-p real set x))
     (q4971339-r-leq real x bound))))

(defun-sk q4971339-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q4971339-r-member-p real bound)
     (q4971339-r-upper-bound-p real set bound))))

(defun-sk q4971339-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q4971339-r-member-p real supremum)
     (q4971339-r-upper-bound-p real set supremum)
     (implies
      (and
       (q4971339-r-member-p real bound)
       (q4971339-r-upper-bound-p real set bound))
      (q4971339-r-leq real supremum bound)))))

(defun-sk q4971339-r-supremum-exists-p (real set)
  (exists (supremum)
    (q4971339-r-supremum-p real set supremum)))

(defun-sk q4971339-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q4971339-r-set-valid-p real set)
      (q4971339-r-set-nonempty-p real set)
      (q4971339-r-bounded-above-p real set))
     (q4971339-r-supremum-exists-p real set))))

(defun q4971339-real-p (real)
  (let ((zero (q4971339-r-zero real))
        (one (q4971339-r-one real)))
    (and
     (q4971339-r-member-p real zero)
     (q4971339-r-member-p real one)
     (not (equal zero one))
     (q4971339-r-less real zero one)
     (q4971339-real-field-laws-p real)
     (q4971339-r-dedekind-complete-p real))))

(defun-sk q4971339-vector-space-laws-p (real vector-space)
  (forall (a b u v w)
    (implies
     (and
      (q4971339-r-member-p real a)
      (q4971339-r-member-p real b)
      (q4971339-v-member-p vector-space u)
      (q4971339-v-member-p vector-space v)
      (q4971339-v-member-p vector-space w))
     (let ((zero-v (q4971339-v-zero real vector-space))
           (one-r (q4971339-r-one real)))
       (and
        (q4971339-v-member-p
         vector-space (q4971339-v-add real vector-space u v))
        (q4971339-v-member-p
         vector-space (q4971339-v-neg real vector-space u))
        (q4971339-v-member-p
         vector-space (q4971339-v-smul real vector-space a u))

        (equal
         (q4971339-v-add
          real vector-space
          (q4971339-v-add real vector-space u v)
          w)
         (q4971339-v-add
          real vector-space
          u
          (q4971339-v-add real vector-space v w)))
        (equal
         (q4971339-v-add real vector-space u v)
         (q4971339-v-add real vector-space v u))
        (equal
         (q4971339-v-add real vector-space u zero-v)
         u)
        (equal
         (q4971339-v-add
          real vector-space u
          (q4971339-v-neg real vector-space u))
         zero-v)

        (equal
         (q4971339-v-smul real vector-space one-r u)
         u)
        (equal
         (q4971339-v-smul
          real vector-space
          (q4971339-r-mul real a b)
          u)
         (q4971339-v-smul
          real vector-space
          a
          (q4971339-v-smul real vector-space b u)))
        (equal
         (q4971339-v-smul
          real vector-space
          (q4971339-r-add real a b)
          u)
         (q4971339-v-add
          real vector-space
          (q4971339-v-smul real vector-space a u)
          (q4971339-v-smul real vector-space b u)))
        (equal
         (q4971339-v-smul
          real vector-space
          a
          (q4971339-v-add real vector-space u v))
         (q4971339-v-add
          real vector-space
          (q4971339-v-smul real vector-space a u)
          (q4971339-v-smul real vector-space a v))))))))

(defun-sk q4971339-inner-product-laws-p (real vector-space)
  (forall (a u v w)
    (implies
     (and
      (q4971339-r-member-p real a)
      (q4971339-v-member-p vector-space u)
      (q4971339-v-member-p vector-space v)
      (q4971339-v-member-p vector-space w))
     (let ((zero-r (q4971339-r-zero real))
           (zero-v (q4971339-v-zero real vector-space)))
       (and
        (q4971339-r-member-p
         real (q4971339-inner real vector-space u v))
        (equal
         (q4971339-inner
          real vector-space
          (q4971339-v-add real vector-space u v)
          w)
         (q4971339-r-add
          real
          (q4971339-inner real vector-space u w)
          (q4971339-inner real vector-space v w)))
        (equal
         (q4971339-inner
          real vector-space
          (q4971339-v-smul real vector-space a u)
          v)
         (q4971339-r-mul
          real a (q4971339-inner real vector-space u v)))
        (equal
         (q4971339-inner real vector-space u v)
         (q4971339-inner real vector-space v u))
        (q4971339-r-leq
         real zero-r (q4971339-inner real vector-space u u))
        (iff
         (equal
          (q4971339-inner real vector-space u u)
          zero-r)
         (equal u zero-v)))))))

(defun-sk q4971339-point-space-nonempty-p (point-space)
  (exists (point)
    (q4971339-p-member-p point-space point)))

(defun-sk q4971339-affine-torsor-laws-p
    (real vector-space point-space)
  (forall (u v p q r)
    (implies
     (and
      (q4971339-v-member-p vector-space u)
      (q4971339-v-member-p vector-space v)
      (q4971339-p-member-p point-space p)
      (q4971339-p-member-p point-space q)
      (q4971339-p-member-p point-space r))
     (let ((zero-v (q4971339-v-zero real vector-space)))
       (and
        (q4971339-p-member-p
         point-space
         (q4971339-vadd real vector-space point-space u p))
        (q4971339-v-member-p
         vector-space
         (q4971339-vsub real vector-space point-space p q))
        (equal
         (q4971339-vadd
          real vector-space point-space zero-v p)
         p)
        (equal
         (q4971339-vadd
          real vector-space point-space
          (q4971339-v-add real vector-space u v)
          p)
         (q4971339-vadd
          real vector-space point-space u
          (q4971339-vadd
           real vector-space point-space v p)))
        (equal
         (q4971339-vadd
          real vector-space point-space
          (q4971339-vsub
           real vector-space point-space p q)
          q)
         p)
        (equal
         (q4971339-vsub
          real vector-space point-space
          (q4971339-vadd
           real vector-space point-space u p)
          p)
         u)
        (equal
         (q4971339-vsub real vector-space point-space p r)
         (q4971339-v-add
          real vector-space
          (q4971339-vsub
           real vector-space point-space p q)
          (q4971339-vsub
           real vector-space point-space q r))))))))

(defun q4971339-context-p (real vector-space point-space)
  (and
   (q4971339-real-p real)
   (q4971339-v-member-p
    vector-space (q4971339-v-zero real vector-space))
   (q4971339-vector-space-laws-p real vector-space)
   (q4971339-inner-product-laws-p real vector-space)
   (q4971339-point-space-nonempty-p point-space)
   (q4971339-affine-torsor-laws-p
    real vector-space point-space)))

(defun q4971339-distance-squared
    (real vector-space point-space p q)
  (let ((difference
         (q4971339-vsub
          real vector-space point-space p q)))
    (q4971339-inner
     real vector-space difference difference)))

;; Mathlib's unoriented angle is pi/2 exactly when the two displacement
;; vectors have zero inner product, including its degenerate-ray convention.
(defun q4971339-right-angle-p
    (real vector-space point-space first vertex third)
  (equal
   (q4971339-inner
    real vector-space
    (q4971339-vsub
     real vector-space point-space first vertex)
    (q4971339-vsub
     real vector-space point-space third vertex))
   (q4971339-r-zero real)))

;; Over a real affine torsor, midpoint(a,c)=midpoint(b,d) is equivalent in
;; both directions to c-a=(b-a)+(d-a). This displacement form avoids adding a
;; derived midpoint operation while retaining possible degeneracies.
(defun q4971339-common-midpoint-p
    (real vector-space point-space a b c d)
  (equal
   (q4971339-vsub
    real vector-space point-space c a)
   (q4971339-v-add
    real vector-space
    (q4971339-vsub
     real vector-space point-space b a)
    (q4971339-vsub
     real vector-space point-space d a))))

(defun q4971339-british-flag-identity-p
    (real vector-space point-space a b c d p)
  (equal
   (q4971339-r-add
    real
    (q4971339-distance-squared
     real vector-space point-space p a)
    (q4971339-distance-squared
     real vector-space point-space p c))
   (q4971339-r-add
    real
    (q4971339-distance-squared
     real vector-space point-space p b)
    (q4971339-distance-squared
     real vector-space point-space p d))))

(defun-sk thousand-theorems-q4971339-british-flag-theorem-statement
    (real vector-space point-space)
  (forall (a b c d p)
    (implies
     (and
      (q4971339-context-p real vector-space point-space)
      (q4971339-p-member-p point-space a)
      (q4971339-p-member-p point-space b)
      (q4971339-p-member-p point-space c)
      (q4971339-p-member-p point-space d)
      (q4971339-p-member-p point-space p)
      (q4971339-common-midpoint-p
       real vector-space point-space a b c d)
      (q4971339-right-angle-p
       real vector-space point-space b a d))
     (q4971339-british-flag-identity-p
      real vector-space point-space a b c d p))))

(value-triple :itpeval-statement-checked)
:q
