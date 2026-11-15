;; Statement-only formalization of thousand-theorems corpus artifact Q459547,
;; "Ptolemy's theorem": in an arbitrary real inner-product affine space, four
;; cospherical points whose diagonals form straight angles at a common point
;; satisfy Ptolemy's side-and-diagonal distance identity.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols present the source's real scalar field,
;; arbitrary real inner-product space, and arbitrary affine torsor. Every
;; carrier restriction and structural law is explicit in the statement.

(defstub q459547-r-member-p (real x) t)
(defstub q459547-r-set-member-p (real set x) t)
(defstub q459547-v-member-p (vector-space x) t)
(defstub q459547-p-member-p (point-space x) t)

(defstub q459547-r-zero (real) t)
(defstub q459547-r-one (real) t)
(defstub q459547-r-add (real x y) t)
(defstub q459547-r-mul (real x y) t)
(defstub q459547-r-neg (real x) t)
(defstub q459547-r-inv (real x) t)
(defstub q459547-r-less (real x y) t)

(defstub q459547-v-zero (real vector-space) t)
(defstub q459547-v-add (real vector-space x y) t)
(defstub q459547-v-neg (real vector-space x) t)
(defstub q459547-v-smul (real vector-space scalar vector) t)
(defstub q459547-inner (real vector-space x y) t)

(defstub q459547-vadd
  (real vector-space point-space vector point)
  t)
(defstub q459547-vsub
  (real vector-space point-space left-point right-point)
  t)

(defun q459547-r-leq (real x y)
  (not (q459547-r-less real y x)))

(defun q459547-r-sub (real x y)
  (q459547-r-add real x (q459547-r-neg real y)))

(defun q459547-r-two (real)
  (q459547-r-add
   real (q459547-r-one real) (q459547-r-one real)))

(defun q459547-r-four (real)
  (q459547-r-mul
   real (q459547-r-two real) (q459547-r-two real)))

(defun-sk q459547-real-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q459547-r-member-p real x)
      (q459547-r-member-p real y)
      (q459547-r-member-p real z))
     (let ((zero (q459547-r-zero real))
           (one (q459547-r-one real)))
       (and
        (q459547-r-member-p real (q459547-r-add real x y))
        (q459547-r-member-p real (q459547-r-mul real x y))
        (q459547-r-member-p real (q459547-r-neg real x))
        (q459547-r-member-p real (q459547-r-inv real x))

        (equal
         (q459547-r-add real (q459547-r-add real x y) z)
         (q459547-r-add real x (q459547-r-add real y z)))
        (equal (q459547-r-add real x y)
               (q459547-r-add real y x))
        (equal (q459547-r-add real x zero) x)
        (equal
         (q459547-r-add real x (q459547-r-neg real x))
         zero)

        (equal
         (q459547-r-mul real (q459547-r-mul real x y) z)
         (q459547-r-mul real x (q459547-r-mul real y z)))
        (equal (q459547-r-mul real x y)
               (q459547-r-mul real y x))
        (equal (q459547-r-mul real x one) x)
        (equal (q459547-r-mul real x zero) zero)
        (equal
         (q459547-r-mul real x (q459547-r-add real y z))
         (q459547-r-add
          real
          (q459547-r-mul real x y)
          (q459547-r-mul real x z)))
        (implies
         (not (equal x zero))
         (equal
          (q459547-r-mul real x (q459547-r-inv real x))
          one))

        (not (q459547-r-less real x x))
        (or (equal x y)
            (q459547-r-less real x y)
            (q459547-r-less real y x))
        (implies
         (and
          (q459547-r-less real x y)
          (q459547-r-less real y z))
         (q459547-r-less real x z))
        (implies
         (q459547-r-less real x y)
         (q459547-r-less
          real
          (q459547-r-add real x z)
          (q459547-r-add real y z)))
        (implies
         (and
          (q459547-r-less real zero x)
          (q459547-r-less real zero y))
         (q459547-r-less
          real zero (q459547-r-mul real x y))))))))

(defun-sk q459547-r-set-valid-p (real set)
  (forall (x)
    (implies
     (q459547-r-set-member-p real set x)
     (q459547-r-member-p real x))))

(defun-sk q459547-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q459547-r-member-p real x)
     (q459547-r-set-member-p real set x))))

(defun-sk q459547-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q459547-r-member-p real x)
      (q459547-r-set-member-p real set x))
     (q459547-r-leq real x bound))))

(defun-sk q459547-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q459547-r-member-p real bound)
     (q459547-r-upper-bound-p real set bound))))

(defun-sk q459547-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q459547-r-member-p real supremum)
     (q459547-r-upper-bound-p real set supremum)
     (implies
      (and
       (q459547-r-member-p real bound)
       (q459547-r-upper-bound-p real set bound))
      (q459547-r-leq real supremum bound)))))

(defun-sk q459547-r-supremum-exists-p (real set)
  (exists (supremum)
    (q459547-r-supremum-p real set supremum)))

(defun-sk q459547-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q459547-r-set-valid-p real set)
      (q459547-r-set-nonempty-p real set)
      (q459547-r-bounded-above-p real set))
     (q459547-r-supremum-exists-p real set))))

(defun q459547-real-p (real)
  (let ((zero (q459547-r-zero real))
        (one (q459547-r-one real)))
    (and
     (q459547-r-member-p real zero)
     (q459547-r-member-p real one)
     (not (equal zero one))
     (q459547-r-less real zero one)
     (q459547-real-field-laws-p real)
     (q459547-r-dedekind-complete-p real))))

(defun-sk q459547-vector-space-laws-p (real vector-space)
  (forall (a b u v w)
    (implies
     (and
      (q459547-r-member-p real a)
      (q459547-r-member-p real b)
      (q459547-v-member-p vector-space u)
      (q459547-v-member-p vector-space v)
      (q459547-v-member-p vector-space w))
     (let ((zero-v (q459547-v-zero real vector-space))
           (one-r (q459547-r-one real)))
       (and
        (q459547-v-member-p
         vector-space (q459547-v-add real vector-space u v))
        (q459547-v-member-p
         vector-space (q459547-v-neg real vector-space u))
        (q459547-v-member-p
         vector-space (q459547-v-smul real vector-space a u))

        (equal
         (q459547-v-add
          real vector-space
          (q459547-v-add real vector-space u v)
          w)
         (q459547-v-add
          real vector-space
          u
          (q459547-v-add real vector-space v w)))
        (equal
         (q459547-v-add real vector-space u v)
         (q459547-v-add real vector-space v u))
        (equal
         (q459547-v-add real vector-space u zero-v)
         u)
        (equal
         (q459547-v-add
          real vector-space u
          (q459547-v-neg real vector-space u))
         zero-v)

        (equal
         (q459547-v-smul real vector-space one-r u)
         u)
        (equal
         (q459547-v-smul
          real vector-space
          (q459547-r-mul real a b)
          u)
         (q459547-v-smul
          real vector-space
          a
          (q459547-v-smul real vector-space b u)))
        (equal
         (q459547-v-smul
          real vector-space
          (q459547-r-add real a b)
          u)
         (q459547-v-add
          real vector-space
          (q459547-v-smul real vector-space a u)
          (q459547-v-smul real vector-space b u)))
        (equal
         (q459547-v-smul
          real vector-space
          a
          (q459547-v-add real vector-space u v))
         (q459547-v-add
          real vector-space
          (q459547-v-smul real vector-space a u)
          (q459547-v-smul real vector-space a v))))))))

(defun-sk q459547-inner-product-laws-p (real vector-space)
  (forall (a u v w)
    (implies
     (and
      (q459547-r-member-p real a)
      (q459547-v-member-p vector-space u)
      (q459547-v-member-p vector-space v)
      (q459547-v-member-p vector-space w))
     (let ((zero-r (q459547-r-zero real))
           (zero-v (q459547-v-zero real vector-space)))
       (and
        (q459547-r-member-p
         real (q459547-inner real vector-space u v))
        (equal
         (q459547-inner
          real vector-space
          (q459547-v-add real vector-space u v)
          w)
         (q459547-r-add
          real
          (q459547-inner real vector-space u w)
          (q459547-inner real vector-space v w)))
        (equal
         (q459547-inner
          real vector-space
          (q459547-v-smul real vector-space a u)
          v)
         (q459547-r-mul
          real a (q459547-inner real vector-space u v)))
        (equal
         (q459547-inner real vector-space u v)
         (q459547-inner real vector-space v u))
        (q459547-r-leq
         real zero-r (q459547-inner real vector-space u u))
        (iff
         (equal
          (q459547-inner real vector-space u u)
          zero-r)
         (equal u zero-v)))))))

(defun-sk q459547-affine-torsor-laws-p
    (real vector-space point-space)
  (forall (p q r u v)
    (implies
     (and
      (q459547-p-member-p point-space p)
      (q459547-p-member-p point-space q)
      (q459547-p-member-p point-space r)
      (q459547-v-member-p vector-space u)
      (q459547-v-member-p vector-space v))
     (let ((zero-v (q459547-v-zero real vector-space)))
       (and
        (q459547-p-member-p
         point-space
         (q459547-vadd
          real vector-space point-space u p))
        (q459547-v-member-p
         vector-space
         (q459547-vsub
          real vector-space point-space p q))
        (equal
         (q459547-vadd
          real vector-space point-space zero-v p)
         p)
        (equal
         (q459547-vadd
          real vector-space point-space
          (q459547-v-add real vector-space u v)
          p)
         (q459547-vadd
          real vector-space point-space
          u
          (q459547-vadd
           real vector-space point-space v p)))
        (equal
         (q459547-vadd
          real vector-space point-space
          (q459547-vsub
           real vector-space point-space p q)
          q)
         p)
        (equal
         (q459547-vsub
          real vector-space point-space
          (q459547-vadd
           real vector-space point-space u p)
          p)
         u)
        (equal
         (q459547-vsub
          real vector-space point-space p r)
         (q459547-v-add
          real vector-space
          (q459547-vsub
           real vector-space point-space p q)
          (q459547-vsub
           real vector-space point-space q r))))))))

(defun q459547-context-p (real vector-space point-space)
  (and
   (q459547-real-p real)
   (q459547-v-member-p
    vector-space (q459547-v-zero real vector-space))
   (q459547-vector-space-laws-p real vector-space)
   (q459547-inner-product-laws-p real vector-space)
   (q459547-affine-torsor-laws-p
    real vector-space point-space)))

(defun q459547-distance-squared
    (real vector-space point-space p q)
  (let ((difference
         (q459547-vsub
          real vector-space point-space p q)))
    (q459547-inner
     real vector-space difference difference)))

;; Equal squared distances from an internally quantified center are equivalent
;; to membership of all four points in one metric sphere.
(defun q459547-cospherical-witness-p
    (real vector-space point-space center a b c d)
  (let ((sa
         (q459547-distance-squared
          real vector-space point-space a center)))
    (and
     (q459547-p-member-p point-space center)
     (equal
      sa
      (q459547-distance-squared
       real vector-space point-space b center))
     (equal
      sa
      (q459547-distance-squared
       real vector-space point-space c center))
     (equal
      sa
      (q459547-distance-squared
       real vector-space point-space d center)))))

(defun-sk q459547-cospherical-four-p
    (real vector-space point-space a b c d)
  (exists (center)
    (q459547-cospherical-witness-p
     real vector-space point-space center a b c d)))

;; For two displacement vectors in a real inner-product space, angle pi is
;; equivalent to a negative inner product attaining equality in Cauchy-Schwarz.
(defun q459547-straight-angle-p
    (real vector-space point-space first middle third)
  (let* ((left
          (q459547-vsub
           real vector-space point-space first middle))
         (right
          (q459547-vsub
           real vector-space point-space third middle))
         (dot (q459547-inner real vector-space left right))
         (left-square
          (q459547-inner real vector-space left left))
         (right-square
          (q459547-inner real vector-space right right)))
    (and
     (q459547-r-less real dot (q459547-r-zero real))
     (equal
      (q459547-r-mul real dot dot)
      (q459547-r-mul real left-square right-square)))))

;; If X is the product of the squared diagonal lengths and Y,Z are the
;; corresponding products for opposite sides, the source distance equality
;; sqrt(Y)+sqrt(Z)=sqrt(X) is equivalent to
;; X-Y-Z >= 0 and (X-Y-Z)^2 = 4*Y*Z.
(defun q459547-ptolemy-conclusion-p
    (real vector-space point-space a b c d)
  (let* ((s-ab
          (q459547-distance-squared
           real vector-space point-space a b))
         (s-bc
          (q459547-distance-squared
           real vector-space point-space b c))
         (s-cd
          (q459547-distance-squared
           real vector-space point-space c d))
         (s-da
          (q459547-distance-squared
           real vector-space point-space d a))
         (s-ac
          (q459547-distance-squared
           real vector-space point-space a c))
         (s-bd
          (q459547-distance-squared
           real vector-space point-space b d))
         (x (q459547-r-mul real s-ac s-bd))
         (y (q459547-r-mul real s-ab s-cd))
         (z (q459547-r-mul real s-bc s-da))
         (difference
          (q459547-r-sub
           real (q459547-r-sub real x y) z)))
    (and
     (q459547-r-leq
      real (q459547-r-zero real) difference)
     (equal
      (q459547-r-mul real difference difference)
      (q459547-r-mul
       real
       (q459547-r-four real)
       (q459547-r-mul real y z))))))

(defun-sk thousand-theorems-q459547-ptolemys-theorem-statement
    (real vector-space point-space)
  (forall (a b c d p)
    (implies
     (and
      (q459547-context-p real vector-space point-space)
      (q459547-p-member-p point-space a)
      (q459547-p-member-p point-space b)
      (q459547-p-member-p point-space c)
      (q459547-p-member-p point-space d)
      (q459547-p-member-p point-space p)
      (q459547-cospherical-four-p
       real vector-space point-space a b c d)
      (q459547-straight-angle-p
       real vector-space point-space a p c)
      (q459547-straight-angle-p
       real vector-space point-space b p d))
     (q459547-ptolemy-conclusion-p
      real vector-space point-space a b c d))))

(value-triple :itpeval-statement-checked)
:q
