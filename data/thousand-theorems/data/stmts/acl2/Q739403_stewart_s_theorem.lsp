;; Statement-only formalization of thousand-theorems corpus artifact Q739403,
;; "Stewart's theorem": four points in an arbitrary real inner-product affine
;; space satisfy Stewart's distance identity when the angle at the fourth
;; point between the second and third points is pi. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative symbols present arbitrary real-scalar, vector, and affine
;; point carriers. All typing and structural laws used by the source theorem
;; are explicit; no carrier is finite-coded or restricted to ACL2 rationals.

(defstub q739403-r-member-p (real x) t)
(defstub q739403-v-member-p (vector-space x) t)
(defstub q739403-p-member-p (point-space x) t)

(defstub q739403-r-zero (real) t)
(defstub q739403-r-one (real) t)
(defstub q739403-r-add (real x y) t)
(defstub q739403-r-mul (real x y) t)
(defstub q739403-r-neg (real x) t)
(defstub q739403-r-inv (real x) t)
(defstub q739403-r-less (real x y) t)
(defstub q739403-r-set-member-p (real set x) t)

(defstub q739403-v-zero (real vector-space) t)
(defstub q739403-v-add (real vector-space x y) t)
(defstub q739403-v-neg (real vector-space x) t)
(defstub q739403-v-smul (real vector-space scalar vector) t)
(defstub q739403-inner (real vector-space x y) t)
(defstub q739403-norm (real vector-space vector) t)

(defstub q739403-vadd
  (real vector-space point-space vector point)
  t)
(defstub q739403-vsub
  (real vector-space point-space left-point right-point)
  t)

(defun q739403-r-leq (real x y)
  (not (q739403-r-less real y x)))

(defun-sk q739403-real-field-laws-p (real)
  (forall (x y z)
    (implies
     (and (q739403-r-member-p real x)
          (q739403-r-member-p real y)
          (q739403-r-member-p real z))
     (let ((zero (q739403-r-zero real))
           (one (q739403-r-one real)))
       (and
        (q739403-r-member-p real (q739403-r-add real x y))
        (q739403-r-member-p real (q739403-r-mul real x y))
        (q739403-r-member-p real (q739403-r-neg real x))
        (q739403-r-member-p real (q739403-r-inv real x))
        (equal (q739403-r-add real x y)
               (q739403-r-add real y x))
        (equal
         (q739403-r-add real (q739403-r-add real x y) z)
         (q739403-r-add real x (q739403-r-add real y z)))
        (equal (q739403-r-add real x zero) x)
        (equal
         (q739403-r-add real x (q739403-r-neg real x))
         zero)
        (equal (q739403-r-mul real x y)
               (q739403-r-mul real y x))
        (equal
         (q739403-r-mul real (q739403-r-mul real x y) z)
         (q739403-r-mul real x (q739403-r-mul real y z)))
        (equal (q739403-r-mul real x one) x)
        (equal (q739403-r-mul real x zero) zero)
        (equal
         (q739403-r-mul real x (q739403-r-add real y z))
         (q739403-r-add
          real
          (q739403-r-mul real x y)
          (q739403-r-mul real x z)))
        (implies
         (not (equal x zero))
         (equal
          (q739403-r-mul real x (q739403-r-inv real x))
          one))
        (not (q739403-r-less real x x))
        (or (equal x y)
            (q739403-r-less real x y)
            (q739403-r-less real y x))
        (implies
         (and (q739403-r-less real x y)
              (q739403-r-less real y z))
         (q739403-r-less real x z))
        (implies
         (q739403-r-less real x y)
         (q739403-r-less
          real
          (q739403-r-add real x z)
          (q739403-r-add real y z)))
        (implies
         (and (q739403-r-less real zero x)
              (q739403-r-less real zero y))
         (q739403-r-less
          real zero (q739403-r-mul real x y))))))))

(defun-sk q739403-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q739403-r-member-p real x)
     (q739403-r-set-member-p real set x))))

(defun-sk q739403-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q739403-r-member-p real x)
      (q739403-r-set-member-p real set x))
     (q739403-r-leq real x bound))))

(defun-sk q739403-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q739403-r-member-p real bound)
     (q739403-r-upper-bound-p real set bound))))

(defun-sk q739403-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q739403-r-member-p real supremum)
     (q739403-r-upper-bound-p real set supremum)
     (implies
      (and
       (q739403-r-member-p real bound)
       (q739403-r-upper-bound-p real set bound))
      (q739403-r-leq real supremum bound)))))

(defun-sk q739403-r-supremum-exists-p (real set)
  (exists (supremum)
    (q739403-r-supremum-p real set supremum)))

(defun-sk q739403-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q739403-r-set-nonempty-p real set)
      (q739403-r-bounded-above-p real set))
     (q739403-r-supremum-exists-p real set))))

(defun q739403-real-p (real)
  (let ((zero (q739403-r-zero real))
        (one (q739403-r-one real)))
    (and
     (q739403-r-member-p real zero)
     (q739403-r-member-p real one)
     (not (equal zero one))
     (q739403-r-less real zero one)
     (q739403-real-field-laws-p real)
     (q739403-r-dedekind-complete-p real))))

(defun-sk q739403-vector-space-laws-p (real vector-space)
  (forall (a b u v w)
    (implies
     (and
      (q739403-r-member-p real a)
      (q739403-r-member-p real b)
      (q739403-v-member-p vector-space u)
      (q739403-v-member-p vector-space v)
      (q739403-v-member-p vector-space w))
     (let ((zero-v (q739403-v-zero real vector-space))
           (one (q739403-r-one real)))
       (and
        (q739403-v-member-p
         vector-space (q739403-v-add real vector-space u v))
        (q739403-v-member-p
         vector-space (q739403-v-neg real vector-space u))
        (q739403-v-member-p
         vector-space (q739403-v-smul real vector-space a u))
        (equal
         (q739403-v-add real vector-space u v)
         (q739403-v-add real vector-space v u))
        (equal
         (q739403-v-add
          real vector-space
          (q739403-v-add real vector-space u v)
          w)
         (q739403-v-add
          real vector-space
          u
          (q739403-v-add real vector-space v w)))
        (equal (q739403-v-add real vector-space u zero-v) u)
        (equal
         (q739403-v-add
          real vector-space u (q739403-v-neg real vector-space u))
         zero-v)
        (equal
         (q739403-v-smul
          real vector-space a
          (q739403-v-add real vector-space u v))
         (q739403-v-add
          real vector-space
          (q739403-v-smul real vector-space a u)
          (q739403-v-smul real vector-space a v)))
        (equal
         (q739403-v-smul
          real vector-space (q739403-r-add real a b) u)
         (q739403-v-add
          real vector-space
          (q739403-v-smul real vector-space a u)
          (q739403-v-smul real vector-space b u)))
        (equal
         (q739403-v-smul
          real vector-space (q739403-r-mul real a b) u)
         (q739403-v-smul
          real vector-space
          a
          (q739403-v-smul real vector-space b u)))
        (equal
         (q739403-v-smul real vector-space one u)
         u))))))

(defun-sk q739403-inner-product-laws-p (real vector-space)
  (forall (a u v w)
    (implies
     (and
      (q739403-r-member-p real a)
      (q739403-v-member-p vector-space u)
      (q739403-v-member-p vector-space v)
      (q739403-v-member-p vector-space w))
     (let ((zero-r (q739403-r-zero real))
           (zero-v (q739403-v-zero real vector-space)))
       (and
        (q739403-r-member-p
         real (q739403-inner real vector-space u v))
        (equal
         (q739403-inner real vector-space u v)
         (q739403-inner real vector-space v u))
        (equal
         (q739403-inner
          real vector-space
          (q739403-v-add real vector-space u v)
          w)
         (q739403-r-add
          real
          (q739403-inner real vector-space u w)
          (q739403-inner real vector-space v w)))
        (equal
         (q739403-inner
          real vector-space
          (q739403-v-smul real vector-space a u)
          v)
         (q739403-r-mul
          real a (q739403-inner real vector-space u v)))
        (q739403-r-leq
         real zero-r (q739403-inner real vector-space u u))
        (equal
         (equal (q739403-inner real vector-space u u) zero-r)
         (equal u zero-v)))))))

;; The nonnegative square root relation uniquely characterizes the norm
;; induced by the real inner product, without replacing real values by
;; rational approximations.
(defun-sk q739403-norm-laws-p (real vector-space)
  (forall (u)
    (implies
     (q739403-v-member-p vector-space u)
     (let ((length (q739403-norm real vector-space u))
           (zero-r (q739403-r-zero real)))
       (and
        (q739403-r-member-p real length)
        (q739403-r-leq real zero-r length)
        (equal
         (q739403-r-mul real length length)
         (q739403-inner real vector-space u u)))))))

(defun-sk q739403-point-space-nonempty-p (point-space)
  (exists (point)
    (q739403-p-member-p point-space point)))

(defun-sk q739403-affine-torsor-laws-p
    (real vector-space point-space)
  (forall (u v p q r)
    (implies
     (and
      (q739403-v-member-p vector-space u)
      (q739403-v-member-p vector-space v)
      (q739403-p-member-p point-space p)
      (q739403-p-member-p point-space q)
      (q739403-p-member-p point-space r))
     (let ((zero-v (q739403-v-zero real vector-space)))
       (and
        (q739403-p-member-p
         point-space
         (q739403-vadd real vector-space point-space u p))
        (q739403-v-member-p
         vector-space
         (q739403-vsub real vector-space point-space p q))
        (equal
         (q739403-vadd real vector-space point-space zero-v p)
         p)
        (equal
         (q739403-vadd
          real vector-space point-space
          (q739403-v-add real vector-space u v)
          p)
         (q739403-vadd
          real vector-space point-space u
          (q739403-vadd real vector-space point-space v p)))
        (equal
         (q739403-vadd
          real vector-space point-space
          (q739403-vsub real vector-space point-space p q)
          q)
         p)
        (equal
         (q739403-vsub
          real vector-space point-space
          (q739403-vadd real vector-space point-space u p)
          p)
         u)
        (equal
         (q739403-vsub real vector-space point-space p r)
         (q739403-v-add
          real vector-space
          (q739403-vsub real vector-space point-space p q)
          (q739403-vsub real vector-space point-space q r))))))))

(defun q739403-context-p (real vector-space point-space)
  (and
   (q739403-real-p real)
   (q739403-v-member-p
    vector-space (q739403-v-zero real vector-space))
   (q739403-vector-space-laws-p real vector-space)
   (q739403-inner-product-laws-p real vector-space)
   (q739403-norm-laws-p real vector-space)
   (q739403-point-space-nonempty-p point-space)
   (q739403-affine-torsor-laws-p real vector-space point-space)))

(defun q739403-distance
    (real vector-space point-space left right)
  (q739403-norm
   real
   vector-space
   (q739403-vsub
    real vector-space point-space left right)))

(defun q739403-square (real x)
  (q739403-r-mul real x x))

;; InnerProductGeometry.angle_eq_pi_iff says exactly that the first
;; displacement is nonzero and the second is a negative scalar multiple of
;; it. The extra nonzero conjunct is a consequence of the other conjuncts
;; and makes the nondegeneracy explicit.
(defun-sk q739403-angle-pi-p
    (real vector-space point-space left vertex right)
  (exists (scale)
    (let ((left-vector
           (q739403-vsub
            real vector-space point-space left vertex))
          (right-vector
           (q739403-vsub
            real vector-space point-space right vertex))
          (zero-v (q739403-v-zero real vector-space))
          (zero-r (q739403-r-zero real)))
      (and
       (q739403-r-member-p real scale)
       (q739403-r-less real scale zero-r)
       (not (equal left-vector zero-v))
       (not (equal right-vector zero-v))
       (equal
        right-vector
        (q739403-v-smul
         real vector-space scale left-vector))))))

(defun-sk thousand-theorems-q739403-stewart-s-theorem-statement
    (real vector-space point-space)
  (forall (a b c p)
    (implies
     (and
      (q739403-context-p real vector-space point-space)
      (q739403-p-member-p point-space a)
      (q739403-p-member-p point-space b)
      (q739403-p-member-p point-space c)
      (q739403-p-member-p point-space p)
      (q739403-angle-pi-p
       real vector-space point-space b p c))
     (let ((dist-ab
            (q739403-distance
             real vector-space point-space a b))
           (dist-ac
            (q739403-distance
             real vector-space point-space a c))
           (dist-ap
            (q739403-distance
             real vector-space point-space a p))
           (dist-bc
            (q739403-distance
             real vector-space point-space b c))
           (dist-bp
            (q739403-distance
             real vector-space point-space b p))
           (dist-cp
            (q739403-distance
             real vector-space point-space c p)))
       (equal
        (q739403-r-add
         real
         (q739403-r-mul
          real (q739403-square real dist-ab) dist-cp)
         (q739403-r-mul
          real (q739403-square real dist-ac) dist-bp))
        (q739403-r-mul
         real
         dist-bc
         (q739403-r-add
          real
          (q739403-square real dist-ap)
          (q739403-r-mul real dist-bp dist-cp))))))))

(value-triple :itpeval-statement-checked)
:q
