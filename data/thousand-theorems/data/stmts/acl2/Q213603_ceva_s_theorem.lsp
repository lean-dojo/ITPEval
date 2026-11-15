;; Statement-only formalization of thousand-theorems corpus artifact Q213603,
;; "Ceva's theorem": in an affinely independent triangle over an arbitrary
;; normed field, three concurrent cevians give a product of distance ratios
;; equal to one when the three denominators are nonzero. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative symbols represent the source's real norm values, arbitrary
;; normed scalar field, seminormed vector space, and affine metric torsor.
;; Every carrier restriction and structural law is explicit below.

(defstub q213603-r-member-p (real x) t)
(defstub q213603-r-set-member-p (real set x) t)
(defstub q213603-k-member-p (scalar-field x) t)
(defstub q213603-v-member-p (vector-space x) t)
(defstub q213603-p-member-p (point-space x) t)

(defstub q213603-r-zero (real) t)
(defstub q213603-r-one (real) t)
(defstub q213603-r-add (real x y) t)
(defstub q213603-r-mul (real x y) t)
(defstub q213603-r-neg (real x) t)
(defstub q213603-r-inv (real x) t)
(defstub q213603-r-less (real x y) t)

(defstub q213603-k-zero (scalar-field) t)
(defstub q213603-k-one (scalar-field) t)
(defstub q213603-k-add (scalar-field x y) t)
(defstub q213603-k-mul (scalar-field x y) t)
(defstub q213603-k-neg (scalar-field x) t)
(defstub q213603-k-inv (scalar-field x) t)
(defstub q213603-k-norm (real scalar-field x) t)

(defstub q213603-v-zero (vector-space) t)
(defstub q213603-v-add (vector-space x y) t)
(defstub q213603-v-neg (vector-space x) t)
(defstub q213603-v-smul (scalar-field vector-space scalar vector) t)
(defstub q213603-v-norm (real vector-space vector) t)

(defstub q213603-vadd
  (vector-space point-space vector point)
  t)
(defstub q213603-vsub
  (vector-space point-space left-point right-point)
  t)

(defun q213603-r-leq (real x y)
  (not (q213603-r-less real y x)))

(defun q213603-r-div (real x y)
  (q213603-r-mul real x (q213603-r-inv real y)))

(defun-sk q213603-real-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q213603-r-member-p real x)
      (q213603-r-member-p real y)
      (q213603-r-member-p real z))
     (let ((zero (q213603-r-zero real))
           (one (q213603-r-one real)))
       (and
        (q213603-r-member-p real (q213603-r-add real x y))
        (q213603-r-member-p real (q213603-r-mul real x y))
        (q213603-r-member-p real (q213603-r-neg real x))
        (q213603-r-member-p real (q213603-r-inv real x))
        (equal
         (q213603-r-add real (q213603-r-add real x y) z)
         (q213603-r-add real x (q213603-r-add real y z)))
        (equal (q213603-r-add real x y)
               (q213603-r-add real y x))
        (equal (q213603-r-add real x zero) x)
        (equal
         (q213603-r-add real x (q213603-r-neg real x))
         zero)
        (equal
         (q213603-r-mul real (q213603-r-mul real x y) z)
         (q213603-r-mul real x (q213603-r-mul real y z)))
        (equal (q213603-r-mul real x y)
               (q213603-r-mul real y x))
        (equal (q213603-r-mul real x one) x)
        (equal (q213603-r-mul real x zero) zero)
        (equal
         (q213603-r-mul real x (q213603-r-add real y z))
         (q213603-r-add
          real
          (q213603-r-mul real x y)
          (q213603-r-mul real x z)))
        (equal (q213603-r-inv real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q213603-r-mul real x (q213603-r-inv real x))
          one))
        (not (q213603-r-less real x x))
        (or (equal x y)
            (q213603-r-less real x y)
            (q213603-r-less real y x))
        (implies
         (and
          (q213603-r-less real x y)
          (q213603-r-less real y z))
         (q213603-r-less real x z))
        (implies
         (q213603-r-less real x y)
         (q213603-r-less
          real
          (q213603-r-add real x z)
          (q213603-r-add real y z)))
        (implies
         (and
          (q213603-r-less real zero x)
          (q213603-r-less real zero y))
         (q213603-r-less
          real zero (q213603-r-mul real x y))))))))

(defun-sk q213603-r-set-valid-p (real set)
  (forall (x)
    (implies
     (q213603-r-set-member-p real set x)
     (q213603-r-member-p real x))))

(defun-sk q213603-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q213603-r-member-p real x)
     (q213603-r-set-member-p real set x))))

(defun-sk q213603-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q213603-r-member-p real x)
      (q213603-r-set-member-p real set x))
     (q213603-r-leq real x bound))))

(defun-sk q213603-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q213603-r-member-p real bound)
     (q213603-r-upper-bound-p real set bound))))

(defun-sk q213603-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q213603-r-member-p real supremum)
     (q213603-r-upper-bound-p real set supremum)
     (implies
      (and
       (q213603-r-member-p real bound)
       (q213603-r-upper-bound-p real set bound))
      (q213603-r-leq real supremum bound)))))

(defun-sk q213603-r-supremum-exists-p (real set)
  (exists (supremum)
    (q213603-r-supremum-p real set supremum)))

(defun-sk q213603-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q213603-r-set-valid-p real set)
      (q213603-r-set-nonempty-p real set)
      (q213603-r-bounded-above-p real set))
     (q213603-r-supremum-exists-p real set))))

(defun q213603-real-p (real)
  (let ((zero (q213603-r-zero real))
        (one (q213603-r-one real)))
    (and
     (q213603-r-member-p real zero)
     (q213603-r-member-p real one)
     (not (equal zero one))
     (q213603-r-less real zero one)
     (q213603-real-field-laws-p real)
     (q213603-r-dedekind-complete-p real))))

(defun-sk q213603-scalar-field-laws-p (scalar-field)
  (forall (x y z)
    (implies
     (and
      (q213603-k-member-p scalar-field x)
      (q213603-k-member-p scalar-field y)
      (q213603-k-member-p scalar-field z))
     (let ((zero (q213603-k-zero scalar-field))
           (one (q213603-k-one scalar-field)))
       (and
        (q213603-k-member-p
         scalar-field (q213603-k-add scalar-field x y))
        (q213603-k-member-p
         scalar-field (q213603-k-mul scalar-field x y))
        (q213603-k-member-p
         scalar-field (q213603-k-neg scalar-field x))
        (q213603-k-member-p
         scalar-field (q213603-k-inv scalar-field x))
        (equal
         (q213603-k-add
          scalar-field (q213603-k-add scalar-field x y) z)
         (q213603-k-add
          scalar-field x (q213603-k-add scalar-field y z)))
        (equal (q213603-k-add scalar-field x y)
               (q213603-k-add scalar-field y x))
        (equal (q213603-k-add scalar-field x zero) x)
        (equal
         (q213603-k-add scalar-field x
                        (q213603-k-neg scalar-field x))
         zero)
        (equal
         (q213603-k-mul
          scalar-field (q213603-k-mul scalar-field x y) z)
         (q213603-k-mul
          scalar-field x (q213603-k-mul scalar-field y z)))
        (equal (q213603-k-mul scalar-field x y)
               (q213603-k-mul scalar-field y x))
        (equal (q213603-k-mul scalar-field x one) x)
        (equal (q213603-k-mul scalar-field x zero) zero)
        (equal
         (q213603-k-mul
          scalar-field x (q213603-k-add scalar-field y z))
         (q213603-k-add
          scalar-field
          (q213603-k-mul scalar-field x y)
          (q213603-k-mul scalar-field x z)))
        (equal (q213603-k-inv scalar-field zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q213603-k-mul
           scalar-field x (q213603-k-inv scalar-field x))
          one)))))))

(defun-sk q213603-scalar-norm-laws-p (real scalar-field)
  (forall (x y)
    (implies
     (and
      (q213603-k-member-p scalar-field x)
      (q213603-k-member-p scalar-field y))
     (let ((zero-k (q213603-k-zero scalar-field))
           (one-k (q213603-k-one scalar-field))
           (zero-r (q213603-r-zero real))
           (one-r (q213603-r-one real))
           (norm-x (q213603-k-norm real scalar-field x))
           (norm-y (q213603-k-norm real scalar-field y)))
       (and
        (q213603-r-member-p real norm-x)
        (q213603-r-member-p real norm-y)
        (q213603-r-leq real zero-r norm-x)
        (equal
         (equal norm-x zero-r)
         (equal x zero-k))
        (equal
         (q213603-k-norm real scalar-field one-k)
         one-r)
        (equal
         (q213603-k-norm
          real scalar-field (q213603-k-neg scalar-field x))
         norm-x)
        (equal
         (q213603-k-norm
          real scalar-field (q213603-k-mul scalar-field x y))
         (q213603-r-mul real norm-x norm-y))
        (q213603-r-leq
         real
         (q213603-k-norm
          real scalar-field (q213603-k-add scalar-field x y))
         (q213603-r-add real norm-x norm-y)))))))

(defun q213603-normed-field-p (real scalar-field)
  (let ((zero (q213603-k-zero scalar-field))
        (one (q213603-k-one scalar-field)))
    (and
     (q213603-k-member-p scalar-field zero)
     (q213603-k-member-p scalar-field one)
     (not (equal zero one))
     (q213603-scalar-field-laws-p scalar-field)
     (q213603-scalar-norm-laws-p real scalar-field))))

(defun-sk q213603-vector-space-laws-p
    (scalar-field vector-space)
  (forall (a b u v w)
    (implies
     (and
      (q213603-k-member-p scalar-field a)
      (q213603-k-member-p scalar-field b)
      (q213603-v-member-p vector-space u)
      (q213603-v-member-p vector-space v)
      (q213603-v-member-p vector-space w))
     (let ((zero-v (q213603-v-zero vector-space))
           (one-k (q213603-k-one scalar-field)))
       (and
        (q213603-v-member-p
         vector-space (q213603-v-add vector-space u v))
        (q213603-v-member-p
         vector-space (q213603-v-neg vector-space u))
        (q213603-v-member-p
         vector-space
         (q213603-v-smul scalar-field vector-space a u))
        (equal
         (q213603-v-add
          vector-space (q213603-v-add vector-space u v) w)
         (q213603-v-add
          vector-space u (q213603-v-add vector-space v w)))
        (equal (q213603-v-add vector-space u v)
               (q213603-v-add vector-space v u))
        (equal (q213603-v-add vector-space u zero-v) u)
        (equal
         (q213603-v-add
          vector-space u (q213603-v-neg vector-space u))
         zero-v)
        (equal
         (q213603-v-smul scalar-field vector-space one-k u)
         u)
        (equal
         (q213603-v-smul
          scalar-field vector-space
          (q213603-k-mul scalar-field a b)
          u)
         (q213603-v-smul
          scalar-field vector-space a
          (q213603-v-smul
           scalar-field vector-space b u)))
        (equal
         (q213603-v-smul
          scalar-field vector-space
          (q213603-k-add scalar-field a b)
          u)
         (q213603-v-add
          vector-space
          (q213603-v-smul
           scalar-field vector-space a u)
          (q213603-v-smul
           scalar-field vector-space b u)))
        (equal
         (q213603-v-smul
          scalar-field vector-space a
          (q213603-v-add vector-space u v))
         (q213603-v-add
          vector-space
          (q213603-v-smul
           scalar-field vector-space a u)
          (q213603-v-smul
           scalar-field vector-space a v))))))))

(defun-sk q213603-vector-norm-laws-p
    (real scalar-field vector-space)
  (forall (a u v)
    (implies
     (and
      (q213603-k-member-p scalar-field a)
      (q213603-v-member-p vector-space u)
      (q213603-v-member-p vector-space v))
     (let ((zero-r (q213603-r-zero real))
           (zero-v (q213603-v-zero vector-space))
           (norm-u (q213603-v-norm real vector-space u))
           (norm-v (q213603-v-norm real vector-space v)))
       (and
        (q213603-r-member-p real norm-u)
        (q213603-r-member-p real norm-v)
        (q213603-r-leq real zero-r norm-u)
        (equal
         (equal norm-u zero-r)
         (equal u zero-v))
        (equal
         (q213603-v-norm
          real vector-space (q213603-v-neg vector-space u))
         norm-u)
        (q213603-r-leq
         real
         (q213603-v-norm
          real vector-space (q213603-v-add vector-space u v))
         (q213603-r-add real norm-u norm-v))
        (equal
         (q213603-v-norm
          real vector-space
          (q213603-v-smul scalar-field vector-space a u))
         (q213603-r-mul
          real
          (q213603-k-norm real scalar-field a)
          norm-u)))))))

(defun-sk q213603-point-space-nonempty-p (point-space)
  (exists (point)
    (q213603-p-member-p point-space point)))

(defun-sk q213603-affine-torsor-laws-p
    (vector-space point-space)
  (forall (u v p q r)
    (implies
     (and
      (q213603-v-member-p vector-space u)
      (q213603-v-member-p vector-space v)
      (q213603-p-member-p point-space p)
      (q213603-p-member-p point-space q)
      (q213603-p-member-p point-space r))
     (let ((zero-v (q213603-v-zero vector-space)))
       (and
        (q213603-p-member-p
         point-space
         (q213603-vadd vector-space point-space u p))
        (q213603-v-member-p
         vector-space
         (q213603-vsub vector-space point-space p q))
        (equal
         (q213603-vadd vector-space point-space zero-v p)
         p)
        (equal
         (q213603-vadd
          vector-space point-space
          (q213603-v-add vector-space u v)
          p)
         (q213603-vadd
          vector-space point-space u
          (q213603-vadd vector-space point-space v p)))
        (equal
         (q213603-vadd
          vector-space point-space
          (q213603-vsub vector-space point-space p q)
          q)
         p)
        (equal
         (q213603-vsub
          vector-space point-space
          (q213603-vadd vector-space point-space u p)
          p)
         u)
        (equal
         (q213603-vsub vector-space point-space p r)
         (q213603-v-add
          vector-space
          (q213603-vsub vector-space point-space p q)
          (q213603-vsub vector-space point-space q r))))))))

(defun q213603-context-p
    (real scalar-field vector-space point-space)
  (and
   (q213603-real-p real)
   (q213603-normed-field-p real scalar-field)
   (q213603-v-member-p
    vector-space (q213603-v-zero vector-space))
   (q213603-vector-space-laws-p scalar-field vector-space)
   (q213603-vector-norm-laws-p
    real scalar-field vector-space)
   (q213603-point-space-nonempty-p point-space)
   (q213603-affine-torsor-laws-p vector-space point-space)))

;; This is the affine line through first and second, with its scalar parameter
;; existentially quantified inside the predicate.
(defun-sk q213603-line-member-p
    (scalar-field vector-space point-space point first second)
  (exists (parameter)
    (and
     (q213603-k-member-p scalar-field parameter)
     (equal
      point
      (q213603-vadd
       vector-space point-space
       (q213603-v-smul
        scalar-field vector-space parameter
        (q213603-vsub
         vector-space point-space second first))
       first)))))

;; For three points over a field, affine independence is equivalent to linear
;; independence of the two displacement vectors based at the first point.
(defun-sk q213603-triangle-independent-p
    (scalar-field vector-space point-space t0 t1 t2)
  (forall (a b)
    (implies
     (and
      (q213603-k-member-p scalar-field a)
      (q213603-k-member-p scalar-field b)
      (equal
       (q213603-v-add
        vector-space
        (q213603-v-smul
         scalar-field vector-space a
         (q213603-vsub vector-space point-space t1 t0))
        (q213603-v-smul
         scalar-field vector-space b
         (q213603-vsub vector-space point-space t2 t0)))
       (q213603-v-zero vector-space)))
     (and
      (equal a (q213603-k-zero scalar-field))
      (equal b (q213603-k-zero scalar-field))))))

(defun q213603-distance
    (real vector-space point-space first second)
  (q213603-v-norm
   real vector-space
   (q213603-vsub vector-space point-space first second)))

(defun q213603-distance-ratio
    (real vector-space point-space first middle last)
  (q213603-r-div
   real
   (q213603-distance
    real vector-space point-space first middle)
   (q213603-distance
    real vector-space point-space middle last)))

(defun q213603-ceva-conclusion-p
    (real vector-space point-space t0 t1 t2 p0 p1 p2)
  (equal
   (q213603-r-mul
    real
    (q213603-distance-ratio
     real vector-space point-space t1 p0 t2)
    (q213603-r-mul
     real
     (q213603-distance-ratio
      real vector-space point-space t2 p1 t0)
     (q213603-distance-ratio
      real vector-space point-space t0 p2 t1)))
   (q213603-r-one real)))

(defun-sk thousand-theorems-q213603-cevas-theorem-statement
    (real scalar-field vector-space point-space)
  (forall (t0 t1 t2 p0 p1 p2 concurrent-point)
    (implies
     (and
      (q213603-context-p
       real scalar-field vector-space point-space)
      (q213603-p-member-p point-space t0)
      (q213603-p-member-p point-space t1)
      (q213603-p-member-p point-space t2)
      (q213603-p-member-p point-space p0)
      (q213603-p-member-p point-space p1)
      (q213603-p-member-p point-space p2)
      (q213603-p-member-p point-space concurrent-point)
      (q213603-triangle-independent-p
       scalar-field vector-space point-space t0 t1 t2)
      (not (equal p0 t2))
      (not (equal p1 t0))
      (not (equal p2 t1))
      (q213603-line-member-p
       scalar-field vector-space point-space p0 t1 t2)
      (q213603-line-member-p
       scalar-field vector-space point-space p1 t2 t0)
      (q213603-line-member-p
       scalar-field vector-space point-space p2 t0 t1)
      (q213603-line-member-p
       scalar-field vector-space point-space concurrent-point t0 p0)
      (q213603-line-member-p
       scalar-field vector-space point-space concurrent-point t1 p1)
      (q213603-line-member-p
       scalar-field vector-space point-space concurrent-point t2 p2))
     (q213603-ceva-conclusion-p
      real vector-space point-space t0 t1 t2 p0 p1 p2))))

(value-triple :itpeval-statement-checked)
:q
