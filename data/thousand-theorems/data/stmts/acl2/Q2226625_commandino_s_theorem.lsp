;; Statement-only formalization of thousand-theorems corpus artifact Q2226625,
;; "Commandino's theorem": for an n-simplex in an affine space over an
;; arbitrary characteristic-zero division ring, the vector from a vertex to
;; the centroid is n times the vector from the centroid to the opposite-face
;; centroid. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative symbols represent the arbitrary scalar division ring, module,
;; affine point space, and simplex vertex map. All carrier and structure laws
;; used by the source types are explicit below.

(defstub q2226625-k-member-p (scalar-space value) t)
(defstub q2226625-v-member-p (vector-space value) t)
(defstub q2226625-p-member-p (point-space value) t)

(defstub q2226625-k-zero (scalar-space) t)
(defstub q2226625-k-one (scalar-space) t)
(defstub q2226625-k-add (scalar-space left right) t)
(defstub q2226625-k-mul (scalar-space left right) t)
(defstub q2226625-k-neg (scalar-space value) t)
(defstub q2226625-k-inv (scalar-space value) t)

(defstub q2226625-v-zero (vector-space) t)
(defstub q2226625-v-add (vector-space left right) t)
(defstub q2226625-v-neg (vector-space value) t)
(defstub q2226625-v-smul
  (scalar-space vector-space scalar vector)
  t)

(defstub q2226625-vadd
  (vector-space point-space vector point)
  t)
(defstub q2226625-vsub
  (vector-space point-space left-point right-point)
  t)

(defstub q2226625-point
  (point-space simplex index)
  t)

(defun q2226625-nat-cast (scalar-space n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q2226625-k-zero scalar-space)
    (q2226625-k-add
     scalar-space
     (q2226625-k-one scalar-space)
     (q2226625-nat-cast
      scalar-space (- (nfix n) 1)))))

(defun q2226625-scalar-list-p
    (scalar-space coefficients count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (equal coefficients nil)
    (and
     (consp coefficients)
     (q2226625-k-member-p scalar-space (car coefficients))
     (q2226625-scalar-list-p
      scalar-space
      (cdr coefficients)
      (- (nfix count) 1)))))

(defun q2226625-scalar-sum
    (scalar-space coefficients count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q2226625-k-zero scalar-space)
    (q2226625-k-add
     scalar-space
     (car coefficients)
     (q2226625-scalar-sum
      scalar-space
      (cdr coefficients)
      (- (nfix count) 1)))))

(defun q2226625-all-zero-scalars-p
    (scalar-space coefficients count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and
     (equal
      (car coefficients)
      (q2226625-k-zero scalar-space))
     (q2226625-all-zero-scalars-p
      scalar-space
      (cdr coefficients)
      (- (nfix count) 1)))))

(defun q2226625-points-typed-from-p
    (point-space simplex start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and
     (q2226625-p-member-p
      point-space
      (q2226625-point point-space simplex (nfix start)))
     (q2226625-points-typed-from-p
      point-space
      simplex
      (+ 1 (nfix start))
      (- (nfix count) 1)))))

(defun q2226625-weighted-vsub-sum
    (scalar-space vector-space point-space simplex
                  coefficients base-index start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q2226625-v-zero vector-space)
    (q2226625-v-add
     vector-space
     (q2226625-v-smul
      scalar-space
      vector-space
      (car coefficients)
      (q2226625-vsub
       vector-space
       point-space
       (q2226625-point point-space simplex (nfix start))
       (q2226625-point point-space simplex base-index)))
     (q2226625-weighted-vsub-sum
      scalar-space
      vector-space
      point-space
      simplex
      (cdr coefficients)
      base-index
      (+ 1 (nfix start))
      (- (nfix count) 1)))))

(defun q2226625-vsub-sum
    (vector-space point-space simplex base-index start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q2226625-v-zero vector-space)
    (q2226625-v-add
     vector-space
     (q2226625-vsub
      vector-space
      point-space
      (q2226625-point point-space simplex (nfix start))
      (q2226625-point point-space simplex base-index))
     (q2226625-vsub-sum
      vector-space
      point-space
      simplex
      base-index
      (+ 1 (nfix start))
      (- (nfix count) 1)))))

(defun q2226625-face-vsub-sum
    (vector-space point-space simplex omitted-index
                  base-index start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q2226625-v-zero vector-space)
    (if (equal (nfix start) omitted-index)
        (q2226625-face-vsub-sum
         vector-space
         point-space
         simplex
         omitted-index
         base-index
         (+ 1 (nfix start))
         (- (nfix count) 1))
      (q2226625-v-add
       vector-space
       (q2226625-vsub
        vector-space
        point-space
        (q2226625-point point-space simplex (nfix start))
        (q2226625-point point-space simplex base-index))
       (q2226625-face-vsub-sum
        vector-space
        point-space
        simplex
        omitted-index
        base-index
        (+ 1 (nfix start))
        (- (nfix count) 1))))))

(defun-sk q2226625-division-ring-laws-p (scalar-space)
  (forall (x y z)
    (and
     (implies
      (q2226625-k-member-p scalar-space x)
      (and
       (q2226625-k-member-p
        scalar-space (q2226625-k-neg scalar-space x))
       (q2226625-k-member-p
        scalar-space (q2226625-k-inv scalar-space x))
       (equal
        (q2226625-k-add
         scalar-space x (q2226625-k-zero scalar-space))
        x)
       (equal
        (q2226625-k-add
         scalar-space x (q2226625-k-neg scalar-space x))
        (q2226625-k-zero scalar-space))
       (equal
        (q2226625-k-mul
         scalar-space x (q2226625-k-one scalar-space))
        x)
       (equal
        (q2226625-k-mul
         scalar-space (q2226625-k-one scalar-space) x)
        x)
       (equal
        (q2226625-k-mul
         scalar-space x (q2226625-k-zero scalar-space))
        (q2226625-k-zero scalar-space))
       (equal
        (q2226625-k-mul
         scalar-space (q2226625-k-zero scalar-space) x)
        (q2226625-k-zero scalar-space))
       (implies
        (not (equal x (q2226625-k-zero scalar-space)))
        (and
         (equal
          (q2226625-k-mul
           scalar-space x (q2226625-k-inv scalar-space x))
          (q2226625-k-one scalar-space))
         (equal
          (q2226625-k-mul
           scalar-space (q2226625-k-inv scalar-space x) x)
          (q2226625-k-one scalar-space))))))
     (implies
      (and
       (q2226625-k-member-p scalar-space x)
       (q2226625-k-member-p scalar-space y))
      (and
       (q2226625-k-member-p
        scalar-space (q2226625-k-add scalar-space x y))
       (q2226625-k-member-p
        scalar-space (q2226625-k-mul scalar-space x y))
       (equal
        (q2226625-k-add scalar-space x y)
        (q2226625-k-add scalar-space y x))))
     (implies
      (and
       (q2226625-k-member-p scalar-space x)
       (q2226625-k-member-p scalar-space y)
       (q2226625-k-member-p scalar-space z))
      (and
       (equal
        (q2226625-k-add
         scalar-space
         (q2226625-k-add scalar-space x y)
         z)
        (q2226625-k-add
         scalar-space
         x
         (q2226625-k-add scalar-space y z)))
       (equal
        (q2226625-k-mul
         scalar-space
         (q2226625-k-mul scalar-space x y)
         z)
        (q2226625-k-mul
         scalar-space
         x
         (q2226625-k-mul scalar-space y z)))
       (equal
        (q2226625-k-mul
         scalar-space
         x
         (q2226625-k-add scalar-space y z))
        (q2226625-k-add
         scalar-space
         (q2226625-k-mul scalar-space x y)
         (q2226625-k-mul scalar-space x z)))
       (equal
        (q2226625-k-mul
         scalar-space
         (q2226625-k-add scalar-space x y)
         z)
        (q2226625-k-add
         scalar-space
         (q2226625-k-mul scalar-space x z)
         (q2226625-k-mul scalar-space y z))))))))

(defun q2226625-division-ring-p (scalar-space)
  (and
   (q2226625-k-member-p
    scalar-space (q2226625-k-zero scalar-space))
   (q2226625-k-member-p
    scalar-space (q2226625-k-one scalar-space))
   (not
    (equal
     (q2226625-k-zero scalar-space)
     (q2226625-k-one scalar-space)))
   (equal
    (q2226625-k-inv
     scalar-space (q2226625-k-zero scalar-space))
    (q2226625-k-zero scalar-space))
   (q2226625-division-ring-laws-p scalar-space)))

(defun-sk q2226625-char-zero-p (scalar-space)
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right)
      (equal
       (q2226625-nat-cast scalar-space left)
       (q2226625-nat-cast scalar-space right)))
     (equal left right))))

(defun-sk q2226625-vector-space-laws-p
    (scalar-space vector-space)
  (forall (a b u v w)
    (and
     (implies
      (q2226625-v-member-p vector-space u)
      (and
       (q2226625-v-member-p
        vector-space (q2226625-v-neg vector-space u))
       (equal
        (q2226625-v-add
         vector-space u (q2226625-v-zero vector-space))
        u)
       (equal
        (q2226625-v-add
         vector-space u (q2226625-v-neg vector-space u))
        (q2226625-v-zero vector-space))
       (equal
        (q2226625-v-smul
         scalar-space
         vector-space
         (q2226625-k-zero scalar-space)
         u)
        (q2226625-v-zero vector-space))))
     (implies
      (and
       (q2226625-v-member-p vector-space u)
       (q2226625-v-member-p vector-space v))
      (and
       (q2226625-v-member-p
        vector-space (q2226625-v-add vector-space u v))
       (equal
        (q2226625-v-add vector-space u v)
        (q2226625-v-add vector-space v u))))
     (implies
      (and
       (q2226625-v-member-p vector-space u)
       (q2226625-v-member-p vector-space v)
       (q2226625-v-member-p vector-space w))
      (equal
       (q2226625-v-add
        vector-space
        (q2226625-v-add vector-space u v)
        w)
       (q2226625-v-add
        vector-space
        u
        (q2226625-v-add vector-space v w))))
     (implies
      (and
       (q2226625-k-member-p scalar-space a)
       (q2226625-v-member-p vector-space u))
      (and
       (q2226625-v-member-p
        vector-space
        (q2226625-v-smul
         scalar-space vector-space a u))
       (equal
        (q2226625-v-smul
         scalar-space
         vector-space
         (q2226625-k-one scalar-space)
         u)
        u)))
     (implies
      (and
       (q2226625-k-member-p scalar-space a)
       (q2226625-k-member-p scalar-space b)
       (q2226625-v-member-p vector-space u))
      (and
       (equal
        (q2226625-v-smul
         scalar-space
         vector-space
         (q2226625-k-mul scalar-space a b)
         u)
        (q2226625-v-smul
         scalar-space
         vector-space
         a
         (q2226625-v-smul
          scalar-space vector-space b u)))
       (equal
        (q2226625-v-smul
         scalar-space
         vector-space
         (q2226625-k-add scalar-space a b)
         u)
        (q2226625-v-add
         vector-space
         (q2226625-v-smul
          scalar-space vector-space a u)
         (q2226625-v-smul
          scalar-space vector-space b u)))))
     (implies
      (and
       (q2226625-k-member-p scalar-space a)
       (q2226625-v-member-p vector-space u)
       (q2226625-v-member-p vector-space v))
      (equal
       (q2226625-v-smul
        scalar-space
        vector-space
        a
        (q2226625-v-add vector-space u v))
       (q2226625-v-add
        vector-space
        (q2226625-v-smul
         scalar-space vector-space a u)
        (q2226625-v-smul
         scalar-space vector-space a v)))))))

(defun q2226625-vector-space-p
    (scalar-space vector-space)
  (and
   (q2226625-v-member-p
    vector-space (q2226625-v-zero vector-space))
   (q2226625-vector-space-laws-p
    scalar-space vector-space)))

(defun-sk q2226625-point-space-nonempty-p (point-space)
  (exists (point)
    (q2226625-p-member-p point-space point)))

(defun-sk q2226625-affine-space-laws-p
    (vector-space point-space)
  (forall (u v p q r)
    (and
     (implies
      (q2226625-p-member-p point-space p)
      (equal
       (q2226625-vadd
        vector-space
        point-space
        (q2226625-v-zero vector-space)
        p)
       p))
     (implies
      (and
       (q2226625-v-member-p vector-space u)
       (q2226625-p-member-p point-space p))
      (and
       (q2226625-p-member-p
        point-space
        (q2226625-vadd vector-space point-space u p))
       (equal
        (q2226625-vsub
         vector-space
         point-space
         (q2226625-vadd vector-space point-space u p)
         p)
        u)))
     (implies
      (and
       (q2226625-p-member-p point-space p)
       (q2226625-p-member-p point-space q))
      (and
       (q2226625-v-member-p
        vector-space
        (q2226625-vsub vector-space point-space p q))
       (equal
        (q2226625-vadd
         vector-space
         point-space
         (q2226625-vsub vector-space point-space p q)
         q)
        p)))
     (implies
      (and
       (q2226625-v-member-p vector-space u)
       (q2226625-v-member-p vector-space v)
       (q2226625-p-member-p point-space p))
      (equal
       (q2226625-vadd
        vector-space
        point-space
        (q2226625-v-add vector-space u v)
        p)
       (q2226625-vadd
        vector-space
        point-space
        u
        (q2226625-vadd vector-space point-space v p))))
     (implies
      (and
       (q2226625-p-member-p point-space p)
       (q2226625-p-member-p point-space q)
       (q2226625-p-member-p point-space r))
      (equal
       (q2226625-vsub vector-space point-space p r)
       (q2226625-v-add
        vector-space
        (q2226625-vsub vector-space point-space p q)
        (q2226625-vsub vector-space point-space q r)))))))

(defun q2226625-context-p
    (scalar-space vector-space point-space)
  (and
   (q2226625-division-ring-p scalar-space)
   (q2226625-char-zero-p scalar-space)
   (q2226625-vector-space-p scalar-space vector-space)
   (q2226625-point-space-nonempty-p point-space)
   (q2226625-affine-space-laws-p
    vector-space point-space)))

;; For the finite index type Fin (n+1), coefficient lists represent all
;; scalar-valued functions. This is the source definition of affine
;; independence via zero-sum weighted point subtractions.
(defun-sk q2226625-simplex-independent-p
    (scalar-space vector-space point-space simplex n)
  (forall (coefficients)
    (implies
     (and
      (q2226625-scalar-list-p
       scalar-space coefficients (+ 1 (nfix n)))
      (equal
       (q2226625-scalar-sum
        scalar-space coefficients (+ 1 (nfix n)))
       (q2226625-k-zero scalar-space))
      (equal
       (q2226625-weighted-vsub-sum
        scalar-space
        vector-space
        point-space
        simplex
        coefficients
        0
        0
        (+ 1 (nfix n)))
       (q2226625-v-zero vector-space)))
     (q2226625-all-zero-scalars-p
      scalar-space coefficients (+ 1 (nfix n))))))

(defun q2226625-simplex-p
    (scalar-space vector-space point-space simplex n)
  (and
   (q2226625-points-typed-from-p
    point-space simplex 0 (+ 1 (nfix n)))
   (q2226625-simplex-independent-p
    scalar-space vector-space point-space simplex n)))

;; The following two definitions are the uniform affine averages of all
;; vertices and of all vertices except the selected one, respectively.
(defun q2226625-centroid
    (scalar-space vector-space point-space simplex n)
  (q2226625-vadd
   vector-space
   point-space
   (q2226625-v-smul
    scalar-space
    vector-space
    (q2226625-k-inv
     scalar-space
     (q2226625-nat-cast scalar-space (+ 1 (nfix n))))
    (q2226625-vsub-sum
     vector-space
     point-space
     simplex
     0
     0
     (+ 1 (nfix n))))
   (q2226625-point point-space simplex 0)))

(defun q2226625-face-opposite-centroid
    (scalar-space vector-space point-space simplex n index)
  (q2226625-vadd
   vector-space
   point-space
   (q2226625-v-smul
    scalar-space
    vector-space
    (q2226625-k-inv
     scalar-space
     (q2226625-nat-cast scalar-space (nfix n)))
    (q2226625-face-vsub-sum
     vector-space
     point-space
     simplex
     index
     0
     0
     (+ 1 (nfix n))))
   (q2226625-point point-space simplex 0)))

(defun-sk thousand-theorems-q2226625-commandinos-theorem-statement ()
  (forall
    (scalar-space vector-space point-space simplex n index)
    (implies
     (and
      (q2226625-context-p
       scalar-space vector-space point-space)
      (natp n)
      (not (equal n 0))
      (natp index)
      (< index (+ 1 n))
      (q2226625-simplex-p
       scalar-space vector-space point-space simplex n))
     (equal
      (q2226625-vsub
       vector-space
       point-space
       (q2226625-point point-space simplex index)
       (q2226625-centroid
        scalar-space vector-space point-space simplex n))
      (q2226625-v-smul
       scalar-space
       vector-space
       (q2226625-nat-cast scalar-space n)
       (q2226625-vsub
        vector-space
        point-space
        (q2226625-centroid
         scalar-space vector-space point-space simplex n)
        (q2226625-face-opposite-centroid
         scalar-space
         vector-space
         point-space
         simplex
         n
         index)))))))

(value-triple :itpeval-statement-checked)
:q
