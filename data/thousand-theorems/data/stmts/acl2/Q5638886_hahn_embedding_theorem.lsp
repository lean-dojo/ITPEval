;; Statement-only formalization of thousand-theorems corpus artifact Q5638886,
;; "Hahn embedding theorem": every linearly ordered abelian group embeds
;; injectively and additively into the lexicographically ordered real Hahn
;; series on its finite Archimedean classes, preserving Archimedean class as
;; the least nonzero coefficient index. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Structure tags index arbitrary carriers.  Every group, ordered-field,
;; quotient, support, and embedding law used below is explicit in the final
;; predicate.

(defstub q5638886-m-member-p (group value) t)
(defstub q5638886-m-zero (group) t)
(defstub q5638886-m-add (group left right) t)
(defstub q5638886-m-negate (group value) t)
(defstub q5638886-m-leq (group left right) t)

(defstub q5638886-r-member-p (real value) t)
(defstub q5638886-r-zero (real) t)
(defstub q5638886-r-one (real) t)
(defstub q5638886-r-add (real left right) t)
(defstub q5638886-r-multiply (real left right) t)
(defstub q5638886-r-negate (real value) t)
(defstub q5638886-r-inverse (real value) t)
(defstub q5638886-r-leq (real left right) t)

(defun q5638886-unary-value (function argument)
  (apply$ function (list argument)))

(defun q5638886-m-abs (group value)
  (if (q5638886-m-leq group (q5638886-m-zero group) value)
      value
    (q5638886-m-negate group value)))

(defun q5638886-m-nsmul (group n value)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q5638886-m-zero group)
    (q5638886-m-add
     group
     value
     (q5638886-m-nsmul group (1- n) value))))

(defun q5638886-r-nat (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q5638886-r-zero real)
    (q5638886-r-add
     real
     (q5638886-r-one real)
     (q5638886-r-nat real (1- n)))))

(defun q5638886-r-less (real left right)
  (and
   (q5638886-r-leq real left right)
   (not (equal left right))))

;; The source domain is an arbitrary linearly ordered additive commutative
;; group.

(defun-sk q5638886-ordered-abelian-group-laws-p (group)
  (forall (x y z)
    (and
     (implies
      (q5638886-m-member-p group x)
      (and
       (q5638886-m-member-p
        group (q5638886-m-negate group x))
       (equal
        (q5638886-m-add group x (q5638886-m-zero group))
        x)
       (equal
        (q5638886-m-add group (q5638886-m-zero group) x)
        x)
       (equal
        (q5638886-m-add
         group x (q5638886-m-negate group x))
        (q5638886-m-zero group))
       (equal
        (q5638886-m-add
         group (q5638886-m-negate group x) x)
        (q5638886-m-zero group))
       (q5638886-m-leq group x x)))
     (implies
      (and
       (q5638886-m-member-p group x)
       (q5638886-m-member-p group y))
      (and
       (q5638886-m-member-p
        group (q5638886-m-add group x y))
       (equal
        (q5638886-m-add group x y)
        (q5638886-m-add group y x))
       (or
        (q5638886-m-leq group x y)
        (q5638886-m-leq group y x))
       (implies
        (and
         (q5638886-m-leq group x y)
         (q5638886-m-leq group y x))
        (equal x y))))
     (implies
      (and
       (q5638886-m-member-p group x)
       (q5638886-m-member-p group y)
       (q5638886-m-member-p group z))
      (and
       (equal
        (q5638886-m-add
         group
         (q5638886-m-add group x y)
         z)
        (q5638886-m-add
         group
         x
         (q5638886-m-add group y z)))
       (implies
        (and
         (q5638886-m-leq group x y)
         (q5638886-m-leq group y z))
        (q5638886-m-leq group x z))
       (implies
        (q5638886-m-leq group x y)
        (q5638886-m-leq
         group
         (q5638886-m-add group z x)
         (q5638886-m-add group z y))))))))

(defun q5638886-ordered-abelian-group-p (group)
  (and
   (q5638886-m-member-p group (q5638886-m-zero group))
   (q5638886-ordered-abelian-group-laws-p group)))

;; A Dedekind-complete ordered field is a presentation of the real field.

(defun-sk q5638886-real-field-algebra-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q5638886-r-member-p real x)
      (q5638886-r-member-p real y)
      (q5638886-r-member-p real z))
     (let ((zero (q5638886-r-zero real))
           (one (q5638886-r-one real)))
       (and
        (q5638886-r-member-p
         real (q5638886-r-add real x y))
        (q5638886-r-member-p
         real (q5638886-r-multiply real x y))
        (q5638886-r-member-p
         real (q5638886-r-negate real x))
        (q5638886-r-member-p
         real (q5638886-r-inverse real x))
        (equal
         (q5638886-r-add
          real (q5638886-r-add real x y) z)
         (q5638886-r-add
          real x (q5638886-r-add real y z)))
        (equal
         (q5638886-r-add real x y)
         (q5638886-r-add real y x))
        (equal (q5638886-r-add real x zero) x)
        (equal
         (q5638886-r-add
          real x (q5638886-r-negate real x))
         zero)
        (equal
         (q5638886-r-multiply
          real (q5638886-r-multiply real x y) z)
         (q5638886-r-multiply
          real x (q5638886-r-multiply real y z)))
        (equal
         (q5638886-r-multiply real x y)
         (q5638886-r-multiply real y x))
        (equal (q5638886-r-multiply real x one) x)
        (equal (q5638886-r-multiply real x zero) zero)
        (equal (q5638886-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q5638886-r-multiply
           real x (q5638886-r-inverse real x))
          one))
        (equal
         (q5638886-r-multiply
          real x (q5638886-r-add real y z))
         (q5638886-r-add
          real
          (q5638886-r-multiply real x y)
          (q5638886-r-multiply real x z))))))))

(defun-sk q5638886-real-field-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q5638886-r-member-p real x)
      (q5638886-r-member-p real y)
      (q5638886-r-member-p real z))
     (let ((zero (q5638886-r-zero real)))
       (and
        (q5638886-r-leq real x x)
        (implies
         (and
          (q5638886-r-leq real x y)
          (q5638886-r-leq real y z))
         (q5638886-r-leq real x z))
        (implies
         (and
          (q5638886-r-leq real x y)
          (q5638886-r-leq real y x))
         (equal x y))
        (or
         (q5638886-r-leq real x y)
         (q5638886-r-leq real y x))
        (implies
         (q5638886-r-leq real x y)
         (q5638886-r-leq
          real
          (q5638886-r-add real z x)
          (q5638886-r-add real z y)))
        (implies
         (and
          (q5638886-r-leq real zero x)
          (q5638886-r-leq real zero y))
         (q5638886-r-leq
          real
          zero
          (q5638886-r-multiply real x y))))))))

(defun-sk q5638886-real-set-nonempty-p (real set)
  (exists (x)
    (and
     (q5638886-r-member-p real x)
     (q5638886-unary-value set x))))

(defun-sk q5638886-real-upper-bound-p (real set upper)
  (forall (x)
    (implies
     (and
      (q5638886-r-member-p real x)
      (q5638886-unary-value set x))
     (q5638886-r-leq real x upper))))

(defun-sk q5638886-real-upper-bound-exists-p (real set)
  (exists (upper)
    (and
     (q5638886-r-member-p real upper)
     (q5638886-real-upper-bound-p real set upper))))

(defun-sk q5638886-real-least-upper-bound-p
    (real set supremum)
  (forall (upper)
    (implies
     (and
      (q5638886-r-member-p real upper)
      (q5638886-real-upper-bound-p real set upper))
     (q5638886-r-leq real supremum upper))))

(defun-sk q5638886-real-supremum-exists-p (real set)
  (exists (supremum)
    (and
     (q5638886-r-member-p real supremum)
     (q5638886-real-upper-bound-p real set supremum)
     (q5638886-real-least-upper-bound-p
      real set supremum))))

(defun-sk q5638886-real-complete-p (real)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (q5638886-real-set-nonempty-p real set)
      (q5638886-real-upper-bound-exists-p real set))
     (q5638886-real-supremum-exists-p real set))))

(defun-sk q5638886-real-archimedean-bound-exists-p
    (real x)
  (exists (n)
    (and
     (natp n)
     (q5638886-r-leq real x (q5638886-r-nat real n)))))

(defun-sk q5638886-real-archimedean-p (real)
  (forall (x)
    (implies
     (q5638886-r-member-p real x)
     (q5638886-real-archimedean-bound-exists-p real x))))

(defun q5638886-real-field-p (real)
  (let ((zero (q5638886-r-zero real))
        (one (q5638886-r-one real)))
    (and
     (q5638886-r-member-p real zero)
     (q5638886-r-member-p real one)
     (not (equal zero one))
     (q5638886-r-less real zero one)
     (q5638886-real-field-algebra-laws-p real)
     (q5638886-real-field-order-laws-p real)
     (q5638886-real-complete-p real)
     (q5638886-real-archimedean-p real))))

;; Finite Archimedean classes are presented by nonzero group elements modulo
;; mutual domination.  The order is the source order: A <= B when a natural
;; multiple of a representative of A dominates a representative of B.

(defun-sk q5638886-class-leq-p (group left right)
  (exists (n)
    (and
     (natp n)
     (q5638886-m-leq
      group
      (q5638886-m-abs group right)
      (q5638886-m-nsmul
       group n (q5638886-m-abs group left))))))

(defun q5638886-class-equivalent-p (group left right)
  (and
   (q5638886-class-leq-p group left right)
   (q5638886-class-leq-p group right left)))

(defun q5638886-class-less-p (group left right)
  (and
   (q5638886-class-leq-p group left right)
   (not (q5638886-class-leq-p group right left))))

;; A real Hahn series on the quotient of nonzero elements by Archimedean
;; equivalence is represented by a tame coefficient function on nonzero
;; representatives, constant on each equivalence class.

(defun q5638886-coeff (series index)
  (q5638886-unary-value series index))

(defun q5638886-support-member-p (real series index)
  (not
   (equal
    (q5638886-coeff series index)
    (q5638886-r-zero real))))

(defun-sk q5638886-series-coefficient-laws-p
    (group real series)
  (forall (left right)
    (and
     (implies
      (and
       (q5638886-m-member-p group left)
       (not (equal left (q5638886-m-zero group))))
      (q5638886-r-member-p
       real (q5638886-coeff series left)))
     (implies
      (and
       (q5638886-m-member-p group left)
       (q5638886-m-member-p group right)
       (not (equal left (q5638886-m-zero group)))
       (not (equal right (q5638886-m-zero group)))
       (q5638886-class-equivalent-p group left right))
      (equal
       (q5638886-coeff series left)
       (q5638886-coeff series right))))))

(defun-sk q5638886-support-subset-laws-p
    (group real series subset)
  (forall (left right)
    (and
     (implies
      (q5638886-unary-value subset left)
      (and
       (q5638886-m-member-p group left)
       (not (equal left (q5638886-m-zero group)))
       (q5638886-support-member-p real series left)))
     (implies
      (and
       (q5638886-m-member-p group left)
       (q5638886-m-member-p group right)
       (not (equal left (q5638886-m-zero group)))
       (not (equal right (q5638886-m-zero group)))
       (q5638886-class-equivalent-p group left right))
      (iff
       (q5638886-unary-value subset left)
       (q5638886-unary-value subset right))))))

(defun-sk q5638886-support-subset-nonempty-p (subset)
  (exists (index)
    (q5638886-unary-value subset index)))

(defun-sk q5638886-support-subset-least-p
    (group subset least)
  (forall (index)
    (implies
     (q5638886-unary-value subset index)
     (q5638886-class-leq-p group least index))))

(defun-sk q5638886-support-subset-least-exists-p
    (group subset)
  (exists (least)
    (and
     (q5638886-unary-value subset least)
     (q5638886-support-subset-least-p
      group subset least))))

(defun-sk q5638886-support-well-ordered-p
    (group real series)
  (forall (subset)
    (implies
     (and
      (tamep-functionp subset)
      (q5638886-support-subset-laws-p
       group real series subset)
      (q5638886-support-subset-nonempty-p subset))
     (q5638886-support-subset-least-exists-p
      group subset))))

(defun q5638886-hahn-series-p (group real series)
  (and
   (tamep-functionp series)
   (q5638886-series-coefficient-laws-p
    group real series)
   (q5638886-support-well-ordered-p
    group real series)))

;; Extensional equality and the lexicographic order are defined directly on
;; the quotient-indexed coefficient functions.

(defun-sk q5638886-series-equal-p (group left right)
  (forall (index)
    (implies
     (and
      (q5638886-m-member-p group index)
      (not (equal index (q5638886-m-zero group))))
     (equal
      (q5638886-coeff left index)
      (q5638886-coeff right index)))))

(defun-sk q5638886-series-equal-below-p
    (group left right pivot)
  (forall (index)
    (implies
     (and
      (q5638886-m-member-p group index)
      (not (equal index (q5638886-m-zero group)))
      (q5638886-class-less-p group index pivot))
     (equal
      (q5638886-coeff left index)
      (q5638886-coeff right index)))))

(defun-sk q5638886-hahn-less-p
    (group real left right)
  (exists (pivot)
    (and
     (q5638886-m-member-p group pivot)
     (not (equal pivot (q5638886-m-zero group)))
     (q5638886-series-equal-below-p
      group left right pivot)
     (q5638886-r-less
      real
      (q5638886-coeff left pivot)
      (q5638886-coeff right pivot)))))

(defun q5638886-hahn-leq-p (group real left right)
  (or
   (q5638886-series-equal-p group left right)
   (q5638886-hahn-less-p group real left right)))

(defun-sk q5638886-zero-series-p (group real series)
  (forall (index)
    (implies
     (and
      (q5638886-m-member-p group index)
      (not (equal index (q5638886-m-zero group))))
     (equal
      (q5638886-coeff series index)
      (q5638886-r-zero real)))))

(defun-sk q5638886-series-sum-p
    (group real left right sum)
  (forall (index)
    (implies
     (and
      (q5638886-m-member-p group index)
      (not (equal index (q5638886-m-zero group))))
     (equal
      (q5638886-coeff sum index)
      (q5638886-r-add
       real
       (q5638886-coeff left index)
       (q5638886-coeff right index))))))

;; ORDER-TOP equals the class of A exactly when the A-coordinate is nonzero
;; and that class is below every support class.  The zero series has top
;; order, matching the Archimedean class of the group zero.

(defun-sk q5638886-support-minimum-class-p
    (group real series representative)
  (forall (index)
    (implies
     (and
      (q5638886-m-member-p group index)
      (not (equal index (q5638886-m-zero group)))
      (q5638886-support-member-p real series index))
     (q5638886-class-leq-p
      group representative index))))

(defun q5638886-preserves-archimedean-class-p
    (group real series value)
  (if (equal value (q5638886-m-zero group))
      (q5638886-zero-series-p group real series)
    (and
     (q5638886-support-member-p real series value)
     (q5638886-support-minimum-class-p
      group real series value))))

;; These are precisely the carrier, zero, addition, monotonicity,
;; injectivity, and class-preservation fields of the required injective
;; OrderAddMonoidHom.

(defun-sk q5638886-embedding-laws-p
    (group real embedding)
  (forall (x y)
    (let ((fx (q5638886-unary-value embedding x))
          (fy (q5638886-unary-value embedding y)))
      (and
       (implies
        (q5638886-m-member-p group x)
        (and
         (q5638886-hahn-series-p group real fx)
         (q5638886-preserves-archimedean-class-p
          group real fx x)))
       (implies
        (and
         (q5638886-m-member-p group x)
         (q5638886-m-member-p group y))
        (and
         (q5638886-series-sum-p
          group
          real
          fx
          fy
          (q5638886-unary-value
           embedding
           (q5638886-m-add group x y)))
         (implies
          (q5638886-m-leq group x y)
          (q5638886-hahn-leq-p
           group real fx fy))
         (implies
          (q5638886-series-equal-p group fx fy)
          (equal x y))))))))

(defun q5638886-hahn-embedding-p
    (group real embedding)
  (and
   (tamep-functionp embedding)
   (q5638886-zero-series-p
    group
    real
    (q5638886-unary-value
     embedding (q5638886-m-zero group)))
   (q5638886-embedding-laws-p
    group real embedding)))

(defun-sk q5638886-hahn-embedding-exists-p (group real)
  (exists (embedding)
    (q5638886-hahn-embedding-p
     group real embedding)))

(defun-sk
    thousand-theorems-q5638886-hahn-embedding-theorem-statement
    ()
  (forall (group real)
    (implies
     (and
      (q5638886-ordered-abelian-group-p group)
      (q5638886-real-field-p real))
     (q5638886-hahn-embedding-exists-p group real))))

(value-triple :itpeval-statement-checked)
:q
