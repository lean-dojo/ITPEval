;; Statement-only formalization of Thousand Theorems artifact Q537618,
;; Banach–Alaoglu theorem: the polar of a neighborhood of zero in an arbitrary
;; seminormed space over a proper nontrivially normed field is compact in the
;; weak-star topology on its continuous dual. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Carriers, sets, families of sets, maps, and operations are arbitrary
;; conservative interfaces.  No carrier, set, family, or function is
;; enumerated or represented by a finite table.

(defstub ba-real-p (real-type x) t)
(defstub ba-scalar-p (scalar-type x) t)
(defstub ba-vector-p (vector-type x) t)
(defstub ba-map-p (scalar-type vector-type map) t)

(defstub ba-set-p (carrier-type set) t)
(defstub ba-in (carrier-type set x) t)
(defstub ba-family-p (carrier-type family) t)
(defstub ba-family-in (carrier-type family set) t)

(defstub ba-real-zero (real-type) t)
(defstub ba-real-one (real-type) t)
(defstub ba-real-add (real-type x y) t)
(defstub ba-real-mul (real-type x y) t)
(defstub ba-real-neg (real-type x) t)
(defstub ba-real-inv (real-type x) t)
(defstub ba-real-le (real-type x y) t)
(defstub ba-real-lt (real-type x y) t)

(defstub ba-scalar-zero (scalar-type) t)
(defstub ba-scalar-one (scalar-type) t)
(defstub ba-scalar-add (scalar-type x y) t)
(defstub ba-scalar-mul (scalar-type x y) t)
(defstub ba-scalar-neg (scalar-type x) t)
(defstub ba-scalar-inv (scalar-type x) t)
(defstub ba-scalar-norm (real-type scalar-type x) t)

(defstub ba-vector-zero (vector-type) t)
(defstub ba-vector-add (vector-type x y) t)
(defstub ba-vector-neg (vector-type x) t)
(defstub ba-smul (scalar-type vector-type a x) t)
(defstub ba-vector-norm (real-type vector-type x) t)

(defstub ba-apply (scalar-type vector-type map x) t)
(defstub ba-zero-map (scalar-type vector-type) t)

(defstub ba-scalar-closed-ball
  (real-type scalar-type center radius)
  t)
(defstub ba-polar-set
  (real-type scalar-type vector-type set)
  t)

(defun ba-real-sub (real-type x y)
  (ba-real-add real-type x (ba-real-neg real-type y)))

(defun ba-scalar-sub (scalar-type x y)
  (ba-scalar-add scalar-type x (ba-scalar-neg scalar-type y)))

(defun ba-vector-sub (vector-type x y)
  (ba-vector-add vector-type x (ba-vector-neg vector-type y)))

(defun ba-scalar-dist (real-type scalar-type x y)
  (ba-scalar-norm
   real-type scalar-type (ba-scalar-sub scalar-type x y)))

(defun ba-weakdual-type (scalar-type vector-type)
  (list 'weak-dual scalar-type vector-type))

;; Extensionality preserves source equality for arbitrary sets, families, and
;; functionals.

(defun-sk ba-sets-extensionally-equal-p (carrier-type left right)
  (forall (x)
    (implies
     (or (ba-in carrier-type left x)
         (ba-in carrier-type right x))
     (iff
      (ba-in carrier-type left x)
      (ba-in carrier-type right x)))))

(defun-sk ba-set-extensionality-p (carrier-type)
  (forall (left right)
    (implies
     (and
      (ba-set-p carrier-type left)
      (ba-set-p carrier-type right)
      (ba-sets-extensionally-equal-p carrier-type left right))
     (equal left right))))

(defun-sk ba-families-extensionally-equal-p
    (carrier-type left right)
  (forall (set)
    (implies
     (or
      (ba-family-in carrier-type left set)
      (ba-family-in carrier-type right set))
     (iff
      (ba-family-in carrier-type left set)
      (ba-family-in carrier-type right set)))))

(defun-sk ba-family-extensionality-p (carrier-type)
  (forall (left right)
    (implies
     (and
      (ba-family-p carrier-type left)
      (ba-family-p carrier-type right)
      (ba-families-extensionally-equal-p
       carrier-type left right))
     (equal left right))))

(defun-sk ba-maps-extensionally-equal-p
    (scalar-type vector-type left right)
  (forall (x)
    (implies
     (ba-vector-p vector-type x)
     (equal
      (ba-apply scalar-type vector-type left x)
      (ba-apply scalar-type vector-type right x)))))

(defun-sk ba-map-extensionality-p (scalar-type vector-type)
  (forall (left right)
    (implies
     (and
      (ba-map-p scalar-type vector-type left)
      (ba-map-p scalar-type vector-type right)
      (ba-maps-extensionally-equal-p
       scalar-type vector-type left right))
     (equal left right))))

;; The real-valued norm codomain is an arbitrary complete linearly ordered
;; field, rather than ACL2 rationals.

(defun-sk ba-real-unary-laws-p (real-type)
  (forall (x)
    (implies
     (ba-real-p real-type x)
     (and
      (ba-real-p real-type (ba-real-neg real-type x))
      (ba-real-p real-type (ba-real-inv real-type x))
      (equal
       (ba-real-add real-type x (ba-real-zero real-type))
       x)
      (equal
       (ba-real-add real-type x (ba-real-neg real-type x))
       (ba-real-zero real-type))
      (equal
       (ba-real-mul real-type x (ba-real-one real-type))
       x)
      (implies
       (not (equal x (ba-real-zero real-type)))
       (equal
        (ba-real-mul real-type x (ba-real-inv real-type x))
        (ba-real-one real-type)))
      (ba-real-le real-type x x)))))

(defun-sk ba-real-binary-laws-p (real-type)
  (forall (x y)
    (implies
     (and
      (ba-real-p real-type x)
      (ba-real-p real-type y))
     (and
      (ba-real-p real-type (ba-real-add real-type x y))
      (ba-real-p real-type (ba-real-mul real-type x y))
      (equal
       (ba-real-add real-type x y)
       (ba-real-add real-type y x))
      (equal
       (ba-real-mul real-type x y)
       (ba-real-mul real-type y x))
      (iff
       (ba-real-lt real-type x y)
       (and
        (ba-real-le real-type x y)
        (not (equal x y))))
      (or
       (ba-real-le real-type x y)
       (ba-real-le real-type y x))
      (implies
       (and
        (ba-real-le real-type x y)
        (ba-real-le real-type y x))
       (equal x y))))))

(defun-sk ba-real-ternary-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (ba-real-p real-type x)
      (ba-real-p real-type y)
      (ba-real-p real-type z))
     (and
      (equal
       (ba-real-add
        real-type (ba-real-add real-type x y) z)
       (ba-real-add
        real-type x (ba-real-add real-type y z)))
      (equal
       (ba-real-mul
        real-type (ba-real-mul real-type x y) z)
       (ba-real-mul
        real-type x (ba-real-mul real-type y z)))
      (equal
       (ba-real-mul
        real-type x (ba-real-add real-type y z))
       (ba-real-add
        real-type
        (ba-real-mul real-type x y)
        (ba-real-mul real-type x z)))
      (implies
       (and
        (ba-real-le real-type x y)
        (ba-real-le real-type y z))
       (ba-real-le real-type x z))
      (implies
       (ba-real-le real-type x y)
       (ba-real-le
        real-type
        (ba-real-add real-type x z)
        (ba-real-add real-type y z)))
      (implies
       (and
        (ba-real-le real-type (ba-real-zero real-type) x)
        (ba-real-le real-type (ba-real-zero real-type) y))
       (ba-real-le
        real-type
        (ba-real-zero real-type)
        (ba-real-mul real-type x y)))))))

(defun ba-real-field-order-laws-p (real-type)
  (and
   (ba-real-unary-laws-p real-type)
   (ba-real-binary-laws-p real-type)
   (ba-real-ternary-laws-p real-type)))

(defun-sk ba-real-set-nonempty-p (real-type set)
  (exists (x)
    (and
     (ba-real-p real-type x)
     (ba-in real-type set x))))

(defun-sk ba-real-upper-bound-p (real-type set bound)
  (forall (x)
    (implies
     (and
      (ba-real-p real-type x)
      (ba-in real-type set x))
     (ba-real-le real-type x bound))))

(defun-sk ba-real-set-bounded-above-p (real-type set)
  (exists (bound)
    (and
     (ba-real-p real-type bound)
     (ba-real-upper-bound-p real-type set bound))))

(defun-sk ba-real-least-upper-bound-p
    (real-type set least-upper-bound)
  (forall (bound)
    (implies
     (and
      (ba-real-p real-type bound)
      (ba-real-upper-bound-p real-type set bound))
     (ba-real-le real-type least-upper-bound bound))))

(defun ba-real-is-lub-p (real-type set least-upper-bound)
  (and
   (ba-real-p real-type least-upper-bound)
   (ba-real-upper-bound-p
    real-type set least-upper-bound)
   (ba-real-least-upper-bound-p
    real-type set least-upper-bound)))

(defun-sk ba-real-set-has-lub-p (real-type set)
  (exists (least-upper-bound)
    (ba-real-is-lub-p
     real-type set least-upper-bound)))

(defun-sk ba-real-complete-p (real-type)
  (forall (set)
    (implies
     (and
      (ba-set-p real-type set)
      (ba-real-set-nonempty-p real-type set)
      (ba-real-set-bounded-above-p real-type set))
     (ba-real-set-has-lub-p real-type set))))

(defun ba-real-structure-p (real-type)
  (and
   (ba-real-p real-type (ba-real-zero real-type))
   (ba-real-p real-type (ba-real-one real-type))
   (not
    (equal
     (ba-real-zero real-type)
     (ba-real-one real-type)))
   (ba-real-lt
    real-type
    (ba-real-zero real-type)
    (ba-real-one real-type))
   (ba-real-field-order-laws-p real-type)
   (ba-real-complete-p real-type)
   (ba-set-extensionality-p real-type)
   (ba-family-extensionality-p real-type)))

;; Nontrivially normed field structure.

(defun-sk ba-scalar-field-norm-laws-p (real-type scalar-type)
  (forall (a b c)
    (and
     (implies
      (ba-scalar-p scalar-type a)
      (and
       (ba-scalar-p
        scalar-type (ba-scalar-neg scalar-type a))
       (ba-scalar-p
        scalar-type (ba-scalar-inv scalar-type a))
       (ba-real-p
        real-type (ba-scalar-norm real-type scalar-type a))
       (equal
        (ba-scalar-add
         scalar-type a (ba-scalar-zero scalar-type))
        a)
       (equal
        (ba-scalar-add
         scalar-type a (ba-scalar-neg scalar-type a))
        (ba-scalar-zero scalar-type))
       (equal
        (ba-scalar-mul
         scalar-type a (ba-scalar-one scalar-type))
        a)
       (implies
        (not (equal a (ba-scalar-zero scalar-type)))
        (equal
         (ba-scalar-mul
          scalar-type a (ba-scalar-inv scalar-type a))
         (ba-scalar-one scalar-type)))
       (ba-real-le
        real-type
        (ba-real-zero real-type)
        (ba-scalar-norm real-type scalar-type a))
       (iff
        (equal
         (ba-scalar-norm real-type scalar-type a)
         (ba-real-zero real-type))
        (equal a (ba-scalar-zero scalar-type)))
       (equal
        (ba-scalar-norm
         real-type scalar-type (ba-scalar-neg scalar-type a))
        (ba-scalar-norm real-type scalar-type a))))
     (implies
      (and
       (ba-scalar-p scalar-type a)
       (ba-scalar-p scalar-type b))
      (and
       (ba-scalar-p
        scalar-type (ba-scalar-add scalar-type a b))
       (ba-scalar-p
        scalar-type (ba-scalar-mul scalar-type a b))
       (equal
        (ba-scalar-add scalar-type a b)
        (ba-scalar-add scalar-type b a))
       (equal
        (ba-scalar-mul scalar-type a b)
        (ba-scalar-mul scalar-type b a))
       (equal
        (ba-scalar-norm
         real-type scalar-type (ba-scalar-mul scalar-type a b))
        (ba-real-mul
         real-type
         (ba-scalar-norm real-type scalar-type a)
         (ba-scalar-norm real-type scalar-type b)))
       (ba-real-le
        real-type
        (ba-scalar-norm
         real-type scalar-type (ba-scalar-add scalar-type a b))
        (ba-real-add
         real-type
         (ba-scalar-norm real-type scalar-type a)
         (ba-scalar-norm real-type scalar-type b)))))
     (implies
      (and
       (ba-scalar-p scalar-type a)
       (ba-scalar-p scalar-type b)
       (ba-scalar-p scalar-type c))
      (and
       (equal
        (ba-scalar-add
         scalar-type (ba-scalar-add scalar-type a b) c)
        (ba-scalar-add
         scalar-type a (ba-scalar-add scalar-type b c)))
       (equal
        (ba-scalar-mul
         scalar-type (ba-scalar-mul scalar-type a b) c)
        (ba-scalar-mul
         scalar-type a (ba-scalar-mul scalar-type b c)))
       (equal
        (ba-scalar-mul
         scalar-type a (ba-scalar-add scalar-type b c))
        (ba-scalar-add
         scalar-type
         (ba-scalar-mul scalar-type a b)
         (ba-scalar-mul scalar-type a c))))))))

(defun-sk ba-norm-is-nontrivial-p (real-type scalar-type)
  (exists (a)
    (and
     (ba-scalar-p scalar-type a)
     (ba-real-lt
      real-type
      (ba-real-one real-type)
      (ba-scalar-norm real-type scalar-type a)))))

(defun ba-nontrivially-normed-field-p (real-type scalar-type)
  (and
   (ba-scalar-p scalar-type (ba-scalar-zero scalar-type))
   (ba-scalar-p scalar-type (ba-scalar-one scalar-type))
   (not
    (equal
     (ba-scalar-zero scalar-type)
     (ba-scalar-one scalar-type)))
   (equal
    (ba-scalar-norm
     real-type scalar-type (ba-scalar-one scalar-type))
    (ba-real-one real-type))
   (ba-scalar-field-norm-laws-p real-type scalar-type)
   (ba-norm-is-nontrivial-p real-type scalar-type)
   (ba-set-extensionality-p scalar-type)
   (ba-family-extensionality-p scalar-type)))

;; Seminormed additive commutative group and normed-space laws.

(defun-sk ba-seminormed-module-laws-p
    (real-type scalar-type vector-type)
  (forall (a b x y z)
    (and
     (implies
      (ba-vector-p vector-type x)
      (and
       (ba-vector-p
        vector-type (ba-vector-neg vector-type x))
       (ba-real-p
        real-type (ba-vector-norm real-type vector-type x))
       (equal
        (ba-vector-add
         vector-type x (ba-vector-zero vector-type))
        x)
       (equal
        (ba-vector-add
         vector-type x (ba-vector-neg vector-type x))
        (ba-vector-zero vector-type))
       (ba-real-le
        real-type
        (ba-real-zero real-type)
        (ba-vector-norm real-type vector-type x))
       (equal
        (ba-vector-norm
         real-type vector-type (ba-vector-neg vector-type x))
        (ba-vector-norm real-type vector-type x))))
     (implies
      (and
       (ba-vector-p vector-type x)
       (ba-vector-p vector-type y))
      (and
       (ba-vector-p
        vector-type (ba-vector-add vector-type x y))
       (equal
        (ba-vector-add vector-type x y)
        (ba-vector-add vector-type y x))
       (ba-real-le
        real-type
        (ba-vector-norm
         real-type vector-type (ba-vector-add vector-type x y))
        (ba-real-add
         real-type
         (ba-vector-norm real-type vector-type x)
         (ba-vector-norm real-type vector-type y)))))
     (implies
      (and
       (ba-vector-p vector-type x)
       (ba-vector-p vector-type y)
       (ba-vector-p vector-type z))
      (equal
       (ba-vector-add
        vector-type (ba-vector-add vector-type x y) z)
       (ba-vector-add
        vector-type x (ba-vector-add vector-type y z))))
     (implies
      (and
       (ba-scalar-p scalar-type a)
       (ba-vector-p vector-type x))
      (and
       (ba-vector-p
        vector-type (ba-smul scalar-type vector-type a x))
       (equal
        (ba-vector-norm
         real-type vector-type
         (ba-smul scalar-type vector-type a x))
        (ba-real-mul
         real-type
         (ba-scalar-norm real-type scalar-type a)
         (ba-vector-norm real-type vector-type x)))))
     (implies
      (and
       (ba-scalar-p scalar-type a)
       (ba-vector-p vector-type x)
       (ba-vector-p vector-type y))
      (equal
       (ba-smul
        scalar-type vector-type a
        (ba-vector-add vector-type x y))
       (ba-vector-add
        vector-type
        (ba-smul scalar-type vector-type a x)
        (ba-smul scalar-type vector-type a y))))
     (implies
      (and
       (ba-scalar-p scalar-type a)
       (ba-scalar-p scalar-type b)
       (ba-vector-p vector-type x))
      (and
       (equal
        (ba-smul
         scalar-type vector-type
         (ba-scalar-add scalar-type a b)
         x)
        (ba-vector-add
         vector-type
         (ba-smul scalar-type vector-type a x)
         (ba-smul scalar-type vector-type b x)))
       (equal
        (ba-smul
         scalar-type vector-type
         (ba-scalar-mul scalar-type a b)
         x)
        (ba-smul
         scalar-type vector-type a
         (ba-smul scalar-type vector-type b x)))))
     (implies
      (ba-vector-p vector-type x)
      (equal
       (ba-smul
        scalar-type vector-type (ba-scalar-one scalar-type) x)
       x)))))

(defun ba-seminormed-space-p
    (real-type scalar-type vector-type)
  (and
   (ba-vector-p vector-type (ba-vector-zero vector-type))
   (equal
    (ba-vector-norm
     real-type vector-type (ba-vector-zero vector-type))
    (ba-real-zero real-type))
   (ba-seminormed-module-laws-p
    real-type scalar-type vector-type)
   (ba-set-extensionality-p vector-type)
   (ba-family-extensionality-p vector-type)))

;; Continuous linear maps are represented extensionally.  Boundedness is the
;; standard norm characterization of continuity for linear maps.

(defun-sk ba-linear-map-p
    (scalar-type vector-type map)
  (forall (a x y)
    (and
     (implies
      (ba-vector-p vector-type x)
      (ba-scalar-p
       scalar-type
       (ba-apply scalar-type vector-type map x)))
     (implies
      (and
       (ba-vector-p vector-type x)
       (ba-vector-p vector-type y))
      (equal
       (ba-apply
        scalar-type vector-type map
        (ba-vector-add vector-type x y))
       (ba-scalar-add
        scalar-type
        (ba-apply scalar-type vector-type map x)
        (ba-apply scalar-type vector-type map y))))
     (implies
      (and
       (ba-scalar-p scalar-type a)
       (ba-vector-p vector-type x))
      (equal
       (ba-apply
        scalar-type vector-type map
        (ba-smul scalar-type vector-type a x))
       (ba-scalar-mul
        scalar-type
        a
        (ba-apply scalar-type vector-type map x)))))))

(defun-sk ba-map-bound-p
    (real-type scalar-type vector-type map bound)
  (forall (x)
    (implies
     (ba-vector-p vector-type x)
     (ba-real-le
      real-type
      (ba-scalar-norm
       real-type scalar-type
       (ba-apply scalar-type vector-type map x))
      (ba-real-mul
       real-type
       bound
       (ba-vector-norm real-type vector-type x))))))

(defun-sk ba-bounded-map-p
    (real-type scalar-type vector-type map)
  (exists (bound)
    (and
     (ba-real-p real-type bound)
     (ba-real-le
      real-type (ba-real-zero real-type) bound)
     (ba-map-bound-p
      real-type scalar-type vector-type map bound))))

(defun ba-weakdual-p
    (real-type scalar-type vector-type map)
  (and
   (ba-map-p scalar-type vector-type map)
   (ba-linear-map-p scalar-type vector-type map)
   (ba-bounded-map-p real-type scalar-type vector-type map)))

(defun-sk ba-map-space-laws-p (scalar-type vector-type)
  (forall (x)
    (and
     (ba-map-p
      scalar-type vector-type
      (ba-zero-map scalar-type vector-type))
     (implies
      (ba-vector-p vector-type x)
      (equal
       (ba-apply
        scalar-type vector-type
        (ba-zero-map scalar-type vector-type)
        x)
       (ba-scalar-zero scalar-type))))))

;; Metric openness on the scalar field.

(defun-sk ba-scalar-ball-subset-p
    (real-type scalar-type center radius set)
  (forall (x)
    (implies
     (and
      (ba-scalar-p scalar-type x)
      (ba-real-lt
       real-type
       (ba-scalar-dist real-type scalar-type x center)
       radius))
     (ba-in scalar-type set x))))

(defun-sk ba-scalar-open-at-p
    (real-type scalar-type set center)
  (exists (radius)
    (and
     (ba-real-p real-type radius)
     (ba-real-lt
      real-type (ba-real-zero real-type) radius)
     (ba-scalar-ball-subset-p
      real-type scalar-type center radius set))))

(defun-sk ba-scalar-open-p (real-type scalar-type set)
  (forall (center)
    (implies
     (and
      (ba-scalar-p scalar-type center)
      (ba-in scalar-type set center))
     (ba-scalar-open-at-p
      real-type scalar-type set center))))

;; The weak-star topology is the initial topology generated by every
;; evaluation map f |-> f(x).  A basic neighborhood is a finite intersection
;; of inverse images of scalar-open sets.

(defun ba-weak-basic-data-p
    (real-type scalar-type vector-type basis)
  (if (consp basis)
      (and
       (consp (car basis))
       (ba-vector-p vector-type (caar basis))
       (ba-set-p scalar-type (cdar basis))
       (ba-scalar-open-p
        real-type scalar-type (cdar basis))
       (ba-weak-basic-data-p
        real-type scalar-type vector-type (cdr basis)))
    (equal basis nil)))

(defun ba-weak-basic-contains-p
    (scalar-type vector-type basis map)
  (if (consp basis)
      (and
       (ba-in
        scalar-type
        (cdar basis)
        (ba-apply
         scalar-type vector-type map (caar basis)))
       (ba-weak-basic-contains-p
        scalar-type vector-type (cdr basis) map))
    (equal basis nil)))

(defun-sk ba-weak-basic-subset-p
    (real-type scalar-type vector-type basis set)
  (forall (map)
    (implies
     (and
      (ba-weakdual-p
       real-type scalar-type vector-type map)
      (ba-weak-basic-contains-p
       scalar-type vector-type basis map))
     (ba-in
      (ba-weakdual-type scalar-type vector-type)
      set
      map))))

(defun-sk ba-weak-open-at-p
    (real-type scalar-type vector-type set map)
  (exists (basis)
    (and
     (ba-weak-basic-data-p
      real-type scalar-type vector-type basis)
     (ba-weak-basic-contains-p
      scalar-type vector-type basis map)
     (ba-weak-basic-subset-p
      real-type scalar-type vector-type basis set))))

(defun-sk ba-weak-open-p
    (real-type scalar-type vector-type set)
  (forall (map)
    (implies
     (and
      (ba-weakdual-p
       real-type scalar-type vector-type map)
      (ba-in
       (ba-weakdual-type scalar-type vector-type)
       set
       map))
     (ba-weak-open-at-p
      real-type scalar-type vector-type set map))))

;; Open-cover compactness for the scalar metric topology.

(defun-sk ba-scalar-open-family-p
    (real-type scalar-type family)
  (forall (set)
    (implies
     (ba-family-in scalar-type family set)
     (and
      (ba-set-p scalar-type set)
      (ba-scalar-open-p real-type scalar-type set)))))

(defun-sk ba-scalar-point-covered-p
    (scalar-type family x)
  (exists (set)
    (and
     (ba-family-in scalar-type family set)
     (ba-in scalar-type set x))))

(defun-sk ba-scalar-family-covers-p
    (scalar-type target family)
  (forall (x)
    (implies
     (and
      (ba-scalar-p scalar-type x)
      (ba-in scalar-type target x))
     (ba-scalar-point-covered-p scalar-type family x))))

(defun ba-scalar-subfamily-list-p
    (scalar-type family sets)
  (if (consp sets)
      (and
       (ba-family-in scalar-type family (car sets))
       (ba-scalar-subfamily-list-p
        scalar-type family (cdr sets)))
    (equal sets nil)))

(defun-sk ba-scalar-point-covered-by-list-p
    (scalar-type sets x)
  (exists (set)
    (and
     (member-equal set sets)
     (ba-in scalar-type set x))))

(defun-sk ba-scalar-list-covers-p
    (scalar-type target sets)
  (forall (x)
    (implies
     (and
      (ba-scalar-p scalar-type x)
      (ba-in scalar-type target x))
     (ba-scalar-point-covered-by-list-p
      scalar-type sets x))))

(defun-sk ba-scalar-finite-subcover-p
    (scalar-type target family)
  (exists (sets)
    (and
     (ba-scalar-subfamily-list-p
      scalar-type family sets)
     (ba-scalar-list-covers-p
      scalar-type target sets))))

(defun-sk ba-scalar-compact-p
    (real-type scalar-type target)
  (forall (family)
    (implies
     (and
      (ba-family-p scalar-type family)
      (ba-scalar-open-family-p
       real-type scalar-type family)
      (ba-scalar-family-covers-p
       scalar-type target family))
     (ba-scalar-finite-subcover-p
      scalar-type target family))))

;; Open-cover compactness in the weak-star topology.

(defun-sk ba-weak-open-family-p
    (real-type scalar-type vector-type family)
  (forall (set)
    (implies
     (ba-family-in
      (ba-weakdual-type scalar-type vector-type)
      family
      set)
     (and
      (ba-set-p
       (ba-weakdual-type scalar-type vector-type)
       set)
      (ba-weak-open-p
       real-type scalar-type vector-type set)))))

(defun-sk ba-weak-point-covered-p
    (scalar-type vector-type family map)
  (exists (set)
    (and
     (ba-family-in
      (ba-weakdual-type scalar-type vector-type)
      family
      set)
     (ba-in
      (ba-weakdual-type scalar-type vector-type)
      set
      map))))

(defun-sk ba-weak-family-covers-p
    (real-type scalar-type vector-type target family)
  (forall (map)
    (implies
     (and
      (ba-weakdual-p
       real-type scalar-type vector-type map)
      (ba-in
       (ba-weakdual-type scalar-type vector-type)
       target
       map))
     (ba-weak-point-covered-p
      scalar-type vector-type family map))))

(defun ba-weak-subfamily-list-p
    (scalar-type vector-type family sets)
  (if (consp sets)
      (and
       (ba-family-in
        (ba-weakdual-type scalar-type vector-type)
        family
        (car sets))
       (ba-weak-subfamily-list-p
        scalar-type vector-type family (cdr sets)))
    (equal sets nil)))

(defun-sk ba-weak-point-covered-by-list-p
    (scalar-type vector-type sets map)
  (exists (set)
    (and
     (member-equal set sets)
     (ba-in
      (ba-weakdual-type scalar-type vector-type)
      set
      map))))

(defun-sk ba-weak-list-covers-p
    (real-type scalar-type vector-type target sets)
  (forall (map)
    (implies
     (and
      (ba-weakdual-p
       real-type scalar-type vector-type map)
      (ba-in
       (ba-weakdual-type scalar-type vector-type)
       target
       map))
     (ba-weak-point-covered-by-list-p
      scalar-type vector-type sets map))))

(defun-sk ba-weak-finite-subcover-p
    (real-type scalar-type vector-type target family)
  (exists (sets)
    (and
     (ba-weak-subfamily-list-p
      scalar-type vector-type family sets)
     (ba-weak-list-covers-p
      real-type scalar-type vector-type target sets))))

(defun-sk ba-weak-compact-p
    (real-type scalar-type vector-type target)
  (forall (family)
    (implies
     (and
      (ba-family-p
       (ba-weakdual-type scalar-type vector-type)
       family)
      (ba-weak-open-family-p
       real-type scalar-type vector-type family)
      (ba-weak-family-covers-p
       real-type scalar-type vector-type target family))
     (ba-weak-finite-subcover-p
      real-type scalar-type vector-type target family))))

;; Properness means compactness of every scalar closed ball.  The constructor
;; laws below give closed balls and polars their exact source membership.

(defun-sk ba-scalar-closed-ball-laws-p
    (real-type scalar-type)
  (forall (center radius x)
    (implies
     (and
      (ba-scalar-p scalar-type center)
      (ba-real-p real-type radius))
     (and
      (ba-set-p
       scalar-type
       (ba-scalar-closed-ball
        real-type scalar-type center radius))
      (implies
       (ba-scalar-p scalar-type x)
       (iff
        (ba-in
         scalar-type
         (ba-scalar-closed-ball
          real-type scalar-type center radius)
         x)
        (ba-real-le
         real-type
         (ba-scalar-dist
          real-type scalar-type x center)
         radius)))))))

(defun-sk ba-proper-space-p (real-type scalar-type)
  (forall (center radius)
    (implies
     (and
      (ba-scalar-p scalar-type center)
      (ba-real-p real-type radius))
     (ba-scalar-compact-p
      real-type
      scalar-type
      (ba-scalar-closed-ball
       real-type scalar-type center radius)))))

(defun-sk ba-polar-bound-p
    (real-type scalar-type vector-type set map)
  (forall (x)
    (implies
     (and
      (ba-vector-p vector-type x)
      (ba-in vector-type set x))
     (ba-real-le
      real-type
      (ba-scalar-norm
       real-type scalar-type
       (ba-apply scalar-type vector-type map x))
      (ba-real-one real-type)))))

(defun-sk ba-polar-set-laws-p
    (real-type scalar-type vector-type)
  (forall (set map)
    (implies
     (ba-set-p vector-type set)
     (and
      (ba-set-p
       (ba-weakdual-type scalar-type vector-type)
       (ba-polar-set
        real-type scalar-type vector-type set))
      (implies
       (ba-map-p scalar-type vector-type map)
       (iff
        (ba-in
         (ba-weakdual-type scalar-type vector-type)
         (ba-polar-set
          real-type scalar-type vector-type set)
         map)
        (and
         (ba-weakdual-p
          real-type scalar-type vector-type map)
         (ba-polar-bound-p
          real-type scalar-type vector-type set map))))))))

(defun-sk ba-vector-ball-subset-p
    (real-type vector-type radius set)
  (forall (x)
    (implies
     (and
      (ba-vector-p vector-type x)
      (ba-real-lt
       real-type
       (ba-vector-norm real-type vector-type x)
       radius))
     (ba-in vector-type set x))))

(defun-sk ba-neighborhood-of-zero-p
    (real-type vector-type set)
  (exists (radius)
    (and
     (ba-real-p real-type radius)
     (ba-real-lt
      real-type (ba-real-zero real-type) radius)
     (ba-vector-ball-subset-p
      real-type vector-type radius set))))

(defun ba-banach-alaoglu-context-p
    (real-type scalar-type vector-type)
  (and
   (ba-real-structure-p real-type)
   (ba-nontrivially-normed-field-p real-type scalar-type)
   (ba-seminormed-space-p
    real-type scalar-type vector-type)
   (ba-map-extensionality-p scalar-type vector-type)
   (ba-map-space-laws-p scalar-type vector-type)
   (ba-set-extensionality-p
    (ba-weakdual-type scalar-type vector-type))
   (ba-family-extensionality-p
    (ba-weakdual-type scalar-type vector-type))
   (ba-scalar-closed-ball-laws-p real-type scalar-type)
   (ba-polar-set-laws-p
    real-type scalar-type vector-type)
   (ba-proper-space-p real-type scalar-type)))

(defun-sk thousand-theorems-q537618-statement ()
  (forall (real-type scalar-type vector-type set)
    (implies
     (and
      (ba-banach-alaoglu-context-p
       real-type scalar-type vector-type)
      (ba-set-p vector-type set)
      (ba-neighborhood-of-zero-p
       real-type vector-type set))
     (ba-weak-compact-p
      real-type
      scalar-type
      vector-type
      (ba-polar-set
       real-type scalar-type vector-type set)))))

(value-triple :itpeval-statement-checked)
:q
