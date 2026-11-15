;; Statement-only formalization of thousand-theorems corpus artifact Q1660147,
;; "Mazur–Ulam theorem": every isometric equivalence between real normed
;; affine spaces is an affine isometry equivalence with the same underlying
;; map. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative application interfaces present arbitrary carriers and
;; operations. The real scalars are represented by a Dedekind-complete
;; ordered field. The two vector spaces, their affine torsors, the input
;; isometric equivalence, and every law used in the conclusion are explicit.

(defstub q1660147-apply1 (function x) t)
(defstub q1660147-apply2 (function x y) t)

(defun q1660147-member-p (carrier x)
  (if (q1660147-apply1 carrier x) t nil))

;; A presentation of the real numbers as a complete ordered field.

(defun-sk q1660147-real-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (q1660147-member-p carrier x)
      (q1660147-member-p carrier y)
      (q1660147-member-p carrier z))
     (let* ((xy-add (q1660147-apply2 add x y))
            (yz-add (q1660147-apply2 add y z))
            (xy-multiply (q1660147-apply2 multiply x y))
            (yz-multiply (q1660147-apply2 multiply y z))
            (negative-x (q1660147-apply1 negate x))
            (inverse-x (q1660147-apply1 inverse x)))
       (and
        (q1660147-member-p carrier xy-add)
        (q1660147-member-p carrier xy-multiply)
        (q1660147-member-p carrier negative-x)
        (q1660147-member-p carrier inverse-x)
        (equal
         (q1660147-apply2 add xy-add z)
         (q1660147-apply2 add x yz-add))
        (equal xy-add (q1660147-apply2 add y x))
        (equal (q1660147-apply2 add x zero) x)
        (equal (q1660147-apply2 add x negative-x) zero)
        (equal
         (q1660147-apply2 multiply xy-multiply z)
         (q1660147-apply2 multiply x yz-multiply))
        (equal xy-multiply (q1660147-apply2 multiply y x))
        (equal (q1660147-apply2 multiply x one) x)
        (equal (q1660147-apply1 inverse zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q1660147-apply2 multiply x inverse-x)
          one))
        (equal
         (q1660147-apply2 multiply x yz-add)
         (q1660147-apply2
          add
          (q1660147-apply2 multiply x y)
          (q1660147-apply2 multiply x z))))))))

(defun-sk q1660147-real-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (q1660147-member-p carrier x)
      (q1660147-member-p carrier y)
      (q1660147-member-p carrier z))
     (and
      (not (q1660147-apply2 less x x))
      (or
       (equal x y)
       (q1660147-apply2 less x y)
       (q1660147-apply2 less y x))
      (implies
       (and
        (q1660147-apply2 less x y)
        (q1660147-apply2 less y z))
       (q1660147-apply2 less x z))
      (implies
       (q1660147-apply2 less x y)
       (q1660147-apply2
        less
        (q1660147-apply2 add x z)
        (q1660147-apply2 add y z)))
      (implies
       (and
        (q1660147-apply2 less zero x)
        (q1660147-apply2 less zero y))
       (q1660147-apply2
        less zero (q1660147-apply2 multiply x y)))))))

(defun q1660147-real-leq-p (less left right)
  (not (q1660147-apply2 less right left)))

(defun-sk q1660147-real-set-valid-p (carrier set)
  (forall (x)
    (implies
     (q1660147-apply1 set x)
     (q1660147-member-p carrier x))))

(defun-sk q1660147-real-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (q1660147-member-p carrier x)
     (q1660147-apply1 set x))))

(defun-sk q1660147-real-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (q1660147-member-p carrier x)
      (q1660147-apply1 set x))
     (q1660147-real-leq-p less x bound))))

(defun-sk q1660147-real-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (q1660147-member-p carrier bound)
     (q1660147-real-upper-bound-p
      carrier less set bound))))

(defun-sk q1660147-real-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (q1660147-member-p carrier bound)
      (q1660147-real-upper-bound-p
       carrier less set bound))
     (q1660147-real-leq-p less supremum bound))))

(defun q1660147-real-supremum-p
    (carrier less set supremum)
  (and
   (q1660147-member-p carrier supremum)
   (q1660147-real-upper-bound-p
    carrier less set supremum)
   (q1660147-real-least-upper-bound-p
    carrier less set supremum)))

(defun-sk q1660147-real-supremum-exists-p
    (carrier less set)
  (exists (supremum)
    (q1660147-real-supremum-p
     carrier less set supremum)))

(defun-sk q1660147-real-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (q1660147-real-set-valid-p carrier set)
      (q1660147-real-set-nonempty-p carrier set)
      (q1660147-real-bounded-above-p carrier less set))
     (q1660147-real-supremum-exists-p
      carrier less set))))

(defun q1660147-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (q1660147-member-p carrier zero)
   (q1660147-member-p carrier one)
   (not (equal zero one))
   (q1660147-apply2 less zero one)
   (q1660147-real-field-laws-p
    carrier zero one add multiply negate inverse)
   (q1660147-real-order-laws-p
    carrier zero add multiply less)
   (q1660147-real-complete-p carrier less)))

(defun q1660147-real-abs
    (zero negate less value)
  (if (q1660147-apply2 less value zero)
      (q1660147-apply1 negate value)
    value))

;; Normed vector spaces over the presented real field.

(defun-sk q1660147-vector-space-laws-p
    (real-carrier real-zero real-one real-add real-multiply
     vector-carrier vector-zero vector-add vector-negate scalar-multiply)
  (forall (a b x y z)
    (implies
     (and
      (q1660147-member-p real-carrier a)
      (q1660147-member-p real-carrier b)
      (q1660147-member-p vector-carrier x)
      (q1660147-member-p vector-carrier y)
      (q1660147-member-p vector-carrier z))
     (let* ((xy-add (q1660147-apply2 vector-add x y))
            (yz-add (q1660147-apply2 vector-add y z))
            (negative-x (q1660147-apply1 vector-negate x))
            (a-times-x
             (q1660147-apply2 scalar-multiply a x))
            (b-times-x
             (q1660147-apply2 scalar-multiply b x)))
       (and
        (q1660147-member-p vector-carrier xy-add)
        (q1660147-member-p vector-carrier negative-x)
        (q1660147-member-p vector-carrier a-times-x)
        (equal
         (q1660147-apply2 vector-add xy-add z)
         (q1660147-apply2 vector-add x yz-add))
        (equal xy-add (q1660147-apply2 vector-add y x))
        (equal (q1660147-apply2 vector-add x vector-zero) x)
        (equal
         (q1660147-apply2 vector-add x negative-x)
         vector-zero)
        (equal
         (q1660147-apply2 scalar-multiply real-one x)
         x)
        (equal
         (q1660147-apply2
          scalar-multiply
          (q1660147-apply2 real-multiply a b)
          x)
         (q1660147-apply2
          scalar-multiply a b-times-x))
        (equal
         (q1660147-apply2
          scalar-multiply
          (q1660147-apply2 real-add a b)
          x)
         (q1660147-apply2
          vector-add a-times-x b-times-x))
        (equal
         (q1660147-apply2 scalar-multiply a xy-add)
         (q1660147-apply2
          vector-add
          (q1660147-apply2 scalar-multiply a x)
          (q1660147-apply2 scalar-multiply a y)))
        (equal
         (q1660147-apply2 scalar-multiply real-zero x)
         vector-zero))))))

(defun-sk q1660147-norm-laws-p
    (real-carrier real-zero real-add real-multiply real-negate real-less
     vector-carrier vector-zero vector-add scalar-multiply norm)
  (forall (a x y)
    (implies
     (and
      (q1660147-member-p real-carrier a)
      (q1660147-member-p vector-carrier x)
      (q1660147-member-p vector-carrier y))
     (let ((norm-x (q1660147-apply1 norm x))
           (norm-y (q1660147-apply1 norm y))
           (norm-xy
            (q1660147-apply1
             norm (q1660147-apply2 vector-add x y))))
       (and
        (q1660147-member-p real-carrier norm-x)
        (q1660147-real-leq-p real-less real-zero norm-x)
        (iff (equal norm-x real-zero)
             (equal x vector-zero))
        (q1660147-real-leq-p
         real-less
         norm-xy
         (q1660147-apply2 real-add norm-x norm-y))
        (equal
         (q1660147-apply1
          norm
          (q1660147-apply2 scalar-multiply a x))
         (q1660147-apply2
          real-multiply
          (q1660147-real-abs
           real-zero real-negate real-less a)
          norm-x)))))))

(defun q1660147-normed-real-vector-space-p
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-less
     vector-carrier vector-zero vector-add vector-negate
     scalar-multiply norm)
  (and
   (q1660147-member-p vector-carrier vector-zero)
   (q1660147-vector-space-laws-p
    real-carrier real-zero real-one real-add real-multiply
    vector-carrier vector-zero vector-add vector-negate scalar-multiply)
   (q1660147-norm-laws-p
    real-carrier real-zero real-add real-multiply real-negate real-less
    vector-carrier vector-zero vector-add scalar-multiply norm)))

;; Normed affine spaces, represented as additive torsors whose point distance
;; is the norm of the vector difference.

(defun-sk q1660147-torsor-laws-p
    (vector-carrier vector-zero vector-add
     point-carrier vector-add-point point-subtract)
  (forall (v w p q)
    (implies
     (and
      (q1660147-member-p vector-carrier v)
      (q1660147-member-p vector-carrier w)
      (q1660147-member-p point-carrier p)
      (q1660147-member-p point-carrier q))
     (let ((v-plus-p
            (q1660147-apply2 vector-add-point v p))
           (p-minus-q
            (q1660147-apply2 point-subtract p q)))
       (and
        (q1660147-member-p point-carrier v-plus-p)
        (q1660147-member-p vector-carrier p-minus-q)
        (equal
         (q1660147-apply2 vector-add-point vector-zero p)
         p)
        (equal
         (q1660147-apply2
          vector-add-point
          (q1660147-apply2 vector-add v w)
          p)
         (q1660147-apply2
          vector-add-point
          v
          (q1660147-apply2 vector-add-point w p)))
        (equal
         (q1660147-apply2
          vector-add-point p-minus-q q)
         p)
        (equal
         (q1660147-apply2
          point-subtract v-plus-p p)
         v))))))

(defun-sk q1660147-point-carrier-nonempty-p (point-carrier)
  (exists (p)
    (q1660147-member-p point-carrier p)))

(defun q1660147-normed-affine-space-p
    (vector-carrier vector-zero vector-add
     point-carrier vector-add-point point-subtract)
  (and
   (q1660147-point-carrier-nonempty-p point-carrier)
   (q1660147-torsor-laws-p
    vector-carrier vector-zero vector-add
    point-carrier vector-add-point point-subtract)))

(defun q1660147-point-distance
    (norm point-subtract p q)
  (q1660147-apply1
   norm (q1660147-apply2 point-subtract p q)))

;; The source object f : PE ≃ᵢ PF is represented by a mutually inverse pair
;; of maps. Its isometry field is the equality of all point distances.

(defun-sk q1660147-map-points-p
    (source-carrier target-carrier map)
  (forall (p)
    (implies
     (q1660147-member-p source-carrier p)
     (q1660147-member-p
      target-carrier (q1660147-apply1 map p)))))

(defun-sk q1660147-maps-inverse-p
    (source-carrier target-carrier map inverse-map)
  (forall (p q)
    (and
     (implies
      (q1660147-member-p source-carrier p)
      (equal
       (q1660147-apply1
        inverse-map (q1660147-apply1 map p))
       p))
     (implies
      (q1660147-member-p target-carrier q)
      (equal
       (q1660147-apply1
        map (q1660147-apply1 inverse-map q))
       q)))))

(defun-sk q1660147-map-isometry-p
    (source-carrier source-norm source-point-subtract
     target-norm target-point-subtract map)
  (forall (p q)
    (implies
     (and
      (q1660147-member-p source-carrier p)
      (q1660147-member-p source-carrier q))
     (equal
      (q1660147-point-distance
       target-norm target-point-subtract
       (q1660147-apply1 map p)
       (q1660147-apply1 map q))
      (q1660147-point-distance
       source-norm source-point-subtract p q)))))

(defun q1660147-isometry-equivalence-p
    (source-carrier source-norm source-point-subtract
     target-carrier target-norm target-point-subtract
     map inverse-map)
  (and
   (q1660147-map-points-p source-carrier target-carrier map)
   (q1660147-map-points-p target-carrier source-carrier inverse-map)
   (q1660147-maps-inverse-p
    source-carrier target-carrier map inverse-map)
   (q1660147-map-isometry-p
    source-carrier source-norm source-point-subtract
    target-norm target-point-subtract map)))

;; An internally quantified linear isometry equivalence is the linear part of
;; the affine lift. Keeping this witness existential preserves the source
;; theorem's quantifier scope.

(defun-sk q1660147-linear-map-laws-p
    (real-carrier
     source-carrier source-add source-scalar-multiply
     target-carrier target-add target-scalar-multiply linear-map)
  (forall (a x y)
    (implies
     (and
      (q1660147-member-p real-carrier a)
      (q1660147-member-p source-carrier x)
      (q1660147-member-p source-carrier y))
     (and
      (q1660147-member-p
       target-carrier (q1660147-apply1 linear-map x))
      (equal
       (q1660147-apply1
        linear-map (q1660147-apply2 source-add x y))
       (q1660147-apply2
        target-add
        (q1660147-apply1 linear-map x)
        (q1660147-apply1 linear-map y)))
      (equal
       (q1660147-apply1
        linear-map
        (q1660147-apply2 source-scalar-multiply a x))
       (q1660147-apply2
        target-scalar-multiply
        a
        (q1660147-apply1 linear-map x)))))))

(defun-sk q1660147-linear-norm-preserving-p
    (source-carrier source-norm target-norm linear-map)
  (forall (x)
    (implies
     (q1660147-member-p source-carrier x)
     (equal
      (q1660147-apply1
       target-norm (q1660147-apply1 linear-map x))
      (q1660147-apply1 source-norm x)))))

(defun q1660147-linear-isometry-equivalence-p
    (real-carrier
     source-carrier source-add source-scalar-multiply source-norm
     target-carrier target-add target-scalar-multiply target-norm
     linear-map linear-inverse)
  (and
   (q1660147-linear-map-laws-p
    real-carrier
    source-carrier source-add source-scalar-multiply
    target-carrier target-add target-scalar-multiply linear-map)
   (q1660147-linear-map-laws-p
    real-carrier
    target-carrier target-add target-scalar-multiply
    source-carrier source-add source-scalar-multiply linear-inverse)
   (q1660147-maps-inverse-p
    source-carrier target-carrier linear-map linear-inverse)
   (q1660147-linear-norm-preserving-p
    source-carrier source-norm target-norm linear-map)))

(defun-sk q1660147-affine-compatibility-p
    (source-vector-carrier source-point-carrier source-vector-add-point
     target-vector-add-point map linear-map)
  (forall (v p)
    (implies
     (and
      (q1660147-member-p source-vector-carrier v)
      (q1660147-member-p source-point-carrier p))
     (equal
      (q1660147-apply1
       map
       (q1660147-apply2 source-vector-add-point v p))
      (q1660147-apply2
       target-vector-add-point
       (q1660147-apply1 linear-map v)
       (q1660147-apply1 map p))))))

(defun q1660147-affine-isometry-lift-p
    (real-carrier
     source-vector-carrier source-vector-add source-scalar-multiply source-norm
     source-point-carrier source-vector-add-point
     target-vector-carrier target-vector-add target-scalar-multiply target-norm
     target-vector-add-point
     map linear-map linear-inverse)
  (and
   (q1660147-linear-isometry-equivalence-p
    real-carrier
    source-vector-carrier source-vector-add
    source-scalar-multiply source-norm
    target-vector-carrier target-vector-add
    target-scalar-multiply target-norm
    linear-map linear-inverse)
   (q1660147-affine-compatibility-p
    source-vector-carrier source-point-carrier source-vector-add-point
    target-vector-add-point map linear-map)))

(defun-sk q1660147-affine-isometry-lift-exists-p
    (real-carrier
     source-vector-carrier source-vector-add source-scalar-multiply source-norm
     source-point-carrier source-vector-add-point
     target-vector-carrier target-vector-add target-scalar-multiply target-norm
     target-vector-add-point map)
  (exists (linear-map linear-inverse)
    (q1660147-affine-isometry-lift-p
     real-carrier
     source-vector-carrier source-vector-add
     source-scalar-multiply source-norm
     source-point-carrier source-vector-add-point
     target-vector-carrier target-vector-add
     target-scalar-multiply target-norm
     target-vector-add-point
     map linear-map linear-inverse)))

(defun thousand-theorems-q1660147-mazur-ulam-theorem-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     source-vector-carrier source-vector-zero source-vector-add
     source-vector-negate source-scalar-multiply source-norm
     source-point-carrier source-vector-add-point source-point-subtract
     target-vector-carrier target-vector-zero target-vector-add
     target-vector-negate target-scalar-multiply target-norm
     target-point-carrier target-vector-add-point target-point-subtract
     map inverse-map)
  (implies
   (and
    (q1660147-real-field-p
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less)
    (q1660147-normed-real-vector-space-p
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-less
     source-vector-carrier source-vector-zero source-vector-add
     source-vector-negate source-scalar-multiply source-norm)
    (q1660147-normed-affine-space-p
     source-vector-carrier source-vector-zero source-vector-add
     source-point-carrier source-vector-add-point source-point-subtract)
    (q1660147-normed-real-vector-space-p
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-less
     target-vector-carrier target-vector-zero target-vector-add
     target-vector-negate target-scalar-multiply target-norm)
    (q1660147-normed-affine-space-p
     target-vector-carrier target-vector-zero target-vector-add
     target-point-carrier target-vector-add-point target-point-subtract)
    (q1660147-isometry-equivalence-p
     source-point-carrier source-norm source-point-subtract
     target-point-carrier target-norm target-point-subtract
     map inverse-map))
   (q1660147-affine-isometry-lift-exists-p
    real-carrier
    source-vector-carrier source-vector-add
    source-scalar-multiply source-norm
    source-point-carrier source-vector-add-point
    target-vector-carrier target-vector-add
    target-scalar-multiply target-norm
    target-vector-add-point map)))

(value-triple :itpeval-statement-checked)
:q
