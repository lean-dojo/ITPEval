;; Statement-only formalization of thousand-theorems corpus artifact Q1306095,
;; "Whitney embedding theorem": every compact Hausdorff smooth
;; finite-dimensional real manifold admits a smooth closed embedding into
;; some finite-dimensional Euclidean space with injective derivative
;; everywhere. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Mathematical carriers, sets, families, maps, charts, linear maps, and jets
;; range over unrestricted ACL2 objects.  The conservative interfaces below
;; interpret these tags; every field, topology, vector-space, chart, and
;; smoothness law used by the statement is explicit in its predicate body.

(defstub q1306095-set-member-p (set object) t)
(defstub q1306095-family-member-p (family set) t)

(defstub q1306095-empty-set (carrier) t)
(defstub q1306095-full-set (carrier) t)
(defstub q1306095-intersection-set (carrier left right) t)
(defstub q1306095-union-set (carrier family) t)
(defstub q1306095-complement-set (carrier set) t)

(defstub q1306095-field-member-p (field value) t)
(defstub q1306095-field-carrier-set (field) t)
(defstub q1306095-field-zero (field) t)
(defstub q1306095-field-one (field) t)
(defstub q1306095-field-add (field left right) t)
(defstub q1306095-field-multiply (field left right) t)
(defstub q1306095-field-negate (field value) t)
(defstub q1306095-field-inverse (field value) t)
(defstub q1306095-field-absolute (field value) t)
(defstub q1306095-field-le-p (field left right) t)
(defstub q1306095-field-from-nat (field n) t)

(defstub q1306095-space-member-p (space value) t)
(defstub q1306095-space-carrier-set (space) t)
(defstub q1306095-space-zero (space) t)
(defstub q1306095-space-add (space left right) t)
(defstub q1306095-space-negate (space value) t)
(defstub q1306095-space-smul (space scalar value) t)
(defstub q1306095-space-norm (space value) t)

(defstub q1306095-function-value (function argument) t)
(defstub q1306095-linear-value (linear-map argument) t)
(defstub q1306095-jet-value (jet order point arguments) t)
(defstub q1306095-chart-jet (jet-family chart) t)

(defstub q1306095-atlas-member-p (atlas chart) t)
(defstub q1306095-chart-source (chart) t)
(defstub q1306095-chart-target (chart) t)
(defstub q1306095-chart-forward (chart point) t)
(defstub q1306095-chart-inverse (chart coordinate) t)

(defstub q1306095-topology-open-p (topology set) t)

(defstub q1306095-coordinate-function (chart mapping) t)
(defstub q1306095-transition-function (left-chart right-chart) t)
(defstub q1306095-zero-function (space) t)

;; Set constructors are extensional on the represented carrier.  Families are
;; arbitrary extensional collections of represented subsets, not finite
;; enumerations.

(defun-sk q1306095-valid-set-p (carrier set)
  (forall (x)
    (implies
     (q1306095-set-member-p set x)
     (q1306095-set-member-p carrier x))))

(defun-sk q1306095-set-equiv-p (carrier left right)
  (forall (x)
    (implies
     (q1306095-set-member-p carrier x)
     (iff
      (q1306095-set-member-p left x)
      (q1306095-set-member-p right x)))))

(defun-sk q1306095-family-members-valid-p (carrier family)
  (forall (set)
    (implies
     (q1306095-family-member-p family set)
     (q1306095-valid-set-p carrier set))))

(defun-sk q1306095-family-extensional-p (carrier family)
  (forall (left right)
    (implies
     (and
      (q1306095-valid-set-p carrier left)
      (q1306095-valid-set-p carrier right)
      (q1306095-set-equiv-p carrier left right))
     (iff
      (q1306095-family-member-p family left)
      (q1306095-family-member-p family right)))))

(defun q1306095-family-of-sets-p (carrier family)
  (and
   (q1306095-family-members-valid-p carrier family)
   (q1306095-family-extensional-p carrier family)))

(defun-sk q1306095-union-member-exists-p (family x)
  (exists (set)
    (and
     (q1306095-family-member-p family set)
     (q1306095-set-member-p set x))))

(defun-sk q1306095-set-constructor-laws-p (carrier)
  (forall (x left right family)
    (and
     (not
      (q1306095-set-member-p
       (q1306095-empty-set carrier) x))
     (iff
      (q1306095-set-member-p
       (q1306095-full-set carrier) x)
      (q1306095-set-member-p carrier x))
     (iff
      (q1306095-set-member-p
       (q1306095-intersection-set carrier left right) x)
      (and
       (q1306095-set-member-p carrier x)
       (q1306095-set-member-p left x)
       (q1306095-set-member-p right x)))
     (iff
      (q1306095-set-member-p
       (q1306095-complement-set carrier left) x)
      (and
       (q1306095-set-member-p carrier x)
       (not (q1306095-set-member-p left x))))
     (iff
      (q1306095-set-member-p
       (q1306095-union-set carrier family) x)
      (and
       (q1306095-set-member-p carrier x)
       (q1306095-union-member-exists-p family x))))))

(defun-sk q1306095-field-carrier-set-laws-p (field)
  (forall (x)
    (iff
     (q1306095-set-member-p
      (q1306095-field-carrier-set field) x)
     (q1306095-field-member-p field x))))

(defun-sk q1306095-space-carrier-set-laws-p (space)
  (forall (x)
    (iff
     (q1306095-set-member-p
      (q1306095-space-carrier-set space) x)
     (q1306095-space-member-p space x))))

;; A complete Archimedean ordered field is a presentation of the real numbers.

(defun q1306095-field-subtract (field left right)
  (q1306095-field-add
   field left (q1306095-field-negate field right)))

(defun q1306095-field-lt-p (field left right)
  (and
   (q1306095-field-le-p field left right)
   (not (equal left right))))

(defun-sk q1306095-field-algebra-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (q1306095-field-member-p field x)
      (q1306095-field-member-p field y)
      (q1306095-field-member-p field z))
     (and
      (q1306095-field-member-p
       field (q1306095-field-add field x y))
      (q1306095-field-member-p
       field (q1306095-field-multiply field x y))
      (q1306095-field-member-p
       field (q1306095-field-negate field x))
      (q1306095-field-member-p
       field (q1306095-field-inverse field x))
      (q1306095-field-member-p
       field (q1306095-field-absolute field x))
      (equal
       (q1306095-field-add
        field (q1306095-field-add field x y) z)
       (q1306095-field-add
        field x (q1306095-field-add field y z)))
      (equal
       (q1306095-field-add field x y)
       (q1306095-field-add field y x))
      (equal
       (q1306095-field-add
        field x (q1306095-field-zero field))
       x)
      (equal
       (q1306095-field-add
        field x (q1306095-field-negate field x))
       (q1306095-field-zero field))
      (equal
       (q1306095-field-multiply
        field (q1306095-field-multiply field x y) z)
       (q1306095-field-multiply
        field x (q1306095-field-multiply field y z)))
      (equal
       (q1306095-field-multiply field x y)
       (q1306095-field-multiply field y x))
      (equal
       (q1306095-field-multiply
        field x (q1306095-field-one field))
       x)
      (equal
       (q1306095-field-multiply
        field x (q1306095-field-zero field))
       (q1306095-field-zero field))
      (implies
       (not (equal x (q1306095-field-zero field)))
       (equal
        (q1306095-field-multiply
         field x (q1306095-field-inverse field x))
        (q1306095-field-one field)))
      (equal
       (q1306095-field-multiply
        field x (q1306095-field-add field y z))
       (q1306095-field-add
        field
        (q1306095-field-multiply field x y)
        (q1306095-field-multiply field x z)))))))

(defun-sk q1306095-field-order-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (q1306095-field-member-p field x)
      (q1306095-field-member-p field y)
      (q1306095-field-member-p field z))
     (and
      (q1306095-field-le-p field x x)
      (implies
       (and
        (q1306095-field-le-p field x y)
        (q1306095-field-le-p field y z))
       (q1306095-field-le-p field x z))
      (implies
       (and
        (q1306095-field-le-p field x y)
        (q1306095-field-le-p field y x))
       (equal x y))
      (or
       (q1306095-field-le-p field x y)
       (q1306095-field-le-p field y x))
      (implies
       (q1306095-field-le-p field x y)
       (q1306095-field-le-p
        field
        (q1306095-field-add field z x)
        (q1306095-field-add field z y)))
      (implies
       (and
        (q1306095-field-le-p
         field (q1306095-field-zero field) x)
        (q1306095-field-le-p
         field (q1306095-field-zero field) y))
       (q1306095-field-le-p
        field
        (q1306095-field-zero field)
        (q1306095-field-multiply field x y)))))))

(defun-sk q1306095-field-absolute-laws-p (field)
  (forall (x y)
    (implies
     (and
      (q1306095-field-member-p field x)
      (q1306095-field-member-p field y))
     (and
      (q1306095-field-le-p
       field
       (q1306095-field-zero field)
       (q1306095-field-absolute field x))
      (implies
       (q1306095-field-le-p
        field (q1306095-field-zero field) x)
       (equal (q1306095-field-absolute field x) x))
      (implies
       (q1306095-field-le-p
        field x (q1306095-field-zero field))
       (equal
        (q1306095-field-absolute field x)
        (q1306095-field-negate field x)))
      (iff
       (equal
        (q1306095-field-absolute field x)
        (q1306095-field-zero field))
       (equal x (q1306095-field-zero field)))
      (equal
       (q1306095-field-absolute
        field (q1306095-field-negate field x))
       (q1306095-field-absolute field x))
      (q1306095-field-le-p
       field
       (q1306095-field-absolute
        field (q1306095-field-add field x y))
       (q1306095-field-add
        field
        (q1306095-field-absolute field x)
        (q1306095-field-absolute field y)))
      (equal
       (q1306095-field-absolute
        field (q1306095-field-multiply field x y))
       (q1306095-field-multiply
        field
        (q1306095-field-absolute field x)
        (q1306095-field-absolute field y)))))))

(defun-sk q1306095-field-nat-laws-p (field)
  (forall (n)
    (implies
     (natp n)
     (and
      (q1306095-field-member-p
       field (q1306095-field-from-nat field n))
      (iff
       (equal n 0)
       (equal
        (q1306095-field-from-nat field n)
        (q1306095-field-zero field)))
      (equal
       (q1306095-field-from-nat field (+ 1 n))
       (q1306095-field-add
        field
        (q1306095-field-from-nat field n)
        (q1306095-field-one field)))))))

(defun-sk q1306095-archimedean-witness-exists-p (field x)
  (exists (n)
    (and
     (natp n)
     (q1306095-field-le-p
      field x (q1306095-field-from-nat field n)))))

(defun-sk q1306095-field-archimedean-p (field)
  (forall (x)
    (implies
     (q1306095-field-member-p field x)
     (q1306095-archimedean-witness-exists-p field x))))

(defun-sk q1306095-field-set-nonempty-p (field set)
  (exists (x)
    (and
     (q1306095-field-member-p field x)
     (q1306095-set-member-p set x))))

(defun-sk q1306095-upper-bound-p (field set upper)
  (forall (x)
    (implies
     (and
      (q1306095-field-member-p field x)
      (q1306095-set-member-p set x))
     (q1306095-field-le-p field x upper))))

(defun-sk q1306095-upper-bound-exists-p (field set)
  (exists (upper)
    (and
     (q1306095-field-member-p field upper)
     (q1306095-upper-bound-p field set upper))))

(defun-sk q1306095-least-upper-bound-p (field set supremum)
  (forall (upper)
    (implies
     (and
      (q1306095-field-member-p field upper)
      (q1306095-upper-bound-p field set upper))
     (q1306095-field-le-p field supremum upper))))

(defun-sk q1306095-supremum-exists-p (field set)
  (exists (supremum)
    (and
     (q1306095-field-member-p field supremum)
     (q1306095-upper-bound-p field set supremum)
     (q1306095-least-upper-bound-p field set supremum))))

(defun-sk q1306095-field-complete-p (field)
  (forall (set)
    (implies
     (and
      (q1306095-valid-set-p
       (q1306095-field-carrier-set field) set)
      (q1306095-field-set-nonempty-p field set)
      (q1306095-upper-bound-exists-p field set))
     (q1306095-supremum-exists-p field set))))

(defun q1306095-real-field-p (field)
  (and
   (q1306095-field-member-p
    field (q1306095-field-zero field))
   (q1306095-field-member-p
    field (q1306095-field-one field))
   (not
    (equal
     (q1306095-field-zero field)
     (q1306095-field-one field)))
   (equal
    (q1306095-field-inverse
     field (q1306095-field-zero field))
    (q1306095-field-zero field))
   (q1306095-field-algebra-laws-p field)
   (q1306095-field-order-laws-p field)
   (q1306095-field-absolute-laws-p field)
   (q1306095-field-nat-laws-p field)
   (q1306095-field-archimedean-p field)
   (q1306095-field-complete-p field)))

;; Normed vector spaces and exact finite bases.

(defun q1306095-space-subtract (space left right)
  (q1306095-space-add
   space left (q1306095-space-negate space right)))

(defun q1306095-space-distance (space left right)
  (q1306095-space-norm
   space (q1306095-space-subtract space left right)))

(defun-sk q1306095-normed-space-laws-p (field space)
  (forall (a b x y z)
    (implies
     (and
      (q1306095-field-member-p field a)
      (q1306095-field-member-p field b)
      (q1306095-space-member-p space x)
      (q1306095-space-member-p space y)
      (q1306095-space-member-p space z))
     (and
      (q1306095-space-member-p
       space (q1306095-space-add space x y))
      (q1306095-space-member-p
       space (q1306095-space-negate space x))
      (q1306095-space-member-p
       space (q1306095-space-smul space a x))
      (q1306095-field-member-p
       field (q1306095-space-norm space x))
      (equal
       (q1306095-space-add
        space (q1306095-space-add space x y) z)
       (q1306095-space-add
        space x (q1306095-space-add space y z)))
      (equal
       (q1306095-space-add space x y)
       (q1306095-space-add space y x))
      (equal
       (q1306095-space-add
        space x (q1306095-space-zero space))
       x)
      (equal
       (q1306095-space-add
        space x (q1306095-space-negate space x))
       (q1306095-space-zero space))
      (equal
       (q1306095-space-smul
        space (q1306095-field-one field) x)
       x)
      (equal
       (q1306095-space-smul
        space (q1306095-field-multiply field a b) x)
       (q1306095-space-smul
        space a (q1306095-space-smul space b x)))
      (equal
       (q1306095-space-smul
        space (q1306095-field-add field a b) x)
       (q1306095-space-add
        space
        (q1306095-space-smul space a x)
        (q1306095-space-smul space b x)))
      (equal
       (q1306095-space-smul
        space a (q1306095-space-add space x y))
       (q1306095-space-add
        space
        (q1306095-space-smul space a x)
        (q1306095-space-smul space a y)))
      (q1306095-field-le-p
       field
       (q1306095-field-zero field)
       (q1306095-space-norm space x))
      (iff
       (equal
        (q1306095-space-norm space x)
        (q1306095-field-zero field))
       (equal x (q1306095-space-zero space)))
      (equal
       (q1306095-space-norm
        space (q1306095-space-negate space x))
       (q1306095-space-norm space x))
      (q1306095-field-le-p
       field
       (q1306095-space-norm
        space (q1306095-space-add space x y))
       (q1306095-field-add
        field
        (q1306095-space-norm space x)
        (q1306095-space-norm space y)))
      (equal
       (q1306095-space-norm
        space (q1306095-space-smul space a x))
       (q1306095-field-multiply
        field
        (q1306095-field-absolute field a)
        (q1306095-space-norm space x)))))))

(defun q1306095-normed-space-p (field space)
  (and
   (q1306095-space-member-p
    space (q1306095-space-zero space))
   (q1306095-normed-space-laws-p field space)))

(defun q1306095-coefficients-valid-p
    (field coefficients count)
  (if (zp count)
      t
    (and
     (q1306095-field-member-p
      field
      (q1306095-function-value coefficients (- count 1)))
     (q1306095-coefficients-valid-p
      field coefficients (- count 1)))))

(defun q1306095-basis-elements-p (space basis)
  (if (consp basis)
      (and
       (q1306095-space-member-p space (car basis))
       (q1306095-basis-elements-p space (cdr basis)))
    (equal basis nil)))

(defun q1306095-linear-combination
    (field space basis coefficients index)
  (if (zp index)
      (q1306095-space-zero space)
    (q1306095-space-add
     space
     (q1306095-linear-combination
      field space basis coefficients (- index 1))
     (q1306095-space-smul
      space
      (q1306095-function-value coefficients (- index 1))
      (nth (- index 1) basis)))))

(defun q1306095-all-coefficients-zero-p
    (field coefficients count)
  (if (zp count)
      t
    (and
     (equal
      (q1306095-function-value coefficients (- count 1))
      (q1306095-field-zero field))
     (q1306095-all-coefficients-zero-p
      field coefficients (- count 1)))))

(defun-sk q1306095-basis-independent-p
    (field space basis)
  (forall (coefficients)
    (implies
     (and
      (q1306095-coefficients-valid-p
       field coefficients (len basis))
      (equal
       (q1306095-linear-combination
        field space basis coefficients (len basis))
       (q1306095-space-zero space)))
     (q1306095-all-coefficients-zero-p
      field coefficients (len basis)))))

(defun-sk q1306095-basis-spans-point-p
    (field space basis point)
  (exists (coefficients)
    (and
     (q1306095-coefficients-valid-p
      field coefficients (len basis))
     (equal
      (q1306095-linear-combination
       field space basis coefficients (len basis))
      point))))

(defun-sk q1306095-basis-spans-p (field space basis)
  (forall (point)
    (implies
     (q1306095-space-member-p space point)
     (q1306095-basis-spans-point-p
      field space basis point))))

(defun q1306095-basis-p (field space basis)
  (and
   (true-listp basis)
   (q1306095-basis-elements-p space basis)
   (q1306095-basis-independent-p field space basis)
   (q1306095-basis-spans-p field space basis)))

(defun-sk q1306095-finite-dimensional-p (field space)
  (exists (basis)
    (q1306095-basis-p field space basis)))

(defun-sk q1306095-exact-dimension-p (field space n)
  (exists (basis)
    (and
     (q1306095-basis-p field space basis)
     (equal (len basis) n))))

(defun q1306095-euclidean-space-p (field space n)
  (and
   (natp n)
   (q1306095-space-carrier-set-laws-p space)
   (q1306095-set-constructor-laws-p
    (q1306095-space-carrier-set space))
   (q1306095-normed-space-p field space)
   (q1306095-exact-dimension-p field space n)))

;; Topology, Hausdorffness, and compactness are stated through arbitrary open
;; covers with internal finite-subcover witnesses.

(defun q1306095-open-set-p (carrier topology set)
  (and
   (q1306095-valid-set-p carrier set)
   (q1306095-topology-open-p topology set)))

(defun-sk q1306095-topology-extensional-p
    (carrier topology)
  (forall (left right)
    (implies
     (and
      (q1306095-valid-set-p carrier left)
      (q1306095-valid-set-p carrier right)
      (q1306095-set-equiv-p carrier left right))
     (iff
      (q1306095-topology-open-p topology left)
      (q1306095-topology-open-p topology right)))))

(defun-sk q1306095-family-members-open-p
    (carrier topology family)
  (forall (set)
    (implies
     (q1306095-family-member-p family set)
     (q1306095-open-set-p carrier topology set))))

(defun-sk q1306095-topology-closure-laws-p
    (carrier topology)
  (forall (left right family)
    (and
     (q1306095-open-set-p
      carrier topology (q1306095-empty-set carrier))
     (q1306095-open-set-p
      carrier topology (q1306095-full-set carrier))
     (implies
      (and
       (q1306095-open-set-p carrier topology left)
       (q1306095-open-set-p carrier topology right))
      (q1306095-open-set-p
       carrier topology
       (q1306095-intersection-set carrier left right)))
     (implies
      (and
       (q1306095-family-of-sets-p carrier family)
       (q1306095-family-members-open-p
        carrier topology family))
      (q1306095-open-set-p
       carrier topology
       (q1306095-union-set carrier family))))))

(defun q1306095-topology-laws-p (carrier topology)
  (and
   (q1306095-topology-extensional-p carrier topology)
   (q1306095-topology-closure-laws-p carrier topology)))

(defun-sk q1306095-disjoint-p (left right)
  (forall (x)
    (not
     (and
      (q1306095-set-member-p left x)
      (q1306095-set-member-p right x)))))

(defun-sk q1306095-separated-neighborhoods-exist-p
    (carrier topology x y)
  (exists (left right)
    (and
     (q1306095-open-set-p carrier topology left)
     (q1306095-open-set-p carrier topology right)
     (q1306095-set-member-p left x)
     (q1306095-set-member-p right y)
     (q1306095-disjoint-p left right))))

(defun-sk q1306095-hausdorff-p (carrier topology)
  (forall (x y)
    (implies
     (and
      (q1306095-set-member-p carrier x)
      (q1306095-set-member-p carrier y)
      (not (equal x y)))
     (q1306095-separated-neighborhoods-exist-p
      carrier topology x y))))

(defun-sk q1306095-cover-point-p (family x)
  (exists (set)
    (and
     (q1306095-family-member-p family set)
     (q1306095-set-member-p set x))))

(defun-sk q1306095-cover-p (carrier family)
  (forall (x)
    (implies
     (q1306095-set-member-p carrier x)
     (q1306095-cover-point-p family x))))

(defun q1306095-subcover-elements-p (chosen carrier family)
  (if (consp chosen)
      (and
       (q1306095-valid-set-p carrier (car chosen))
       (q1306095-family-member-p family (car chosen))
       (q1306095-subcover-elements-p
        (cdr chosen) carrier family))
    (equal chosen nil)))

(defun q1306095-subcover-covers-point-p (chosen x)
  (if (consp chosen)
      (or
       (q1306095-set-member-p (car chosen) x)
       (q1306095-subcover-covers-point-p (cdr chosen) x))
    nil))

(defun-sk q1306095-subcover-covers-p (chosen carrier)
  (forall (x)
    (implies
     (q1306095-set-member-p carrier x)
     (q1306095-subcover-covers-point-p chosen x))))

(defun q1306095-finite-subcover-p
    (chosen carrier family)
  (and
   (true-listp chosen)
   (q1306095-subcover-elements-p chosen carrier family)
   (q1306095-subcover-covers-p chosen carrier)))

(defun-sk q1306095-finite-subcover-exists-p
    (carrier family)
  (exists (chosen)
    (q1306095-finite-subcover-p chosen carrier family)))

(defun-sk q1306095-compact-p (carrier topology)
  (forall (family)
    (implies
     (and
      (q1306095-family-of-sets-p carrier family)
      (q1306095-family-members-open-p
       carrier topology family)
      (q1306095-cover-p carrier family))
     (q1306095-finite-subcover-exists-p
      carrier family))))

;; Norm-open and relatively open subsets.

(defun-sk q1306095-norm-ball-subset-p
    (field space ambient set center radius)
  (forall (point)
    (implies
     (and
      (q1306095-set-member-p ambient point)
      (q1306095-field-lt-p
       field
       (q1306095-space-distance space point center)
       radius))
     (q1306095-set-member-p set point))))

(defun-sk q1306095-open-radius-exists-p
    (field space ambient set center)
  (exists (radius)
    (and
     (q1306095-field-member-p field radius)
     (q1306095-field-lt-p
      field (q1306095-field-zero field) radius)
     (q1306095-norm-ball-subset-p
      field space ambient set center radius))))

(defun-sk q1306095-relatively-open-law-p
    (field space ambient set)
  (forall (center)
    (implies
     (q1306095-set-member-p set center)
     (q1306095-open-radius-exists-p
      field space ambient set center))))

(defun q1306095-relatively-open-p
    (field space ambient set)
  (and
   (q1306095-valid-set-p ambient set)
   (q1306095-relatively-open-law-p
    field space ambient set)))

(defun q1306095-norm-open-p (field space set)
  (q1306095-relatively-open-p
   field space (q1306095-space-carrier-set space) set))

;; Linear maps, Fréchet derivatives within a set, and all-order smooth jets.

(defun-sk q1306095-linear-map-p
    (field source target linear-map)
  (forall (a x y)
    (implies
     (and
      (q1306095-field-member-p field a)
      (q1306095-space-member-p source x)
      (q1306095-space-member-p source y))
     (and
      (q1306095-space-member-p
       target (q1306095-linear-value linear-map x))
      (equal
       (q1306095-linear-value
        linear-map (q1306095-space-add source x y))
       (q1306095-space-add
        target
        (q1306095-linear-value linear-map x)
        (q1306095-linear-value linear-map y)))
      (equal
       (q1306095-linear-value
        linear-map (q1306095-space-smul source a x))
       (q1306095-space-smul
        target a (q1306095-linear-value linear-map x)))))))

(defun-sk q1306095-derivative-delta-law-p
    (field source target domain function point linear-map
     epsilon delta)
  (forall (nearby)
    (implies
     (and
      (q1306095-set-member-p domain nearby)
      (q1306095-field-lt-p
       field
       (q1306095-field-zero field)
       (q1306095-space-distance source nearby point))
      (q1306095-field-lt-p
       field
       (q1306095-space-distance source nearby point)
       delta))
     (q1306095-field-le-p
      field
      (q1306095-space-norm
       target
       (q1306095-space-subtract
        target
        (q1306095-space-subtract
         target
         (q1306095-function-value function nearby)
         (q1306095-function-value function point))
        (q1306095-linear-value
         linear-map
         (q1306095-space-subtract source nearby point))))
      (q1306095-field-multiply
       field epsilon
       (q1306095-space-distance source nearby point))))))

(defun-sk q1306095-derivative-delta-exists-p
    (field source target domain function point linear-map epsilon)
  (exists (delta)
    (and
     (q1306095-field-member-p field delta)
     (q1306095-field-lt-p
      field (q1306095-field-zero field) delta)
     (q1306095-derivative-delta-law-p
      field source target domain function point linear-map
      epsilon delta))))

(defun-sk q1306095-has-derivative-within-p
    (field source target domain function point linear-map)
  (forall (epsilon)
    (implies
     (and
      (q1306095-field-member-p field epsilon)
      (q1306095-field-lt-p
       field (q1306095-field-zero field) epsilon))
     (q1306095-derivative-delta-exists-p
      field source target domain function point linear-map epsilon))))

(defun q1306095-derivative-within-p
    (field source target domain function point linear-map)
  (and
   (q1306095-set-member-p domain point)
   (q1306095-linear-map-p field source target linear-map)
   (q1306095-has-derivative-within-p
    field source target domain function point linear-map)))

(defun q1306095-arguments-in-space-p (space arguments)
  (if (consp arguments)
      (and
       (q1306095-space-member-p space (car arguments))
       (q1306095-arguments-in-space-p space (cdr arguments)))
    (equal arguments nil)))

(defun q1306095-valid-arguments-p (space order arguments)
  (and
   (true-listp arguments)
   (equal (len arguments) order)
   (q1306095-arguments-in-space-p space arguments)))

(defun-sk q1306095-multilinear-slot-laws-p
    (field source target jet order point arguments slot)
  (forall (a u v)
    (implies
     (and
      (q1306095-field-member-p field a)
      (q1306095-space-member-p source u)
      (q1306095-space-member-p source v))
     (and
      (equal
       (q1306095-jet-value
        jet order point
        (update-nth
         slot (q1306095-space-add source u v) arguments))
       (q1306095-space-add
        target
        (q1306095-jet-value
         jet order point (update-nth slot u arguments))
        (q1306095-jet-value
         jet order point (update-nth slot v arguments))))
      (equal
       (q1306095-jet-value
        jet order point
        (update-nth
         slot (q1306095-space-smul source a u) arguments))
       (q1306095-space-smul
        target a
        (q1306095-jet-value
         jet order point
         (update-nth slot u arguments))))))))

(defun-sk q1306095-multilinear-map-p
    (field source target jet order point)
  (forall (arguments slot)
    (implies
     (and
      (q1306095-valid-arguments-p source order arguments)
      (natp slot)
      (< slot order))
     (and
      (q1306095-space-member-p
       target
       (q1306095-jet-value
        jet order point arguments))
      (q1306095-multilinear-slot-laws-p
       field source target jet order point arguments slot)))))

(defun-sk q1306095-jet-step-delta-law-p
    (field source target domain jet order point arguments
     epsilon delta)
  (forall (nearby)
    (implies
     (and
      (q1306095-set-member-p domain nearby)
      (q1306095-field-lt-p
       field
       (q1306095-field-zero field)
       (q1306095-space-distance source nearby point))
      (q1306095-field-lt-p
       field
       (q1306095-space-distance source nearby point)
       delta))
     (q1306095-field-le-p
      field
      (q1306095-space-norm
       target
       (q1306095-space-subtract
        target
        (q1306095-space-subtract
         target
         (q1306095-jet-value
          jet order nearby arguments)
         (q1306095-jet-value
          jet order point arguments))
        (q1306095-jet-value
         jet (+ 1 order) point
         (cons
          (q1306095-space-subtract source nearby point)
          arguments))))
      (q1306095-field-multiply
       field
       epsilon
       (q1306095-space-distance source nearby point))))))

(defun-sk q1306095-jet-step-delta-exists-p
    (field source target domain jet order point arguments epsilon)
  (exists (delta)
    (and
     (q1306095-field-member-p field delta)
     (q1306095-field-lt-p
      field (q1306095-field-zero field) delta)
     (q1306095-jet-step-delta-law-p
      field source target domain jet order point arguments
      epsilon delta))))

(defun-sk q1306095-jet-step-p
    (field source target domain jet order point arguments)
  (forall (epsilon)
    (implies
     (and
      (q1306095-field-member-p field epsilon)
      (q1306095-field-lt-p
       field (q1306095-field-zero field) epsilon))
     (q1306095-jet-step-delta-exists-p
      field source target domain jet order point arguments
      epsilon))))

(defun-sk q1306095-smooth-jet-laws-p
    (field source target domain function jet)
  (forall (order point arguments)
    (implies
     (and
      (natp order)
      (q1306095-set-member-p domain point)
      (q1306095-valid-arguments-p source order arguments))
     (and
      (q1306095-space-member-p
       target
       (q1306095-jet-value jet order point arguments))
      (q1306095-multilinear-map-p
       field source target jet order point)
      (q1306095-jet-step-p
       field source target domain jet order point arguments)
      (implies
       (equal order 0)
       (equal
        (q1306095-jet-value jet 0 point nil)
        (q1306095-function-value function point)))))))

(defun q1306095-smooth-jet-within-p
    (field source target domain function jet)
  (and
   (q1306095-valid-set-p
    (q1306095-space-carrier-set source) domain)
   (q1306095-smooth-jet-laws-p
    field source target domain function jet)))

(defun-sk q1306095-smooth-jet-exists-p
    (field source target domain function)
  (exists (jet)
    (q1306095-smooth-jet-within-p
     field source target domain function jet)))

;; Unique differentiability of the model-with-corners range ensures that the
;; manifold derivative does not depend on a chosen smooth extension.

(defun-sk q1306095-zero-function-laws-p (space)
  (forall (x)
    (implies
     (q1306095-space-member-p space x)
     (equal
      (q1306095-function-value
       (q1306095-zero-function space) x)
      (q1306095-space-zero space)))))

(defun-sk q1306095-linear-map-zero-p (source target linear-map)
  (forall (x)
    (implies
     (q1306095-space-member-p source x)
     (equal
      (q1306095-linear-value linear-map x)
      (q1306095-space-zero target)))))

(defun-sk q1306095-unique-diff-on-p
    (field space corner)
  (forall (point linear-map)
    (implies
     (and
      (q1306095-set-member-p corner point)
      (q1306095-derivative-within-p
       field space space corner
       (q1306095-zero-function space)
       point linear-map))
     (q1306095-linear-map-zero-p
      space space linear-map))))

;; Coordinate and transition function constructors have their exact values.

(defun-sk q1306095-function-constructor-laws-p ()
  (forall (chart left right mapping coordinate)
    (and
     (equal
      (q1306095-function-value
       (q1306095-coordinate-function chart mapping)
       coordinate)
      (q1306095-function-value
       mapping
       (q1306095-chart-inverse chart coordinate)))
     (equal
      (q1306095-function-value
       (q1306095-transition-function left right)
       coordinate)
      (q1306095-chart-forward
       right
       (q1306095-chart-inverse left coordinate))))))

;; Charts are homeomorphisms onto relatively open pieces of the
;; model-with-corners range.

(defun-sk q1306095-chart-target-characterization-p
    (corner chart ambient-open)
  (forall (coordinate)
    (iff
     (q1306095-set-member-p
      (q1306095-chart-target chart) coordinate)
     (and
      (q1306095-set-member-p corner coordinate)
      (q1306095-set-member-p ambient-open coordinate)))))

(defun-sk q1306095-chart-target-relative-open-p
    (field model-space corner chart)
  (exists (ambient-open)
    (and
     (q1306095-norm-open-p
      field model-space ambient-open)
     (q1306095-chart-target-characterization-p
      corner chart ambient-open))))

(defun-sk q1306095-chart-inverse-laws-p (chart)
  (forall (point coordinate)
    (and
     (implies
      (q1306095-set-member-p
       (q1306095-chart-source chart) point)
      (and
       (q1306095-set-member-p
        (q1306095-chart-target chart)
        (q1306095-chart-forward chart point))
       (equal
        (q1306095-chart-inverse
         chart (q1306095-chart-forward chart point))
        point)))
     (implies
      (q1306095-set-member-p
       (q1306095-chart-target chart) coordinate)
      (and
       (q1306095-set-member-p
        (q1306095-chart-source chart)
        (q1306095-chart-inverse chart coordinate))
       (equal
        (q1306095-chart-forward
         chart (q1306095-chart-inverse chart coordinate))
        coordinate))))))

(defun-sk q1306095-chart-image-ball-subset-p
    (field model-space chart subset center radius)
  (forall (coordinate)
    (implies
     (and
      (q1306095-set-member-p
       (q1306095-chart-target chart) coordinate)
      (q1306095-field-lt-p
       field
       (q1306095-space-distance
        model-space coordinate center)
       radius))
     (q1306095-set-member-p
      subset (q1306095-chart-inverse chart coordinate)))))

(defun-sk q1306095-chart-image-open-radius-exists-p
    (field model-space chart subset center)
  (exists (radius)
    (and
     (q1306095-field-member-p field radius)
     (q1306095-field-lt-p
      field (q1306095-field-zero field) radius)
     (q1306095-chart-image-ball-subset-p
      field model-space chart subset center radius))))

(defun-sk q1306095-chart-image-relatively-open-p
    (field model-space chart subset)
  (forall (center)
    (implies
     (and
      (q1306095-set-member-p
       (q1306095-chart-target chart) center)
      (q1306095-set-member-p
       subset (q1306095-chart-inverse chart center)))
     (q1306095-chart-image-open-radius-exists-p
      field model-space chart subset center))))

(defun-sk q1306095-chart-topology-laws-p
    (field model-space carrier topology chart)
  (forall (subset)
    (implies
     (q1306095-valid-set-p
      (q1306095-chart-source chart) subset)
     (iff
      (q1306095-open-set-p carrier topology subset)
      (q1306095-chart-image-relatively-open-p
       field model-space chart subset)))))

(defun q1306095-chart-p
    (field model-space corner carrier topology chart)
  (and
   (q1306095-valid-set-p
    carrier (q1306095-chart-source chart))
   (q1306095-valid-set-p
    corner (q1306095-chart-target chart))
   (q1306095-open-set-p
    carrier topology (q1306095-chart-source chart))
   (q1306095-chart-target-relative-open-p
    field model-space corner chart)
   (q1306095-chart-inverse-laws-p chart)
   (q1306095-chart-topology-laws-p
    field model-space carrier topology chart)))

(defun-sk q1306095-chart-containing-point-exists-p
    (atlas point)
  (exists (chart)
    (and
     (q1306095-atlas-member-p atlas chart)
     (q1306095-set-member-p
      (q1306095-chart-source chart) point))))

(defun-sk q1306095-atlas-cover-p (carrier atlas)
  (forall (point)
    (implies
     (q1306095-set-member-p carrier point)
     (q1306095-chart-containing-point-exists-p
      atlas point))))

(defun-sk q1306095-atlas-chart-laws-p
    (field model-space corner carrier topology atlas)
  (forall (chart)
    (implies
     (q1306095-atlas-member-p atlas chart)
     (q1306095-chart-p
      field model-space corner carrier topology chart))))

(defun-sk q1306095-transition-domain-characterization-p
    (domain left right)
  (forall (coordinate)
    (iff
     (q1306095-set-member-p domain coordinate)
     (and
      (q1306095-set-member-p
       (q1306095-chart-target left) coordinate)
      (q1306095-set-member-p
       (q1306095-chart-source right)
       (q1306095-chart-inverse left coordinate))))))

(defun-sk q1306095-smooth-transition-exists-p
    (field model-space left right)
  (exists (domain)
    (and
     (q1306095-transition-domain-characterization-p
      domain left right)
     (q1306095-smooth-jet-exists-p
      field model-space model-space domain
      (q1306095-transition-function left right)))))

(defun-sk q1306095-smooth-atlas-p
    (field model-space atlas)
  (forall (left right)
    (implies
     (and
      (q1306095-atlas-member-p atlas left)
      (q1306095-atlas-member-p atlas right))
     (q1306095-smooth-transition-exists-p
      field model-space left right))))

(defun q1306095-compact-smooth-manifold-p
    (field model-space corner carrier topology atlas)
  (and
   (q1306095-real-field-p field)
   (q1306095-normed-space-p field model-space)
   (q1306095-finite-dimensional-p field model-space)
   (q1306095-space-carrier-set-laws-p model-space)
   (q1306095-set-constructor-laws-p
    (q1306095-space-carrier-set model-space))
   (q1306095-valid-set-p
    (q1306095-space-carrier-set model-space) corner)
   (q1306095-zero-function-laws-p model-space)
   (q1306095-unique-diff-on-p
    field model-space corner)
   (q1306095-set-constructor-laws-p carrier)
   (q1306095-topology-laws-p carrier topology)
   (q1306095-hausdorff-p carrier topology)
   (q1306095-compact-p carrier topology)
   (q1306095-atlas-chart-laws-p
    field model-space corner carrier topology atlas)
   (q1306095-atlas-cover-p carrier atlas)
   (q1306095-smooth-atlas-p
    field model-space atlas)))

;; Smooth manifold maps into an exact n-dimensional real normed space.  Such a
;; target is linearly homeomorphic and diffeomorphic to the canonical R^n, so
;; this is a bidirectionally equivalent Euclidean-space presentation.

(defun-sk q1306095-map-values-p
    (carrier target mapping)
  (forall (point)
    (implies
     (q1306095-set-member-p carrier point)
     (q1306095-space-member-p
      target (q1306095-function-value mapping point)))))

(defun-sk q1306095-smooth-coordinate-laws-p
    (field model-space target atlas mapping jet-family)
  (forall (chart)
    (implies
     (q1306095-atlas-member-p atlas chart)
     (q1306095-smooth-jet-within-p
      field model-space target
      (q1306095-chart-target chart)
      (q1306095-coordinate-function chart mapping)
      (q1306095-chart-jet jet-family chart)))))

(defun q1306095-smooth-manifold-map-p
    (field model-space target carrier atlas mapping jet-family)
  (and
   (q1306095-map-values-p carrier target mapping)
   (q1306095-smooth-coordinate-laws-p
    field model-space target atlas mapping jet-family)))

(defun-sk q1306095-map-injective-p (carrier mapping)
  (forall (left right)
    (implies
     (and
      (q1306095-set-member-p carrier left)
      (q1306095-set-member-p carrier right)
      (equal
       (q1306095-function-value mapping left)
       (q1306095-function-value mapping right)))
     (equal left right))))

(defun-sk q1306095-preimage-characterization-p
    (carrier source-set target-set mapping)
  (forall (point)
    (implies
     (q1306095-set-member-p carrier point)
     (iff
      (q1306095-set-member-p source-set point)
      (q1306095-set-member-p
       target-set
       (q1306095-function-value mapping point))))))

(defun-sk q1306095-preimage-open-p
    (carrier topology target-set mapping)
  (exists (source-set)
    (and
     (q1306095-preimage-characterization-p
      carrier source-set target-set mapping)
     (q1306095-open-set-p carrier topology source-set))))

(defun-sk q1306095-map-continuous-p
    (field target carrier topology mapping)
  (forall (target-set)
    (implies
     (q1306095-norm-open-p field target target-set)
     (q1306095-preimage-open-p
      carrier topology target-set mapping))))

(defun-sk q1306095-source-open-induced-p
    (field target carrier mapping source-set)
  (exists (target-set)
    (and
     (q1306095-norm-open-p field target target-set)
     (q1306095-preimage-characterization-p
      carrier source-set target-set mapping))))

(defun-sk q1306095-map-induces-topology-p
    (field target carrier topology mapping)
  (forall (source-set)
    (implies
     (q1306095-open-set-p carrier topology source-set)
     (q1306095-source-open-induced-p
      field target carrier mapping source-set))))

(defun-sk q1306095-image-point-exists-p
    (carrier mapping target-point)
  (exists (source-point)
    (and
     (q1306095-set-member-p carrier source-point)
     (equal
      (q1306095-function-value mapping source-point)
      target-point))))

(defun-sk q1306095-image-complement-ball-p
    (field target carrier mapping center radius)
  (forall (point)
    (implies
     (and
      (q1306095-space-member-p target point)
      (q1306095-field-lt-p
       field
       (q1306095-space-distance target point center)
       radius))
     (not
      (q1306095-image-point-exists-p
       carrier mapping point)))))

(defun-sk q1306095-image-complement-radius-exists-p
    (field target carrier mapping center)
  (exists (radius)
    (and
     (q1306095-field-member-p field radius)
     (q1306095-field-lt-p
      field (q1306095-field-zero field) radius)
     (q1306095-image-complement-ball-p
      field target carrier mapping center radius))))

(defun-sk q1306095-image-closed-p
    (field target carrier mapping)
  (forall (center)
    (implies
     (and
      (q1306095-space-member-p target center)
      (not
       (q1306095-image-point-exists-p
        carrier mapping center)))
     (q1306095-image-complement-radius-exists-p
      field target carrier mapping center))))

(defun q1306095-closed-embedding-p
    (field target carrier topology mapping)
  (and
   (q1306095-map-values-p carrier target mapping)
   (q1306095-map-injective-p carrier mapping)
   (q1306095-map-continuous-p
    field target carrier topology mapping)
   (q1306095-map-induces-topology-p
    field target carrier topology mapping)
   (q1306095-image-closed-p
    field target carrier mapping)))

(defun-sk q1306095-first-jet-injective-p
    (model-space jet coordinate)
  (forall (left right)
    (implies
     (and
      (q1306095-space-member-p model-space left)
      (q1306095-space-member-p model-space right)
      (equal
       (q1306095-jet-value jet 1 coordinate (list left))
       (q1306095-jet-value jet 1 coordinate (list right))))
     (equal left right))))

(defun-sk q1306095-chart-derivative-injective-at-p
    (model-space atlas mapping jet-family point)
  (exists (chart)
    (and
     (q1306095-atlas-member-p atlas chart)
     (q1306095-set-member-p
      (q1306095-chart-source chart) point)
     (q1306095-first-jet-injective-p
      model-space
      (q1306095-chart-jet jet-family chart)
      (q1306095-chart-forward chart point)))))

(defun-sk q1306095-injective-manifold-derivative-p
    (model-space carrier atlas mapping jet-family)
  (forall (point)
    (implies
     (q1306095-set-member-p carrier point)
     (q1306095-chart-derivative-injective-at-p
      model-space atlas mapping jet-family point))))

(defun q1306095-embedding-witness-p
    (field model-space carrier topology atlas
     n target mapping jet-family)
  (and
   (q1306095-euclidean-space-p field target n)
   (q1306095-smooth-manifold-map-p
    field model-space target carrier atlas mapping jet-family)
   (q1306095-closed-embedding-p
    field target carrier topology mapping)
   (q1306095-injective-manifold-derivative-p
    model-space carrier atlas mapping jet-family)))

(defun-sk q1306095-embedding-witness-exists-p
    (field model-space carrier topology atlas)
  (exists (n target mapping jet-family)
    (q1306095-embedding-witness-p
     field model-space carrier topology atlas
     n target mapping jet-family)))

(defun-sk
    thousand-theorems-q1306095-whitney-embedding-theorem-statement
    ()
  (forall (field model-space corner carrier topology atlas)
    (implies
     (and
      (q1306095-function-constructor-laws-p)
      (q1306095-field-carrier-set-laws-p field)
      (q1306095-set-constructor-laws-p
       (q1306095-field-carrier-set field))
      (q1306095-compact-smooth-manifold-p
       field model-space corner carrier topology atlas))
     (q1306095-embedding-witness-exists-p
      field model-space carrier topology atlas))))

(value-triple :itpeval-statement-checked)
:q
