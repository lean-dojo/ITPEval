;; Statement-only formalization of thousand-theorems corpus artifact Q609612,
;; "Knaster–Tarski theorem": the fixed points of a monotone self-map of an
;; arbitrary complete lattice form a complete lattice. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ function objects represent the arbitrary carrier, order,
;; self-map, and unary characteristic predicates of potentially infinite
;; subsets. All typing, order, completeness, and monotonicity assumptions are
;; explicit in the statement predicate.

(defun q609612-member-p (carrier x)
  (if (apply$ carrier (list x))
      t
    nil))

(defun q609612-le-p (carrier order x y)
  (and
   (q609612-member-p carrier x)
   (q609612-member-p carrier y)
   (if (apply$ order (list x y))
       t
     nil)))

(defun q609612-map-value (map x)
  (apply$ map (list x)))

(defun-sk q609612-carrier-nonempty-p (carrier)
  (exists (x)
    (q609612-member-p carrier x)))

(defun-sk q609612-partial-order-p (carrier order)
  (forall (x y z)
    (and
     (implies
      (q609612-member-p carrier x)
      (q609612-le-p carrier order x x))
     (implies
      (and
       (q609612-le-p carrier order x y)
       (q609612-le-p carrier order y x))
      (equal x y))
     (implies
      (and
       (q609612-le-p carrier order x y)
       (q609612-le-p carrier order y z))
      (q609612-le-p carrier order x z)))))

(defun q609612-subset-member-p (carrier subset x)
  (and
   (q609612-member-p carrier x)
   (if (apply$ subset (list x))
       t
     nil)))

(defun-sk q609612-subset-below-p
    (carrier order subset bound)
  (forall (x)
    (implies
     (q609612-subset-member-p carrier subset x)
     (q609612-le-p carrier order x bound))))

(defun q609612-upper-bound-p
    (carrier order subset bound)
  (and
   (q609612-member-p carrier bound)
   (q609612-subset-below-p
    carrier order subset bound)))

(defun-sk q609612-below-every-upper-bound-p
    (carrier order subset supremum)
  (forall (bound)
    (implies
     (q609612-upper-bound-p
      carrier order subset bound)
     (q609612-le-p
      carrier order supremum bound))))

(defun q609612-least-upper-bound-p
    (carrier order subset supremum)
  (and
   (q609612-upper-bound-p
    carrier order subset supremum)
   (q609612-below-every-upper-bound-p
    carrier order subset supremum)))

(defun-sk q609612-least-upper-bound-exists-p
    (carrier order subset)
  (exists (supremum)
    (q609612-least-upper-bound-p
     carrier order subset supremum)))

(defun-sk q609612-below-subset-p
    (carrier order subset bound)
  (forall (x)
    (implies
     (q609612-subset-member-p carrier subset x)
     (q609612-le-p carrier order bound x))))

(defun q609612-lower-bound-p
    (carrier order subset bound)
  (and
   (q609612-member-p carrier bound)
   (q609612-below-subset-p
    carrier order subset bound)))

(defun-sk q609612-every-lower-bound-below-p
    (carrier order subset infimum)
  (forall (bound)
    (implies
     (q609612-lower-bound-p
      carrier order subset bound)
     (q609612-le-p
      carrier order bound infimum))))

(defun q609612-greatest-lower-bound-p
    (carrier order subset infimum)
  (and
   (q609612-lower-bound-p
    carrier order subset infimum)
   (q609612-every-lower-bound-below-p
    carrier order subset infimum)))

(defun-sk q609612-greatest-lower-bound-exists-p
    (carrier order subset)
  (exists (infimum)
    (q609612-greatest-lower-bound-p
     carrier order subset infimum)))

(defun-sk q609612-all-subsets-have-bounds-p
    (carrier order)
  (forall (subset)
    (implies
     (tamep-functionp subset)
     (and
      (q609612-least-upper-bound-exists-p
       carrier order subset)
      (q609612-greatest-lower-bound-exists-p
       carrier order subset)))))

(defun q609612-complete-lattice-p (carrier order)
  (and
   (tamep-functionp carrier)
   (tamep-functionp order)
   (q609612-carrier-nonempty-p carrier)
   (q609612-partial-order-p carrier order)
   (q609612-all-subsets-have-bounds-p
    carrier order)))

(defun-sk q609612-map-typed-p (carrier map)
  (forall (x)
    (implies
     (q609612-member-p carrier x)
     (q609612-member-p
      carrier
      (q609612-map-value map x)))))

(defun-sk q609612-monotone-p (carrier order map)
  (forall (x y)
    (implies
     (q609612-le-p carrier order x y)
     (q609612-le-p
      carrier
      order
      (q609612-map-value map x)
      (q609612-map-value map y)))))

(defun q609612-fixed-point-p (carrier map x)
  (and
   (q609612-member-p carrier x)
   (equal
    (q609612-map-value map x)
    x)))

(defun-sk q609612-fixed-point-nonempty-p
    (carrier map)
  (exists (x)
    (q609612-fixed-point-p carrier map x)))

(defun-sk q609612-fixed-point-partial-order-p
    (carrier order map)
  (forall (x y z)
    (and
     (implies
      (q609612-fixed-point-p carrier map x)
      (q609612-le-p carrier order x x))
     (implies
      (and
       (q609612-fixed-point-p carrier map x)
       (q609612-fixed-point-p carrier map y)
       (q609612-le-p carrier order x y)
       (q609612-le-p carrier order y x))
      (equal x y))
     (implies
      (and
       (q609612-fixed-point-p carrier map x)
       (q609612-fixed-point-p carrier map y)
       (q609612-fixed-point-p carrier map z)
       (q609612-le-p carrier order x y)
       (q609612-le-p carrier order y z))
      (q609612-le-p carrier order x z)))))

(defun q609612-fixed-subset-member-p
    (carrier map subset x)
  (and
   (q609612-fixed-point-p carrier map x)
   (if (apply$ subset (list x))
       t
     nil)))

(defun-sk q609612-fixed-subset-below-p
    (carrier order map subset bound)
  (forall (x)
    (implies
     (q609612-fixed-subset-member-p
      carrier map subset x)
     (q609612-le-p carrier order x bound))))

(defun q609612-fixed-upper-bound-p
    (carrier order map subset bound)
  (and
   (q609612-fixed-point-p carrier map bound)
   (q609612-fixed-subset-below-p
    carrier order map subset bound)))

(defun-sk q609612-fixed-below-every-upper-bound-p
    (carrier order map subset supremum)
  (forall (bound)
    (implies
     (q609612-fixed-upper-bound-p
      carrier order map subset bound)
     (q609612-le-p
      carrier order supremum bound))))

(defun q609612-fixed-least-upper-bound-p
    (carrier order map subset supremum)
  (and
   (q609612-fixed-upper-bound-p
    carrier order map subset supremum)
   (q609612-fixed-below-every-upper-bound-p
    carrier order map subset supremum)))

(defun-sk q609612-fixed-least-upper-bound-exists-p
    (carrier order map subset)
  (exists (supremum)
    (q609612-fixed-least-upper-bound-p
     carrier order map subset supremum)))

(defun-sk q609612-below-fixed-subset-p
    (carrier order map subset bound)
  (forall (x)
    (implies
     (q609612-fixed-subset-member-p
      carrier map subset x)
     (q609612-le-p carrier order bound x))))

(defun q609612-fixed-lower-bound-p
    (carrier order map subset bound)
  (and
   (q609612-fixed-point-p carrier map bound)
   (q609612-below-fixed-subset-p
    carrier order map subset bound)))

(defun-sk q609612-every-fixed-lower-bound-below-p
    (carrier order map subset infimum)
  (forall (bound)
    (implies
     (q609612-fixed-lower-bound-p
      carrier order map subset bound)
     (q609612-le-p
      carrier order bound infimum))))

(defun q609612-fixed-greatest-lower-bound-p
    (carrier order map subset infimum)
  (and
   (q609612-fixed-lower-bound-p
    carrier order map subset infimum)
   (q609612-every-fixed-lower-bound-below-p
    carrier order map subset infimum)))

(defun-sk q609612-fixed-greatest-lower-bound-exists-p
    (carrier order map subset)
  (exists (infimum)
    (q609612-fixed-greatest-lower-bound-p
     carrier order map subset infimum)))

(defun-sk q609612-all-fixed-subsets-have-bounds-p
    (carrier order map)
  (forall (subset)
    (implies
     (tamep-functionp subset)
     (and
      (q609612-fixed-least-upper-bound-exists-p
       carrier order map subset)
      (q609612-fixed-greatest-lower-bound-exists-p
       carrier order map subset)))))

(defun q609612-fixed-points-complete-lattice-p
    (carrier order map)
  (and
   (q609612-fixed-point-nonempty-p carrier map)
   (q609612-fixed-point-partial-order-p
    carrier order map)
   (q609612-all-fixed-subsets-have-bounds-p
    carrier order map)))

(defun thousand-theorems-q609612-knaster-tarski-theorem-statement
    (carrier order map)
  (implies
   (and
    (q609612-complete-lattice-p carrier order)
    (tamep-functionp map)
    (q609612-map-typed-p carrier map)
    (q609612-monotone-p carrier order map))
   (q609612-fixed-points-complete-lattice-p
    carrier order map)))

(value-triple :itpeval-statement-checked)
:q
