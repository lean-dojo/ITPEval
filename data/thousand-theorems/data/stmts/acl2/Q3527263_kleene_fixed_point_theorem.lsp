;; Statement-only formalization of thousand-theorems corpus artifact Q3527263,
;; "Kleene fixed-point theorem": for an omega-Scott-continuous monotone
;; self-map of a complete lattice, the least fixed point is the supremum of
;; the finite iterates of bottom. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ function objects present the arbitrary carrier, order, subsets,
;; self-map, and omega-indexed chains.  The complete-lattice, monotonicity, and
;; omega-Scott-continuity laws are all explicit in the statement predicate.
;; DEFCHOOSE names uniquely characterized suprema and the least prefixed point;
;; these are conservative definitions, not externally supplied witnesses.

(defun q3527263-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun q3527263-le (order x y)
  (if (apply$ order (list x y)) t nil))

(defun q3527263-map-value (map x)
  (apply$ map (list x)))

(defun q3527263-set-member-p (set x)
  (if (apply$ set (list x)) t nil))

(defun q3527263-sequence-value (sequence n)
  (apply$ sequence (list n)))

;; Partial orders and arbitrary subsets of the carrier.

(defun-sk q3527263-order-reflexive-p (carrier order)
  (forall (x)
    (implies
     (q3527263-member-p carrier x)
     (q3527263-le order x x))))

(defun-sk q3527263-order-transitive-p (carrier order)
  (forall (x y z)
    (implies
     (and
      (q3527263-member-p carrier x)
      (q3527263-member-p carrier y)
      (q3527263-member-p carrier z)
      (q3527263-le order x y)
      (q3527263-le order y z))
     (q3527263-le order x z))))

(defun-sk q3527263-order-antisymmetric-p (carrier order)
  (forall (x y)
    (implies
     (and
      (q3527263-member-p carrier x)
      (q3527263-member-p carrier y)
      (q3527263-le order x y)
      (q3527263-le order y x))
     (equal x y))))

(defun q3527263-partial-order-p (carrier order)
  (and
   (tamep-functionp carrier)
   (tamep-functionp order)
   (q3527263-order-reflexive-p carrier order)
   (q3527263-order-transitive-p carrier order)
   (q3527263-order-antisymmetric-p carrier order)))

(defun-sk q3527263-bottom-law-p (carrier order bottom)
  (forall (x)
    (implies
     (q3527263-member-p carrier x)
     (q3527263-le order bottom x))))

(defun-sk q3527263-valid-set-elements-p (carrier set)
  (forall (x)
    (implies
     (q3527263-set-member-p set x)
     (q3527263-member-p carrier x))))

(defun q3527263-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (q3527263-valid-set-elements-p carrier set)))

(defun-sk q3527263-upper-bound-p
    (carrier order set bound)
  (forall (x)
    (implies
     (and
      (q3527263-member-p carrier x)
      (q3527263-set-member-p set x))
     (q3527263-le order x bound))))

(defun-sk q3527263-least-upper-bound-minimal-p
    (carrier order set supremum)
  (forall (bound)
    (implies
     (and
      (q3527263-member-p carrier bound)
      (q3527263-upper-bound-p
       carrier order set bound))
     (q3527263-le order supremum bound))))

(defun q3527263-least-upper-bound-p
    (carrier order set supremum)
  (and
   (q3527263-member-p carrier supremum)
   (q3527263-upper-bound-p
    carrier order set supremum)
   (q3527263-least-upper-bound-minimal-p
    carrier order set supremum)))

(defun-sk q3527263-set-supremum-exists-p
    (carrier order set)
  (exists (supremum)
    (q3527263-least-upper-bound-p
     carrier order set supremum)))

(defun-sk q3527263-all-set-suprema-exist-p
    (carrier order)
  (forall (set)
    (implies
     (q3527263-valid-set-p carrier set)
     (q3527263-set-supremum-exists-p
      carrier order set))))

(defun q3527263-complete-lattice-p
    (carrier order bottom)
  (and
   (q3527263-partial-order-p carrier order)
   (q3527263-member-p carrier bottom)
   (q3527263-bottom-law-p carrier order bottom)
   (q3527263-all-set-suprema-exist-p carrier order)))

;; The bundled order homomorphism is an arbitrary carrier-valued monotone map.

(defun-sk q3527263-map-typed-p (carrier map)
  (forall (x)
    (implies
     (q3527263-member-p carrier x)
     (q3527263-member-p
      carrier
      (q3527263-map-value map x)))))

(defun-sk q3527263-map-monotone-p
    (carrier order map)
  (forall (x y)
    (implies
     (and
      (q3527263-member-p carrier x)
      (q3527263-member-p carrier y)
      (q3527263-le order x y))
     (q3527263-le
      order
      (q3527263-map-value map x)
      (q3527263-map-value map y)))))

(defun q3527263-order-hom-p (carrier order map)
  (and
   (tamep-functionp map)
   (q3527263-map-typed-p carrier map)
   (q3527263-map-monotone-p carrier order map)))

;; Suprema of arbitrary increasing omega-chains.

(defun-sk q3527263-sequence-typed-p
    (carrier sequence)
  (forall (n)
    (implies
     (natp n)
     (q3527263-member-p
      carrier
      (q3527263-sequence-value sequence n)))))

(defun-sk q3527263-sequence-increasing-p
    (order sequence)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (<= m n))
     (q3527263-le
      order
      (q3527263-sequence-value sequence m)
      (q3527263-sequence-value sequence n)))))

(defun q3527263-omega-chain-p
    (carrier order sequence)
  (and
   (tamep-functionp sequence)
   (q3527263-sequence-typed-p carrier sequence)
   (q3527263-sequence-increasing-p order sequence)))

(defun-sk q3527263-sequence-upper-bound-p
    (order sequence bound)
  (forall (n)
    (implies
     (natp n)
     (q3527263-le
      order
      (q3527263-sequence-value sequence n)
      bound))))

(defun-sk q3527263-sequence-supremum-minimal-p
    (carrier order sequence supremum)
  (forall (bound)
    (implies
     (and
      (q3527263-member-p carrier bound)
      (q3527263-sequence-upper-bound-p
       order sequence bound))
     (q3527263-le order supremum bound))))

(defun q3527263-sequence-supremum-p
    (carrier order sequence supremum)
  (and
   (q3527263-member-p carrier supremum)
   (q3527263-sequence-upper-bound-p
    order sequence supremum)
   (q3527263-sequence-supremum-minimal-p
    carrier order sequence supremum)))

(defchoose q3527263-sequence-supremum
    (supremum)
    (carrier order sequence)
  (q3527263-sequence-supremum-p
   carrier order sequence supremum))

(defun-sk q3527263-mapped-sequence-upper-bound-p
    (order map sequence bound)
  (forall (n)
    (implies
     (natp n)
     (q3527263-le
      order
      (q3527263-map-value
       map
       (q3527263-sequence-value sequence n))
      bound))))

(defun-sk q3527263-mapped-sequence-supremum-minimal-p
    (carrier order map sequence supremum)
  (forall (bound)
    (implies
     (and
      (q3527263-member-p carrier bound)
      (q3527263-mapped-sequence-upper-bound-p
       order map sequence bound))
     (q3527263-le order supremum bound))))

(defun q3527263-mapped-sequence-supremum-p
    (carrier order map sequence supremum)
  (and
   (q3527263-member-p carrier supremum)
   (q3527263-mapped-sequence-upper-bound-p
    order map sequence supremum)
   (q3527263-mapped-sequence-supremum-minimal-p
    carrier order map sequence supremum)))

(defchoose q3527263-mapped-sequence-supremum
    (supremum)
    (carrier order map sequence)
  (q3527263-mapped-sequence-supremum-p
   carrier order map sequence supremum))

(defun-sk q3527263-omega-scott-continuous-p
    (carrier order map)
  (forall (sequence)
    (implies
     (q3527263-omega-chain-p
      carrier order sequence)
     (equal
      (q3527263-map-value
       map
       (q3527263-sequence-supremum
        carrier order sequence))
      (q3527263-mapped-sequence-supremum
       carrier order map sequence)))))

;; The source's least fixed point is its definitionally equivalent least
;; prefixed point.  Antisymmetry makes this chosen element unique.

(defun q3527263-prefixed-point-p
    (carrier order map x)
  (and
   (q3527263-member-p carrier x)
   (q3527263-le
    order
    (q3527263-map-value map x)
    x)))

(defun-sk q3527263-below-every-prefixed-point-p
    (carrier order map candidate)
  (forall (x)
    (implies
     (q3527263-prefixed-point-p
      carrier order map x)
     (q3527263-le order candidate x))))

(defun q3527263-least-prefixed-point-p
    (carrier order map candidate)
  (and
   (q3527263-prefixed-point-p
    carrier order map candidate)
   (q3527263-below-every-prefixed-point-p
    carrier order map candidate)))

(defchoose q3527263-lfp
    (candidate)
    (carrier order map)
  (q3527263-least-prefixed-point-p
   carrier order map candidate))

;; The right-hand side is the least upper bound of f^[n](bottom), for all
;; natural n, without bounding or finitely tabulating the iteration sequence.

(defun q3527263-iterate (map n x)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      x
    (q3527263-map-value
     map
     (q3527263-iterate map (1- n) x))))

(defun-sk q3527263-iterates-upper-bound-p
    (order map bottom bound)
  (forall (n)
    (implies
     (natp n)
     (q3527263-le
      order
      (q3527263-iterate map n bottom)
      bound))))

(defun-sk q3527263-iterates-supremum-minimal-p
    (carrier order map bottom supremum)
  (forall (bound)
    (implies
     (and
      (q3527263-member-p carrier bound)
      (q3527263-iterates-upper-bound-p
       order map bottom bound))
     (q3527263-le order supremum bound))))

(defun q3527263-iterates-supremum-p
    (carrier order map bottom supremum)
  (and
   (q3527263-member-p carrier supremum)
   (q3527263-iterates-upper-bound-p
    order map bottom supremum)
   (q3527263-iterates-supremum-minimal-p
    carrier order map bottom supremum)))

(defchoose q3527263-iterates-supremum
    (supremum)
    (carrier order map bottom)
  (q3527263-iterates-supremum-p
   carrier order map bottom supremum))

(defun thousand-theorems-q3527263-kleene-fixed-point-theorem-statement
    (carrier order bottom map)
  (implies
   (and
    (q3527263-complete-lattice-p
     carrier order bottom)
    (q3527263-order-hom-p
     carrier order map)
    (q3527263-omega-scott-continuous-p
     carrier order map))
   (equal
    (q3527263-lfp carrier order map)
    (q3527263-iterates-supremum
     carrier order map bottom))))

(value-triple :itpeval-statement-checked)
:q
