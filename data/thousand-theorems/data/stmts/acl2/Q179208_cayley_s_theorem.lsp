;; Statement-only formalization of thousand-theorems corpus artifact Q179208,
;; "Cayley's theorem": a group acting faithfully on an arbitrary carrier is
;; multiplicatively equivalent to the image of its permutation action.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame function objects represent arbitrary, potentially infinite carriers,
;; operations, and actions.  Equality of action rows is extensional on the
;; acted-on carrier.  The canonical action map is an injective homomorphism
;; into permutations exactly when its corestriction to its image is a
;; multiplicative equivalence.

(defun q179208-member-p (carrier element)
  (if (apply$ carrier (list element))
      t
    nil))

(defun q179208-unary-value (function argument)
  (apply$ function (list argument)))

(defun q179208-binary-value (function left right)
  (apply$ function (list left right)))

;; Group structure on the acting carrier.

(defun-sk q179208-group-laws-p
    (group-carrier multiplication inverse identity)
  (forall (x y z)
    (and
     (implies
      (q179208-member-p group-carrier x)
      (and
       (q179208-member-p
        group-carrier
        (q179208-unary-value inverse x))
       (equal
        (q179208-binary-value multiplication identity x)
        x)
       (equal
        (q179208-binary-value multiplication x identity)
        x)
       (equal
        (q179208-binary-value
         multiplication
         (q179208-unary-value inverse x)
         x)
        identity)
       (equal
        (q179208-binary-value
         multiplication
         x
         (q179208-unary-value inverse x))
        identity)))
     (implies
      (and
       (q179208-member-p group-carrier x)
       (q179208-member-p group-carrier y))
      (q179208-member-p
       group-carrier
       (q179208-binary-value multiplication x y)))
     (implies
      (and
       (q179208-member-p group-carrier x)
       (q179208-member-p group-carrier y)
       (q179208-member-p group-carrier z))
      (equal
       (q179208-binary-value
        multiplication
        (q179208-binary-value multiplication x y)
        z)
       (q179208-binary-value
        multiplication
        x
        (q179208-binary-value multiplication y z)))))))

(defun q179208-group-p
    (group-carrier multiplication inverse identity)
  (and
   (tamep-functionp group-carrier)
   (tamep-functionp multiplication)
   (tamep-functionp inverse)
   (q179208-member-p group-carrier identity)
   (q179208-group-laws-p
    group-carrier multiplication inverse identity)))

;; Multiplicative action on the arbitrary point carrier.

(defun-sk q179208-action-laws-p
    (group-carrier point-carrier multiplication identity action)
  (forall (g k h)
    (and
     (implies
      (and
       (q179208-member-p group-carrier g)
       (q179208-member-p point-carrier h))
      (q179208-member-p
       point-carrier
       (q179208-binary-value action g h)))
     (implies
      (q179208-member-p point-carrier h)
      (equal
       (q179208-binary-value action identity h)
       h))
     (implies
      (and
       (q179208-member-p group-carrier g)
       (q179208-member-p group-carrier k)
       (q179208-member-p point-carrier h))
      (equal
       (q179208-binary-value
        action
        (q179208-binary-value multiplication g k)
        h)
       (q179208-binary-value
        action
        g
        (q179208-binary-value action k h)))))))

(defun q179208-action-p
    (group-carrier point-carrier multiplication identity action)
  (and
   (tamep-functionp point-carrier)
   (tamep-functionp action)
   (q179208-action-laws-p
    group-carrier
    point-carrier
    multiplication
    identity
    action)))

;; Two group elements determine the same permutation precisely when their
;; action rows agree at every point of H.

(defun-sk q179208-action-row-equal-p
    (point-carrier action left right)
  (forall (h)
    (implies
     (q179208-member-p point-carrier h)
     (equal
      (q179208-binary-value action left h)
      (q179208-binary-value action right h)))))

;; FaithfulSMul is injectivity of the map from group elements to action rows.
;; Its quantifier remains internal; no distinguishing-point witness is added
;; as an external parameter.

(defun-sk q179208-faithful-action-p
    (group-carrier point-carrier action)
  (forall (left right)
    (implies
     (and
      (q179208-member-p group-carrier left)
      (q179208-member-p group-carrier right)
      (q179208-action-row-equal-p
       point-carrier action left right))
     (equal left right))))

;; Every action row is a permutation, with the row of g^-1 as inverse.

(defun-sk q179208-action-row-permutation-p
    (group-carrier
     point-carrier
     inverse
     action)
  (forall (g h)
    (implies
     (and
      (q179208-member-p group-carrier g)
      (q179208-member-p point-carrier h))
     (let ((inverse-g
            (q179208-unary-value inverse g)))
       (and
        (q179208-member-p
         point-carrier
         (q179208-binary-value action g h))
        (equal
         (q179208-binary-value
          action
          inverse-g
          (q179208-binary-value action g h))
         h)
        (equal
         (q179208-binary-value
          action
          g
          (q179208-binary-value action inverse-g h))
         h))))))

;; These are the laws of the canonical multiplicative equivalence from G to
;; the exact image of g |-> (h |-> g • h).  Multiplication in that image is
;; permutation composition, equality is extensional row equality, and
;; surjectivity is definitional because every image element is an action row.

(defun-sk q179208-canonical-range-mul-equiv-laws-p
    (group-carrier
     point-carrier
     multiplication
     identity
     action)
  (forall (g k h)
    (and
     (implies
      (and
       (q179208-member-p group-carrier g)
       (q179208-member-p group-carrier k))
      (iff
       (equal g k)
       (q179208-action-row-equal-p
        point-carrier action g k)))
     (implies
      (q179208-member-p point-carrier h)
      (equal
       (q179208-binary-value action identity h)
       h))
     (implies
      (and
       (q179208-member-p group-carrier g)
       (q179208-member-p group-carrier k)
       (q179208-member-p point-carrier h))
      (equal
       (q179208-binary-value
        action
        (q179208-binary-value multiplication g k)
        h)
       (q179208-binary-value
        action
        g
        (q179208-binary-value action k h)))))))

(defun q179208-canonical-range-mul-equiv-p
    (group-carrier
     point-carrier
     multiplication
     inverse
     identity
     action)
  (and
   (q179208-action-row-permutation-p
    group-carrier point-carrier inverse action)
   (q179208-canonical-range-mul-equiv-laws-p
    group-carrier
    point-carrier
    multiplication
    identity
    action)))

(defun thousand-theorems-q179208-cayley-s-theorem-statement
    (group-carrier
     point-carrier
     multiplication
     inverse
     identity
     action)
  (implies
   (and
    (q179208-group-p
     group-carrier multiplication inverse identity)
    (q179208-action-p
     group-carrier
     point-carrier
     multiplication
     identity
     action)
    (q179208-faithful-action-p
     group-carrier point-carrier action))
   (q179208-canonical-range-mul-equiv-p
    group-carrier
    point-carrier
    multiplication
    inverse
    identity
    action)))

(value-triple :itpeval-statement-checked)
:q
