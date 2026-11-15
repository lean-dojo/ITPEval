;; Statement-only formalization of thousand-theorems corpus artifact Q1065966,
;; "Isomorphism theorem": the canonical first, second, and third isomorphisms
;; for groups, expressed through quotient-coset representative relations.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ function objects represent arbitrary carriers, operations,
;; homomorphisms, and subgroup predicates. DEFUN-SK supplies genuine
;; unbounded quantification over their carrier elements.

(defun q1065966-member-p (predicate element)
  (if (apply$ predicate (list element))
      t
    nil))

(defun q1065966-multiply (multiplication left right)
  (apply$ multiplication (list left right)))

(defun q1065966-invert (inverse element)
  (apply$ inverse (list element)))

(defun q1065966-map (mapping element)
  (apply$ mapping (list element)))

(defun-sk q1065966-subset-p (left right)
  (forall (element)
    (implies
     (q1065966-member-p left element)
     (q1065966-member-p right element))))

(defun-sk q1065966-range-member-p (source mapping value)
  (exists (element)
    (and
     (q1065966-member-p source element)
     (equal (q1065966-map mapping element) value))))

(defun-sk q1065966-range-preimage-p (source mapping value)
  (exists (preimage)
    (and
     (q1065966-member-p source preimage)
     (equal (q1065966-map mapping preimage) value))))

(defun-sk q1065966-product-member-p
    (subgroup-h subgroup-n multiplication element)
  (exists (h n)
    (and
     (q1065966-member-p subgroup-h h)
     (q1065966-member-p subgroup-n n)
     (equal
      element
      (q1065966-multiply multiplication h n)))))

(defun-sk q1065966-group-laws-p
    (carrier multiplication inverse identity)
  (forall (x y z)
    (and
     (implies
      (q1065966-member-p carrier x)
      (and
       (q1065966-member-p
        carrier
        (q1065966-invert inverse x))
       (equal
        (q1065966-multiply multiplication identity x)
        x)
       (equal
        (q1065966-multiply multiplication x identity)
        x)
       (equal
        (q1065966-multiply
         multiplication
         (q1065966-invert inverse x)
         x)
        identity)
       (equal
        (q1065966-multiply
         multiplication
         x
         (q1065966-invert inverse x))
        identity)))
     (implies
      (and
       (q1065966-member-p carrier x)
       (q1065966-member-p carrier y))
      (q1065966-member-p
       carrier
       (q1065966-multiply multiplication x y)))
     (implies
      (and
       (q1065966-member-p carrier x)
       (q1065966-member-p carrier y)
       (q1065966-member-p carrier z))
      (equal
       (q1065966-multiply
        multiplication
        (q1065966-multiply multiplication x y)
        z)
       (q1065966-multiply
        multiplication
        x
        (q1065966-multiply multiplication y z)))))))

(defun q1065966-group-p
    (carrier multiplication inverse identity)
  (and
   (tamep-functionp carrier)
   (tamep-functionp multiplication)
   (tamep-functionp inverse)
   (q1065966-member-p carrier identity)
   (q1065966-group-laws-p
    carrier multiplication inverse identity)))

(defun q1065966-subgroup-p
    (carrier multiplication inverse identity subgroup)
  (and
   (tamep-functionp subgroup)
   (q1065966-group-p
    carrier multiplication inverse identity)
   (q1065966-subset-p subgroup carrier)
   (q1065966-group-p
    subgroup multiplication inverse identity)))

(defun-sk q1065966-normal-laws-p
    (carrier subgroup multiplication inverse)
  (forall (conjugator element)
    (implies
     (and
      (q1065966-member-p carrier conjugator)
      (q1065966-member-p subgroup element))
     (q1065966-member-p
      subgroup
      (q1065966-multiply
       multiplication
       (q1065966-multiply multiplication conjugator element)
       (q1065966-invert inverse conjugator))))))

(defun q1065966-normal-subgroup-p
    (carrier multiplication inverse identity subgroup)
  (and
   (q1065966-subgroup-p
    carrier multiplication inverse identity subgroup)
   (q1065966-normal-laws-p
    carrier subgroup multiplication inverse)))

;; Equality of representatives modulo a normal subgroup K is x^-1*y in K.

(defun q1065966-quotient-equivalent-p
    (subgroup multiplication inverse x y)
  (q1065966-member-p
   subgroup
   (q1065966-multiply
    multiplication
    (q1065966-invert inverse x)
    y)))

(defun-sk q1065966-hom-laws-p
    (source target source-multiplication target-multiplication mapping)
  (forall (x y)
    (and
     (implies
      (q1065966-member-p source x)
      (q1065966-member-p target (q1065966-map mapping x)))
     (implies
      (and
       (q1065966-member-p source x)
       (q1065966-member-p source y))
      (equal
       (q1065966-map
        mapping
        (q1065966-multiply source-multiplication x y))
       (q1065966-multiply
        target-multiplication
        (q1065966-map mapping x)
        (q1065966-map mapping y)))))))

(defun q1065966-hom-p
    (source
     target
     source-multiplication
     target-multiplication
     source-identity
     target-identity
     mapping)
  (and
   (tamep-functionp mapping)
   (equal
    (q1065966-map mapping source-identity)
    target-identity)
   (q1065966-hom-laws-p
    source target source-multiplication target-multiplication mapping)))

;; First isomorphism theorem. The kernel quotient relation agrees exactly
;; with equality in the range, the representative map preserves products,
;; and every member of the range has a source representative. These are the
;; well-definedness, injectivity, multiplicativity, and surjectivity clauses
;; of the canonical equivalence G/ker(phi) -> range(phi).

(defun-sk q1065966-first-canonical-isomorphism-p
    (source
     target
     source-multiplication
     target-multiplication
     source-inverse
     mapping
     target-identity)
  (forall (x y value)
    (and
     (implies
      (and
       (q1065966-member-p source x)
       (q1065966-member-p source y))
      (and
       (iff
        (equal
         (q1065966-map
          mapping
          (q1065966-multiply
           source-multiplication
           (q1065966-invert source-inverse x)
           y))
         target-identity)
        (equal
         (q1065966-map mapping x)
         (q1065966-map mapping y)))
       (equal
        (q1065966-map
         mapping
         (q1065966-multiply source-multiplication x y))
        (q1065966-multiply
         target-multiplication
         (q1065966-map mapping x)
         (q1065966-map mapping y)))))
     (implies
     (and
      (q1065966-member-p target value)
      (q1065966-range-member-p source mapping value))
      (q1065966-range-preimage-p source mapping value)))))

(defun thousand-theorems-q1065966-quotient-ker-equiv-range-statement
    (source
     target
     source-multiplication
     target-multiplication
     source-inverse
     target-inverse
     source-identity
     target-identity
     mapping)
  (implies
   (and
    (q1065966-group-p
     source
     source-multiplication
     source-inverse
     source-identity)
    (q1065966-group-p
     target
     target-multiplication
     target-inverse
     target-identity)
    (q1065966-hom-p
     source
     target
     source-multiplication
     target-multiplication
     source-identity
     target-identity
     mapping))
   (q1065966-first-canonical-isomorphism-p
    source
    target
    source-multiplication
    target-multiplication
    source-inverse
    mapping
    target-identity)))

;; Second isomorphism theorem. Since N is normal, H join N is the product HN.
;; The canonical inclusion is the identity on H-representatives. Its domain
;; relation is equality modulo H intersect N, its codomain relation is
;; equality modulo N, and H join N is represented by the product HN.

(defun q1065966-second-domain-equivalent-p
    (subgroup-h subgroup-n multiplication inverse x y)
  (and
   (q1065966-quotient-equivalent-p
    subgroup-h multiplication inverse x y)
   (q1065966-quotient-equivalent-p
    subgroup-n multiplication inverse x y)))

(defun q1065966-second-canonical-forward (representative)
  representative)

(defun-sk q1065966-h-representative-mod-n-p
    (subgroup-h subgroup-n multiplication inverse element)
  (exists (h)
    (and
     (q1065966-member-p subgroup-h h)
     (q1065966-member-p
      subgroup-n
      (q1065966-multiply
       multiplication
       (q1065966-invert inverse h)
       element)))))

(defun-sk q1065966-second-canonical-isomorphism-p
    (subgroup-h subgroup-n multiplication inverse)
  (forall (x y z)
    (and
     (implies
      (q1065966-member-p subgroup-h x)
      (q1065966-product-member-p
       subgroup-h
       subgroup-n
       multiplication
       (q1065966-second-canonical-forward x)))
     (implies
      (and
       (q1065966-member-p subgroup-h x)
       (q1065966-member-p subgroup-h y))
      (and
       (iff
        (q1065966-second-domain-equivalent-p
         subgroup-h subgroup-n multiplication inverse x y)
        (q1065966-quotient-equivalent-p
         subgroup-n
         multiplication
         inverse
         (q1065966-second-canonical-forward x)
         (q1065966-second-canonical-forward y)))
       (q1065966-quotient-equivalent-p
        subgroup-n
        multiplication
        inverse
        (q1065966-second-canonical-forward
         (q1065966-multiply multiplication x y))
        (q1065966-multiply
         multiplication
         (q1065966-second-canonical-forward x)
         (q1065966-second-canonical-forward y)))))
     (implies
      (q1065966-product-member-p
       subgroup-h subgroup-n multiplication z)
      (q1065966-h-representative-mod-n-p
       subgroup-h subgroup-n multiplication inverse z)))))

(defun thousand-theorems-q1065966-quotient-inf-equiv-prod-normal-quotient-statement
    (carrier
     multiplication
     inverse
     identity
     subgroup-h
     subgroup-n)
  (implies
   (and
    (q1065966-subgroup-p
     carrier multiplication inverse identity subgroup-h)
    (q1065966-normal-subgroup-p
     carrier multiplication inverse identity subgroup-n))
   (q1065966-second-canonical-isomorphism-p
    subgroup-h subgroup-n multiplication inverse)))

;; An element xN lies in M/N exactly when it has an M-representative.

(defun-sk q1065966-mapped-m-member-p
    (subgroup-n subgroup-m multiplication inverse element)
  (exists (representative)
    (and
     (q1065966-member-p subgroup-m representative)
     (q1065966-quotient-equivalent-p
      subgroup-n
      multiplication
      inverse
      representative
      element))))

(defun q1065966-iterated-quotient-equivalent-p
    (subgroup-n subgroup-m multiplication inverse x y)
  (q1065966-mapped-m-member-p
   subgroup-n
   subgroup-m
   multiplication
   inverse
   (q1065966-multiply
    multiplication
    (q1065966-invert inverse x)
    y)))

;; The forward and inverse maps are both induced by the identity on
;; G-representatives, but use the two different quotient relations.

(defun q1065966-third-canonical-forward (representative)
  representative)

(defun q1065966-third-canonical-inverse (representative)
  representative)

;; These clauses state well-definedness in both directions, inverse laws on
;; equivalence classes, and preservation of quotient multiplication.

(defun-sk q1065966-third-canonical-isomorphism-p
    (carrier subgroup-n subgroup-m multiplication inverse)
  (forall (x y)
    (and
     (implies
      (q1065966-member-p carrier x)
      (and
       (q1065966-member-p
        carrier
        (q1065966-third-canonical-forward x))
       (q1065966-member-p
        carrier
        (q1065966-third-canonical-inverse x))
       (q1065966-iterated-quotient-equivalent-p
        subgroup-n
        subgroup-m
        multiplication
        inverse
        (q1065966-third-canonical-inverse
         (q1065966-third-canonical-forward x))
        x)
       (q1065966-quotient-equivalent-p
        subgroup-m
        multiplication
        inverse
        (q1065966-third-canonical-forward
         (q1065966-third-canonical-inverse x))
        x)))
     (implies
      (and
       (q1065966-member-p carrier x)
       (q1065966-member-p carrier y))
      (and
       (implies
        (q1065966-iterated-quotient-equivalent-p
         subgroup-n subgroup-m multiplication inverse x y)
        (q1065966-quotient-equivalent-p
         subgroup-m
         multiplication
         inverse
         (q1065966-third-canonical-forward x)
         (q1065966-third-canonical-forward y)))
       (implies
        (q1065966-quotient-equivalent-p
         subgroup-m multiplication inverse x y)
        (q1065966-iterated-quotient-equivalent-p
         subgroup-n
         subgroup-m
         multiplication
         inverse
         (q1065966-third-canonical-inverse x)
         (q1065966-third-canonical-inverse y)))
       (q1065966-quotient-equivalent-p
        subgroup-m
        multiplication
        inverse
        (q1065966-third-canonical-forward
         (q1065966-multiply multiplication x y))
        (q1065966-multiply
         multiplication
         (q1065966-third-canonical-forward x)
         (q1065966-third-canonical-forward y)))
       (q1065966-iterated-quotient-equivalent-p
        subgroup-n
        subgroup-m
        multiplication
        inverse
        (q1065966-third-canonical-inverse
         (q1065966-multiply multiplication x y))
        (q1065966-multiply
         multiplication
         (q1065966-third-canonical-inverse x)
         (q1065966-third-canonical-inverse y))))))))

(defun thousand-theorems-q1065966-quotient-quotient-equiv-quotient-statement
    (carrier
     multiplication
     inverse
     identity
     subgroup-n
     subgroup-m)
  (implies
   (and
    (q1065966-normal-subgroup-p
     carrier multiplication inverse identity subgroup-n)
    (q1065966-normal-subgroup-p
     carrier multiplication inverse identity subgroup-m)
    (q1065966-subset-p subgroup-n subgroup-m))
   (q1065966-third-canonical-isomorphism-p
    carrier subgroup-n subgroup-m multiplication inverse)))

(value-triple :itpeval-statement-checked)
:q
