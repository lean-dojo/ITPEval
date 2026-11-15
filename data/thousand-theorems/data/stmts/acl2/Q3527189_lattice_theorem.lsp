;; Statement-only formalization of thousand-theorems corpus artifact Q3527189,
;; "Lattice theorem": Noether's third isomorphism theorem, giving the canonical
;; multiplicative equivalence (G/N)/(M/N) with G/M when N and M are normal
;; subgroups of G and N is contained in M. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ function objects represent the arbitrary carrier, operation,
;; inverse, and subgroup predicates. DEFUN-SK keeps all element and
;; representative quantifiers internal to the statement.

(defun q3527189-member-p (predicate element)
  (if (apply$ predicate (list element))
      t
    nil))

(defun q3527189-multiply (multiplication left right)
  (apply$ multiplication (list left right)))

(defun q3527189-invert (inverse element)
  (apply$ inverse (list element)))

(defun-sk q3527189-subset-p (left right)
  (forall (element)
    (implies
     (q3527189-member-p left element)
     (q3527189-member-p right element))))

(defun-sk q3527189-group-laws-p
    (carrier multiplication inverse identity)
  (forall (x y z)
    (and
     (implies
      (q3527189-member-p carrier x)
      (and
       (q3527189-member-p
        carrier
        (q3527189-invert inverse x))
       (equal
        (q3527189-multiply multiplication identity x)
        x)
       (equal
        (q3527189-multiply multiplication x identity)
        x)
       (equal
        (q3527189-multiply
         multiplication
         (q3527189-invert inverse x)
         x)
        identity)
       (equal
        (q3527189-multiply
         multiplication
         x
         (q3527189-invert inverse x))
        identity)))
     (implies
      (and
       (q3527189-member-p carrier x)
       (q3527189-member-p carrier y))
      (q3527189-member-p
       carrier
       (q3527189-multiply multiplication x y)))
     (implies
      (and
       (q3527189-member-p carrier x)
       (q3527189-member-p carrier y)
       (q3527189-member-p carrier z))
      (equal
       (q3527189-multiply
        multiplication
        (q3527189-multiply multiplication x y)
        z)
       (q3527189-multiply
        multiplication
        x
        (q3527189-multiply multiplication y z)))))))

(defun q3527189-group-p
    (carrier multiplication inverse identity)
  (and
   (tamep-functionp carrier)
   (tamep-functionp multiplication)
   (tamep-functionp inverse)
   (q3527189-member-p carrier identity)
   (q3527189-group-laws-p
    carrier multiplication inverse identity)))

(defun q3527189-subgroup-p
    (carrier multiplication inverse identity subgroup)
  (and
   (tamep-functionp subgroup)
   (q3527189-group-p
    carrier multiplication inverse identity)
   (q3527189-subset-p subgroup carrier)
   (q3527189-group-p
    subgroup multiplication inverse identity)))

(defun-sk q3527189-normal-laws-p
    (carrier subgroup multiplication inverse)
  (forall (conjugator element)
    (implies
     (and
      (q3527189-member-p carrier conjugator)
      (q3527189-member-p subgroup element))
     (q3527189-member-p
      subgroup
      (q3527189-multiply
       multiplication
       (q3527189-multiply multiplication conjugator element)
       (q3527189-invert inverse conjugator))))))

(defun q3527189-normal-subgroup-p
    (carrier multiplication inverse identity subgroup)
  (and
   (q3527189-subgroup-p
    carrier multiplication inverse identity subgroup)
   (q3527189-normal-laws-p
    carrier subgroup multiplication inverse)))

;; Equality of representatives modulo a normal subgroup K is
;; x^-1*y in K.

(defun q3527189-quotient-equivalent-p
    (subgroup multiplication inverse x y)
  (q3527189-member-p
   subgroup
   (q3527189-multiply
    multiplication
    (q3527189-invert inverse x)
    y)))

;; An element of M.map(mk N) is an N-coset having a representative in M.
;; The existential representative is internal, matching Subgroup.map.

(defun-sk q3527189-mapped-m-member-p
    (subgroup-n subgroup-m multiplication inverse element)
  (exists (representative)
    (and
     (q3527189-member-p subgroup-m representative)
     (q3527189-quotient-equivalent-p
      subgroup-n
      multiplication
      inverse
      representative
      element))))

;; Representatives x and y determine equal elements of
;; (G/N)/(M.map(mk N)) precisely when [x^-1*y]_N belongs to M.map(mk N).

(defun q3527189-iterated-quotient-equivalent-p
    (subgroup-n subgroup-m multiplication inverse x y)
  (q3527189-mapped-m-member-p
   subgroup-n
   subgroup-m
   multiplication
   inverse
   (q3527189-multiply
    multiplication
    (q3527189-invert inverse x)
    y)))

;; Both directions of the canonical equivalence are induced by the identity
;; on G-representatives, but their domains and equality relations differ.

(defun q3527189-canonical-forward (representative)
  representative)

(defun q3527189-canonical-inverse (representative)
  representative)

;; These laws are the quotient-presentation form of a MulEquiv. They state
;; that the canonical forward and inverse maps are well-defined, inverse on
;; equivalence classes (hence bijective), and preserve quotient multiplication.

(defun-sk q3527189-canonical-multiplicative-equivalence-p
    (carrier subgroup-n subgroup-m multiplication inverse)
  (forall (x y)
    (and
     (implies
      (q3527189-member-p carrier x)
      (and
       (q3527189-member-p
        carrier
        (q3527189-canonical-forward x))
       (q3527189-member-p
        carrier
        (q3527189-canonical-inverse x))
       (q3527189-iterated-quotient-equivalent-p
        subgroup-n
        subgroup-m
        multiplication
        inverse
        (q3527189-canonical-inverse
         (q3527189-canonical-forward x))
        x)
       (q3527189-quotient-equivalent-p
        subgroup-m
        multiplication
        inverse
        (q3527189-canonical-forward
         (q3527189-canonical-inverse x))
        x)))
     (implies
      (and
       (q3527189-member-p carrier x)
       (q3527189-member-p carrier y))
      (and
       (implies
        (q3527189-iterated-quotient-equivalent-p
         subgroup-n subgroup-m multiplication inverse x y)
        (q3527189-quotient-equivalent-p
         subgroup-m
         multiplication
         inverse
         (q3527189-canonical-forward x)
         (q3527189-canonical-forward y)))
       (implies
        (q3527189-quotient-equivalent-p
         subgroup-m multiplication inverse x y)
        (q3527189-iterated-quotient-equivalent-p
         subgroup-n
         subgroup-m
         multiplication
         inverse
         (q3527189-canonical-inverse x)
         (q3527189-canonical-inverse y)))
       (q3527189-quotient-equivalent-p
        subgroup-m
        multiplication
        inverse
        (q3527189-canonical-forward
         (q3527189-multiply multiplication x y))
        (q3527189-multiply
         multiplication
         (q3527189-canonical-forward x)
         (q3527189-canonical-forward y)))
       (q3527189-iterated-quotient-equivalent-p
        subgroup-n
        subgroup-m
        multiplication
        inverse
        (q3527189-canonical-inverse
         (q3527189-multiply multiplication x y))
        (q3527189-multiply
         multiplication
         (q3527189-canonical-inverse x)
         (q3527189-canonical-inverse y))))))))

(defun thousand-theorems-q3527189-lattice-theorem-statement
    (carrier
     multiplication
     inverse
     identity
     subgroup-n
     subgroup-m)
  (implies
   (and
    (q3527189-normal-subgroup-p
     carrier multiplication inverse identity subgroup-n)
    (q3527189-normal-subgroup-p
     carrier multiplication inverse identity subgroup-m)
    (q3527189-subset-p subgroup-n subgroup-m))
   (q3527189-canonical-multiplicative-equivalence-p
    carrier subgroup-n subgroup-m multiplication inverse)))

(value-triple :itpeval-statement-checked)
:q
