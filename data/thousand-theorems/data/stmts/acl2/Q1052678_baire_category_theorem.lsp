;; Statement-only formalization of thousand-theorems corpus artifact Q1052678,
;; "Baire category theorem": in an arbitrary Baire topological space, the
;; intersection of a countable family of dense open sets is dense. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame characteristic functions represent the carrier, subsets, families of
;; subsets, and natural-number sequences. DEFUN-SK keeps every point, set,
;; family, enumeration, and sequence in its source quantifier scope. APPLY$ is
;; used only to apply those externally supplied characteristic functions.

(defun q1052678-member-p (predicate object)
  (if (apply$ predicate (list object))
      t
    nil))

(defun q1052678-value (function argument)
  (apply$ function (list argument)))

;; Extensional subsets and arbitrary families of subsets.

(defun-sk q1052678-set-contained-p (carrier set)
  (forall (x)
    (implies
     (q1052678-member-p set x)
     (q1052678-member-p carrier x))))

(defun q1052678-valid-set-p (carrier set)
  (and
   (tamep-functionp carrier)
   (tamep-functionp set)
   (q1052678-set-contained-p carrier set)))

(defun-sk q1052678-set-pointwise-equiv-p
    (carrier left right)
  (forall (x)
    (implies
     (q1052678-member-p carrier x)
     (iff
      (q1052678-member-p left x)
      (q1052678-member-p right x)))))

(defun q1052678-set-equiv-p (carrier left right)
  (and
   (q1052678-valid-set-p carrier left)
   (q1052678-valid-set-p carrier right)
   (q1052678-set-pointwise-equiv-p
    carrier left right)))

(defun-sk q1052678-family-extensional-p
    (carrier family)
  (forall (left right)
    (implies
     (and
      (q1052678-valid-set-p carrier left)
      (q1052678-valid-set-p carrier right)
      (q1052678-set-equiv-p carrier left right))
     (iff
      (q1052678-member-p family left)
      (q1052678-member-p family right)))))

(defun-sk q1052678-family-members-valid-p
    (carrier family)
  (forall (set)
    (implies
     (q1052678-member-p family set)
     (q1052678-valid-set-p carrier set))))

(defun q1052678-family-of-sets-p
    (carrier family)
  (and
   (tamep-functionp carrier)
   (tamep-functionp family)
   (q1052678-family-extensional-p carrier family)
   (q1052678-family-members-valid-p
    carrier family)))

(defun-sk q1052678-set-has-point-p (carrier set)
  (exists (x)
    (and
     (q1052678-member-p carrier x)
     (q1052678-member-p set x))))

(defun q1052678-set-nonempty-p (carrier set)
  (and
   (q1052678-valid-set-p carrier set)
   (q1052678-set-has-point-p carrier set)))

(defun-sk q1052678-intersection-has-point-p
    (carrier left right)
  (exists (x)
    (and
     (q1052678-member-p carrier x)
     (q1052678-member-p left x)
     (q1052678-member-p right x))))

(defun q1052678-intersection-nonempty-p
    (carrier left right)
  (and
   (q1052678-valid-set-p carrier left)
   (q1052678-valid-set-p carrier right)
   (q1052678-intersection-has-point-p
    carrier left right)))

;; Topological spaces, with empty set, whole carrier, binary intersections,
;; and arbitrary unions represented extensionally.

(defun q1052678-open-set-p
    (carrier topology set)
  (and
   (q1052678-valid-set-p carrier set)
   (q1052678-member-p topology set)))

(defun-sk q1052678-family-members-open-p
    (carrier topology family)
  (forall (set)
    (implies
     (q1052678-member-p family set)
     (q1052678-open-set-p
      carrier topology set))))

(defun-sk q1052678-empty-representation-p
    (carrier set)
  (forall (x)
    (implies
     (q1052678-member-p carrier x)
     (not (q1052678-member-p set x)))))

(defun-sk q1052678-open-empty-exists-p
    (carrier topology)
  (exists (set)
    (and
     (q1052678-open-set-p carrier topology set)
     (q1052678-empty-representation-p
      carrier set))))

(defun-sk q1052678-full-representation-p
    (carrier set)
  (forall (x)
    (implies
     (q1052678-member-p carrier x)
     (q1052678-member-p set x))))

(defun-sk q1052678-open-full-exists-p
    (carrier topology)
  (exists (set)
    (and
     (q1052678-open-set-p carrier topology set)
     (q1052678-full-representation-p
      carrier set))))

(defun-sk q1052678-intersection-representation-p
    (carrier left right intersection)
  (forall (x)
    (implies
     (q1052678-member-p carrier x)
     (iff
      (q1052678-member-p intersection x)
      (and
       (q1052678-member-p left x)
       (q1052678-member-p right x))))))

(defun-sk q1052678-open-intersection-exists-p
    (carrier topology left right)
  (exists (intersection)
    (and
     (q1052678-open-set-p
      carrier topology intersection)
     (q1052678-intersection-representation-p
      carrier left right intersection))))

(defun-sk q1052678-topology-intersection-law-p
    (carrier topology)
  (forall (left right)
    (implies
     (and
      (q1052678-open-set-p
       carrier topology left)
      (q1052678-open-set-p
       carrier topology right))
     (q1052678-open-intersection-exists-p
      carrier topology left right))))

(defun-sk q1052678-family-union-contains-p
    (carrier family x)
  (exists (set)
    (and
     (q1052678-valid-set-p carrier set)
     (q1052678-member-p family set)
     (q1052678-member-p set x))))

(defun-sk q1052678-union-representation-p
    (carrier family union)
  (forall (x)
    (implies
     (q1052678-member-p carrier x)
     (iff
      (q1052678-member-p union x)
      (q1052678-family-union-contains-p
       carrier family x)))))

(defun-sk q1052678-open-union-exists-p
    (carrier topology family)
  (exists (union)
    (and
     (q1052678-open-set-p carrier topology union)
     (q1052678-union-representation-p
      carrier family union))))

(defun-sk q1052678-topology-union-law-p
    (carrier topology)
  (forall (family)
    (implies
     (and
      (q1052678-family-of-sets-p
       carrier family)
      (q1052678-family-members-open-p
       carrier topology family))
     (q1052678-open-union-exists-p
      carrier topology family))))

(defun q1052678-topological-space-p
    (carrier topology)
  (and
   (q1052678-family-of-sets-p carrier topology)
   (q1052678-open-empty-exists-p
    carrier topology)
   (q1052678-open-full-exists-p
    carrier topology)
   (q1052678-topology-intersection-law-p
    carrier topology)
   (q1052678-topology-union-law-p
    carrier topology)))

;; Density is the equivalent open-set characterization: every nonempty open
;; subset of the carrier meets the given set.

(defun-sk q1052678-dense-open-meeting-exists-p
    (carrier set open)
  (exists (x)
    (and
     (q1052678-member-p carrier x)
     (q1052678-member-p set x)
     (q1052678-member-p open x))))

(defun-sk q1052678-dense-open-law-p
    (carrier topology set)
  (forall (open)
    (implies
     (and
      (q1052678-open-set-p
       carrier topology open)
      (q1052678-set-nonempty-p carrier open))
     (q1052678-dense-open-meeting-exists-p
      carrier set open))))

(defun q1052678-dense-set-p
    (carrier topology set)
  (and
   (q1052678-valid-set-p carrier set)
   (q1052678-dense-open-law-p
    carrier topology set)))

(defun-sk q1052678-family-members-dense-p
    (carrier topology family)
  (forall (set)
    (implies
     (q1052678-member-p family set)
     (q1052678-dense-set-p
      carrier topology set))))

;; Countability is an internal existential enumeration by natural numbers,
;; covering the family up to extensional equality.

(defun-sk q1052678-enumeration-hits-set-p
    (carrier enumeration set)
  (exists (n)
    (and
     (natp n)
     (q1052678-set-equiv-p
      carrier
      (q1052678-value enumeration n)
      set))))

(defun-sk q1052678-enumeration-covers-p
    (carrier family enumeration)
  (forall (set)
    (implies
     (q1052678-member-p family set)
     (q1052678-enumeration-hits-set-p
      carrier enumeration set))))

(defun-sk q1052678-countable-family-witness-p
    (carrier family)
  (exists (enumeration)
    (and
     (tamep-functionp enumeration)
     (q1052678-enumeration-covers-p
      carrier family enumeration))))

(defun q1052678-countable-family-p
    (carrier family)
  (and
   (q1052678-family-of-sets-p carrier family)
   (q1052678-countable-family-witness-p
    carrier family)))

;; The set-theoretic intersection of a family is represented directly by its
;; membership condition, without constructing a lambda term.

(defun-sk q1052678-family-intersection-point-p
    (family x)
  (forall (set)
    (implies
     (q1052678-member-p family set)
     (q1052678-member-p set x))))

(defun-sk q1052678-family-intersection-meets-open-p
    (carrier family open)
  (exists (x)
    (and
     (q1052678-member-p carrier x)
     (q1052678-member-p open x)
     (q1052678-family-intersection-point-p
      family x))))

(defun-sk q1052678-family-intersection-dense-p
    (carrier topology family)
  (forall (open)
    (implies
     (and
      (q1052678-open-set-p
       carrier topology open)
      (q1052678-set-nonempty-p carrier open))
     (q1052678-family-intersection-meets-open-p
      carrier family open))))

;; A Baire space is one in which every natural-number sequence of dense open
;; sets has dense intersection.

(defun-sk q1052678-sequence-of-sets-p
    (carrier sequence)
  (forall (n)
    (implies
     (natp n)
     (q1052678-valid-set-p
      carrier (q1052678-value sequence n)))))

(defun-sk q1052678-sequence-members-open-p
    (carrier topology sequence)
  (forall (n)
    (implies
     (natp n)
     (q1052678-open-set-p
      carrier
      topology
      (q1052678-value sequence n)))))

(defun-sk q1052678-sequence-members-dense-p
    (carrier topology sequence)
  (forall (n)
    (implies
     (natp n)
     (q1052678-dense-set-p
      carrier
      topology
      (q1052678-value sequence n)))))

(defun-sk q1052678-sequence-intersection-point-p
    (sequence x)
  (forall (n)
    (implies
     (natp n)
     (q1052678-member-p
      (q1052678-value sequence n) x))))

(defun-sk q1052678-sequence-intersection-meets-open-p
    (carrier sequence open)
  (exists (x)
    (and
     (q1052678-member-p carrier x)
     (q1052678-member-p open x)
     (q1052678-sequence-intersection-point-p
      sequence x))))

(defun-sk q1052678-sequence-intersection-dense-p
    (carrier topology sequence)
  (forall (open)
    (implies
     (and
      (q1052678-open-set-p
       carrier topology open)
      (q1052678-set-nonempty-p carrier open))
     (q1052678-sequence-intersection-meets-open-p
      carrier sequence open))))

(defun-sk q1052678-baire-sequence-law-p
    (carrier topology)
  (forall (sequence)
    (implies
     (and
      (tamep-functionp sequence)
      (q1052678-sequence-of-sets-p
       carrier sequence)
      (q1052678-sequence-members-open-p
       carrier topology sequence)
      (q1052678-sequence-members-dense-p
       carrier topology sequence))
     (q1052678-sequence-intersection-dense-p
      carrier topology sequence))))

(defun q1052678-baire-space-p
    (carrier topology)
  (and
   (q1052678-topological-space-p
    carrier topology)
   (q1052678-baire-sequence-law-p
    carrier topology)))

(defun thousand-theorems-q1052678-baire-category-statement
    (carrier topology family)
  (implies
   (and
    (q1052678-baire-space-p carrier topology)
    (q1052678-family-of-sets-p carrier family)
    (q1052678-family-members-open-p
     carrier topology family)
    (q1052678-countable-family-p
     carrier family)
    (q1052678-family-members-dense-p
     carrier topology family))
   (q1052678-family-intersection-dense-p
    carrier topology family)))

(value-triple :itpeval-statement-checked)
:q
