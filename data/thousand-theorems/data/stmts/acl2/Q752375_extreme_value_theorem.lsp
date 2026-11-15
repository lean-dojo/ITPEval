;; Statement-only formalization of thousand-theorems corpus artifact Q752375,
;; "Extreme value theorem": a continuous function from a nonempty compact set
;; into a linearly ordered space with closed lower rays attains its minimum.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ functions represent arbitrary carriers, extensional subsets,
;; families of subsets, topologies, the order, and the source function.
;; DEFUN-SK keeps every point, cover, neighborhood, and minimum witness in the
;; same quantifier scope as the corresponding Lean statement.

(defun q752375-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun q752375-relation-p (relation left right)
  (if (apply$ relation (list left right)) t nil))

(defun q752375-value (function argument)
  (apply$ function (list argument)))

;; Extensional subsets and arbitrary families of subsets.

(defun-sk q752375-set-contained-p (carrier set)
  (forall (x)
    (implies
     (q752375-member-p set x)
     (q752375-member-p carrier x))))

(defun q752375-valid-set-p (carrier set)
  (and
   (tamep-functionp carrier)
   (tamep-functionp set)
   (q752375-set-contained-p carrier set)))

(defun-sk q752375-set-equiv-p (carrier left right)
  (forall (x)
    (implies
     (q752375-member-p carrier x)
     (iff
      (q752375-member-p left x)
      (q752375-member-p right x)))))

(defun-sk q752375-family-extensional-p (carrier family)
  (forall (left right)
    (implies
     (and
      (q752375-valid-set-p carrier left)
      (q752375-valid-set-p carrier right)
      (q752375-set-equiv-p carrier left right))
     (iff
      (q752375-member-p family left)
      (q752375-member-p family right)))))

(defun-sk q752375-family-members-valid-p (carrier family)
  (forall (set)
    (implies
     (q752375-member-p family set)
     (q752375-valid-set-p carrier set))))

(defun q752375-family-of-sets-p (carrier family)
  (and
   (tamep-functionp family)
   (q752375-family-extensional-p carrier family)
   (q752375-family-members-valid-p carrier family)))

(defun-sk q752375-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (q752375-member-p carrier x)
     (q752375-member-p set x))))

;; Topological spaces, including arbitrary unions.

(defun q752375-open-set-p (carrier topology set)
  (and
   (q752375-valid-set-p carrier set)
   (q752375-member-p topology set)))

(defun-sk q752375-empty-representation-p (carrier set)
  (forall (x)
    (implies
     (q752375-member-p carrier x)
     (not (q752375-member-p set x)))))

(defun-sk q752375-empty-open-exists-p (carrier topology)
  (exists (set)
    (and
     (q752375-valid-set-p carrier set)
     (q752375-empty-representation-p carrier set)
     (q752375-open-set-p carrier topology set))))

(defun-sk q752375-full-representation-p (carrier set)
  (forall (x)
    (implies
     (q752375-member-p carrier x)
     (q752375-member-p set x))))

(defun-sk q752375-full-open-exists-p (carrier topology)
  (exists (set)
    (and
     (q752375-valid-set-p carrier set)
     (q752375-full-representation-p carrier set)
     (q752375-open-set-p carrier topology set))))

(defun-sk q752375-intersection-representation-p
    (carrier left right intersection)
  (forall (x)
    (implies
     (q752375-member-p carrier x)
     (iff
      (q752375-member-p intersection x)
      (and
       (q752375-member-p left x)
       (q752375-member-p right x))))))

(defun-sk q752375-open-intersection-exists-p
    (carrier topology left right)
  (exists (intersection)
    (and
     (q752375-valid-set-p carrier intersection)
     (q752375-intersection-representation-p
      carrier left right intersection)
     (q752375-open-set-p carrier topology intersection))))

(defun-sk q752375-topology-intersection-law-p
    (carrier topology)
  (forall (left right)
    (implies
     (and
      (q752375-open-set-p carrier topology left)
      (q752375-open-set-p carrier topology right))
     (q752375-open-intersection-exists-p
      carrier topology left right))))

(defun-sk q752375-union-member-p (carrier family x)
  (exists (set)
    (and
     (q752375-valid-set-p carrier set)
     (q752375-member-p family set)
     (q752375-member-p set x))))

(defun-sk q752375-union-representation-p
    (carrier family union)
  (forall (x)
    (implies
     (q752375-member-p carrier x)
     (iff
      (q752375-member-p union x)
      (q752375-union-member-p carrier family x)))))

(defun-sk q752375-family-members-open-p
    (carrier topology family)
  (forall (set)
    (implies
     (q752375-member-p family set)
     (q752375-open-set-p carrier topology set))))

(defun-sk q752375-open-union-exists-p
    (carrier topology family)
  (exists (union)
    (and
     (q752375-valid-set-p carrier union)
     (q752375-union-representation-p carrier family union)
     (q752375-open-set-p carrier topology union))))

(defun-sk q752375-topology-union-law-p
    (carrier topology)
  (forall (family)
    (implies
     (and
      (q752375-family-of-sets-p carrier family)
      (q752375-family-members-open-p
       carrier topology family))
     (q752375-open-union-exists-p
      carrier topology family))))

(defun q752375-topological-space-p (carrier topology)
  (and
   (tamep-functionp carrier)
   (q752375-family-of-sets-p carrier topology)
   (q752375-empty-open-exists-p carrier topology)
   (q752375-full-open-exists-p carrier topology)
   (q752375-topology-intersection-law-p carrier topology)
   (q752375-topology-union-law-p carrier topology)))

;; Closed subsets and the ClosedIicTopology condition.

(defun-sk q752375-complement-representation-p
    (carrier set complement)
  (forall (x)
    (implies
     (q752375-member-p carrier x)
     (iff
      (q752375-member-p complement x)
      (not (q752375-member-p set x))))))

(defun-sk q752375-open-complement-exists-p
    (carrier topology set)
  (exists (complement)
    (and
     (q752375-valid-set-p carrier complement)
     (q752375-complement-representation-p
      carrier set complement)
     (q752375-open-set-p carrier topology complement))))

(defun q752375-closed-set-p (carrier topology set)
  (and
   (q752375-valid-set-p carrier set)
   (q752375-open-complement-exists-p
    carrier topology set)))

;; Linear orders.

(defun-sk q752375-linear-order-laws-p (carrier le)
  (forall (x y z)
    (and
     (implies
      (q752375-member-p carrier x)
      (q752375-relation-p le x x))
     (implies
      (and
       (q752375-member-p carrier x)
       (q752375-member-p carrier y)
       (q752375-relation-p le x y)
       (q752375-relation-p le y x))
      (equal x y))
     (implies
      (and
       (q752375-member-p carrier x)
       (q752375-member-p carrier y)
       (q752375-member-p carrier z)
       (q752375-relation-p le x y)
       (q752375-relation-p le y z))
      (q752375-relation-p le x z))
     (implies
      (and
       (q752375-member-p carrier x)
       (q752375-member-p carrier y))
      (or
       (q752375-relation-p le x y)
       (q752375-relation-p le y x))))))

(defun q752375-linear-order-p (carrier le)
  (and
   (tamep-functionp carrier)
   (tamep-functionp le)
   (q752375-linear-order-laws-p carrier le)))

(defun-sk q752375-iic-representation-p
    (carrier le endpoint iic)
  (forall (x)
    (implies
     (q752375-member-p carrier x)
     (iff
      (q752375-member-p iic x)
      (q752375-relation-p le x endpoint)))))

(defun-sk q752375-closed-iic-exists-p
    (carrier le topology endpoint)
  (exists (iic)
    (and
     (q752375-valid-set-p carrier iic)
     (q752375-iic-representation-p
      carrier le endpoint iic)
     (q752375-closed-set-p carrier topology iic))))

(defun-sk q752375-closed-iic-topology-p
    (carrier le topology)
  (forall (endpoint)
    (implies
     (q752375-member-p carrier endpoint)
     (q752375-closed-iic-exists-p
      carrier le topology endpoint))))

;; Compactness via unrestricted open covers and internal finite subcovers.

(defun-sk q752375-cover-p (carrier set family)
  (forall (x)
    (implies
     (and
      (q752375-member-p carrier x)
      (q752375-member-p set x))
     (q752375-union-member-p carrier family x))))

(defun q752375-finite-subcover-elements-p
    (sets carrier family)
  (if (consp sets)
      (and
       (q752375-valid-set-p carrier (car sets))
       (q752375-member-p family (car sets))
       (q752375-finite-subcover-elements-p
        (cdr sets) carrier family))
    (equal sets nil)))

(defun q752375-finite-subcover-point-p (sets x)
  (if (consp sets)
      (or
       (q752375-member-p (car sets) x)
       (q752375-finite-subcover-point-p (cdr sets) x))
    nil))

(defun-sk q752375-finite-subcover-covers-p
    (carrier set sets)
  (forall (x)
    (implies
     (and
      (q752375-member-p carrier x)
      (q752375-member-p set x))
     (q752375-finite-subcover-point-p sets x))))

(defun q752375-finite-subcover-p
    (sets carrier set family)
  (and
   (true-listp sets)
   (q752375-finite-subcover-elements-p
    sets carrier family)
   (q752375-finite-subcover-covers-p
    carrier set sets)))

(defun-sk q752375-finite-subcover-exists-p
    (carrier set family)
  (exists (sets)
    (q752375-finite-subcover-p
     sets carrier set family)))

(defun-sk q752375-compact-cover-law-p
    (carrier topology set)
  (forall (family)
    (implies
     (and
      (q752375-family-of-sets-p carrier family)
      (q752375-family-members-open-p
       carrier topology family)
      (q752375-cover-p carrier set family))
     (q752375-finite-subcover-exists-p
      carrier set family))))

(defun q752375-compact-set-p (carrier topology set)
  (and
   (q752375-valid-set-p carrier set)
   (q752375-compact-cover-law-p
    carrier topology set)))

;; Typed functions and continuity on a subset, expressed by the exact local
;; open-neighborhood characterization of ContinuousOn.

(defun-sk q752375-function-values-p
    (domain codomain function)
  (forall (x)
    (implies
     (q752375-member-p domain x)
     (q752375-member-p
      codomain (q752375-value function x)))))

(defun q752375-function-p (domain codomain function)
  (and
   (tamep-functionp function)
   (q752375-function-values-p
    domain codomain function)))

(defun-sk q752375-local-image-contained-p
    (domain set source-open function target-open)
  (forall (y)
    (implies
     (and
      (q752375-member-p domain y)
      (q752375-member-p set y)
      (q752375-member-p source-open y))
     (q752375-member-p
      target-open (q752375-value function y)))))

(defun q752375-continuity-neighborhood-witness-p
    (domain domain-topology set function
     target-open x source-open)
  (and
   (q752375-open-set-p
    domain domain-topology source-open)
   (q752375-member-p source-open x)
   (q752375-local-image-contained-p
    domain set source-open function target-open)))

(defun-sk q752375-continuity-neighborhood-exists-p
    (domain domain-topology set function target-open x)
  (exists (source-open)
    (q752375-continuity-neighborhood-witness-p
     domain domain-topology set function
     target-open x source-open)))

(defun-sk q752375-continuous-within-at-p
    (domain domain-topology codomain codomain-topology
     set function x)
  (forall (target-open)
    (implies
     (and
      (q752375-open-set-p
       codomain codomain-topology target-open)
      (q752375-member-p
       target-open (q752375-value function x)))
     (q752375-continuity-neighborhood-exists-p
      domain domain-topology set function target-open x))))

(defun-sk q752375-continuous-on-p
    (domain domain-topology codomain codomain-topology
     set function)
  (forall (x)
    (implies
     (and
      (q752375-member-p domain x)
      (q752375-member-p set x))
     (q752375-continuous-within-at-p
      domain domain-topology codomain codomain-topology
      set function x))))

;; The minimum witness remains existentially quantified inside the conclusion.

(defun-sk q752375-minimum-on-p
    (domain codomain le set function x)
  (forall (y)
    (implies
     (and
      (q752375-member-p domain y)
      (q752375-member-p set y))
     (q752375-relation-p
      le
      (q752375-value function x)
      (q752375-value function y)))))

(defun-sk q752375-minimum-witness-exists-p
    (domain codomain le set function)
  (exists (x)
    (and
     (q752375-member-p domain x)
     (q752375-member-p set x)
     (q752375-member-p
      codomain (q752375-value function x))
     (q752375-minimum-on-p
      domain codomain le set function x))))

;; IsCompact.exists_isMinOn
(defun-sk
    thousand-theorems-q752375-extreme-value-theorem-statement
    ()
  (forall
    (alpha alpha-le alpha-topology
     beta beta-topology set function)
    (implies
     (and
      (q752375-linear-order-p alpha alpha-le)
      (q752375-topological-space-p alpha alpha-topology)
      (q752375-closed-iic-topology-p
       alpha alpha-le alpha-topology)
      (q752375-topological-space-p beta beta-topology)
      (q752375-valid-set-p beta set)
      (q752375-compact-set-p beta beta-topology set)
      (q752375-set-nonempty-p beta set)
      (q752375-function-p beta alpha function)
      (q752375-continuous-on-p
       beta beta-topology alpha alpha-topology
       set function))
     (q752375-minimum-witness-exists-p
      beta alpha alpha-le set function))))

(value-triple :itpeval-statement-checked)
:q
