;; Statement-only formalization of thousand-theorems corpus artifact Q1346677,
;; "Tietze extension theorem": a bounded continuous real-valued function along
;; a closed embedding into a normal space has a bounded continuous extension
;; with the same supremum norm. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Arbitrary carriers, sets, topologies, and maps are represented by tame
;; APPLY$ function objects. Real numbers are represented exactly by paired
;; rational Dedekind cuts. Rational open intervals form a basis for the real
;; topology, and rational upper cuts determine the supremum norm. DEFUN-SK
;; keeps the extension map and all other existential witnesses internal.

(defun q1346677-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun q1346677-value (function object)
  (apply$ function (list object)))

;; Extensional subsets and arbitrary families of subsets.

(defun-sk q1346677-set-contained-p (carrier set)
  (forall (x)
    (implies
     (q1346677-member-p set x)
     (q1346677-member-p carrier x))))

(defun q1346677-valid-set-p (carrier set)
  (and
   (tamep-functionp carrier)
   (tamep-functionp set)
   (q1346677-set-contained-p carrier set)))

(defun-sk q1346677-set-equiv-p (carrier left right)
  (forall (x)
    (implies
     (q1346677-member-p carrier x)
     (iff
      (q1346677-member-p left x)
      (q1346677-member-p right x)))))

(defun-sk q1346677-family-extensional-p (carrier family)
  (forall (left right)
    (implies
     (and
      (q1346677-valid-set-p carrier left)
      (q1346677-valid-set-p carrier right)
      (q1346677-set-equiv-p carrier left right))
     (iff
      (q1346677-member-p family left)
      (q1346677-member-p family right)))))

(defun-sk q1346677-family-members-valid-p (carrier family)
  (forall (set)
    (implies
     (q1346677-member-p family set)
     (q1346677-valid-set-p carrier set))))

(defun q1346677-family-of-sets-p (carrier family)
  (and
   (tamep-functionp family)
   (q1346677-family-extensional-p carrier family)
   (q1346677-family-members-valid-p carrier family)))

(defun q1346677-open-set-p (carrier topology set)
  (and
   (q1346677-valid-set-p carrier set)
   (q1346677-member-p topology set)))

(defun-sk q1346677-family-members-open-p
    (carrier topology family)
  (forall (set)
    (implies
     (q1346677-member-p family set)
     (q1346677-open-set-p carrier topology set))))

(defun-sk q1346677-empty-representation-p (carrier set)
  (forall (x)
    (implies
     (q1346677-member-p carrier x)
     (not (q1346677-member-p set x)))))

(defun-sk q1346677-full-representation-p (carrier set)
  (forall (x)
    (implies
     (q1346677-member-p carrier x)
     (q1346677-member-p set x))))

(defun-sk q1346677-intersection-representation-p
    (carrier left right intersection)
  (forall (x)
    (implies
     (q1346677-member-p carrier x)
     (iff
      (q1346677-member-p intersection x)
      (and
       (q1346677-member-p left x)
       (q1346677-member-p right x))))))

(defun-sk q1346677-union-member-p (carrier family x)
  (exists (set)
    (and
     (q1346677-valid-set-p carrier set)
     (q1346677-member-p family set)
     (q1346677-member-p set x))))

(defun-sk q1346677-union-representation-p
    (carrier family union)
  (forall (x)
    (implies
     (q1346677-member-p carrier x)
     (iff
      (q1346677-member-p union x)
      (q1346677-union-member-p carrier family x)))))

(defun-sk q1346677-empty-open-exists-p (carrier topology)
  (exists (set)
    (and
     (q1346677-valid-set-p carrier set)
     (q1346677-empty-representation-p carrier set)
     (q1346677-open-set-p carrier topology set))))

(defun-sk q1346677-full-open-exists-p (carrier topology)
  (exists (set)
    (and
     (q1346677-valid-set-p carrier set)
     (q1346677-full-representation-p carrier set)
     (q1346677-open-set-p carrier topology set))))

(defun-sk q1346677-intersection-open-exists-p
    (carrier topology left right)
  (exists (intersection)
    (and
     (q1346677-valid-set-p carrier intersection)
     (q1346677-intersection-representation-p
      carrier left right intersection)
     (q1346677-open-set-p
      carrier topology intersection))))

(defun-sk q1346677-union-open-exists-p
    (carrier topology family)
  (exists (union)
    (and
     (q1346677-valid-set-p carrier union)
     (q1346677-union-representation-p
      carrier family union)
     (q1346677-open-set-p carrier topology union))))

(defun-sk q1346677-topology-closure-laws-p
    (carrier topology)
  (forall (left right family)
    (and
     (implies
      (and
       (q1346677-open-set-p carrier topology left)
       (q1346677-open-set-p carrier topology right))
      (q1346677-intersection-open-exists-p
       carrier topology left right))
     (implies
      (and
       (q1346677-family-of-sets-p carrier family)
       (q1346677-family-members-open-p
        carrier topology family))
      (q1346677-union-open-exists-p
       carrier topology family)))))

(defun q1346677-topological-space-p (carrier topology)
  (and
   (tamep-functionp carrier)
   (q1346677-family-of-sets-p carrier topology)
   (q1346677-empty-open-exists-p carrier topology)
   (q1346677-full-open-exists-p carrier topology)
   (q1346677-topology-closure-laws-p carrier topology)))

;; Closed subsets and normality.

(defun-sk q1346677-complement-representation-p
    (carrier set complement)
  (forall (x)
    (implies
     (q1346677-member-p carrier x)
     (iff
      (q1346677-member-p complement x)
      (not (q1346677-member-p set x))))))

(defun-sk q1346677-open-complement-exists-p
    (carrier topology set)
  (exists (complement)
    (and
     (q1346677-valid-set-p carrier complement)
     (q1346677-complement-representation-p
      carrier set complement)
     (q1346677-open-set-p
      carrier topology complement))))

(defun q1346677-closed-set-p (carrier topology set)
  (and
   (q1346677-valid-set-p carrier set)
   (q1346677-open-complement-exists-p
    carrier topology set)))

(defun-sk q1346677-set-subset-p (carrier left right)
  (forall (x)
    (implies
     (and
      (q1346677-member-p carrier x)
      (q1346677-member-p left x))
     (q1346677-member-p right x))))

(defun-sk q1346677-disjoint-sets-p (carrier left right)
  (forall (x)
    (implies
     (q1346677-member-p carrier x)
     (not
      (and
       (q1346677-member-p left x)
       (q1346677-member-p right x))))))

(defun-sk q1346677-normal-separation-exists-p
    (carrier topology left right)
  (exists (left-open right-open)
    (and
     (q1346677-open-set-p
      carrier topology left-open)
     (q1346677-open-set-p
      carrier topology right-open)
     (q1346677-set-subset-p
      carrier left left-open)
     (q1346677-set-subset-p
      carrier right right-open)
     (q1346677-disjoint-sets-p
      carrier left-open right-open))))

(defun-sk q1346677-normal-space-law-p
    (carrier topology)
  (forall (left right)
    (implies
     (and
      (q1346677-closed-set-p carrier topology left)
      (q1346677-closed-set-p carrier topology right)
      (q1346677-disjoint-sets-p carrier left right))
     (q1346677-normal-separation-exists-p
      carrier topology left right))))

(defun q1346677-normal-space-p (carrier topology)
  (and
   (q1346677-topological-space-p carrier topology)
   (q1346677-normal-space-law-p carrier topology)))

;; Exact real numbers as paired lower and upper rational Dedekind cuts.
;; LOWER(q) means q < x and UPPER(q) means x < q.

(defun q1346677-real-lower (real)
  (car real))

(defun q1346677-real-upper (real)
  (cdr real))

(defun q1346677-real-lower-p (real q)
  (if (apply$ (q1346677-real-lower real) (list q)) t nil))

(defun q1346677-real-upper-p (real q)
  (if (apply$ (q1346677-real-upper real) (list q)) t nil))

(defun-sk q1346677-lower-inhabited-p (real)
  (exists (q)
    (and
     (rationalp q)
     (q1346677-real-lower-p real q))))

(defun-sk q1346677-upper-inhabited-p (real)
  (exists (q)
    (and
     (rationalp q)
     (q1346677-real-upper-p real q))))

(defun-sk q1346677-lower-rounded-p (real q)
  (exists (r)
    (and
     (rationalp r)
     (< q r)
     (q1346677-real-lower-p real r))))

(defun-sk q1346677-upper-rounded-p (real q)
  (exists (r)
    (and
     (rationalp r)
     (< r q)
     (q1346677-real-upper-p real r))))

(defun-sk q1346677-real-cut-laws-p (real)
  (forall (q r)
    (and
     (implies
      (q1346677-real-lower-p real q)
      (rationalp q))
     (implies
      (q1346677-real-upper-p real q)
      (rationalp q))
     (implies
      (and
       (rationalp q)
       (rationalp r)
       (< r q)
       (q1346677-real-lower-p real q))
      (q1346677-real-lower-p real r))
     (implies
      (and
       (rationalp q)
       (q1346677-real-lower-p real q))
      (q1346677-lower-rounded-p real q))
     (implies
      (and
       (rationalp q)
       (rationalp r)
       (< q r)
       (q1346677-real-upper-p real q))
      (q1346677-real-upper-p real r))
     (implies
      (and
       (rationalp q)
       (q1346677-real-upper-p real q))
      (q1346677-upper-rounded-p real q))
     (implies
      (rationalp q)
      (not
       (and
        (q1346677-real-lower-p real q)
        (q1346677-real-upper-p real q))))
     (implies
      (and
       (rationalp q)
       (rationalp r)
       (< q r))
      (or
       (q1346677-real-lower-p real q)
       (q1346677-real-upper-p real r))))))

(defun q1346677-real-p (real)
  (and
   (consp real)
   (tamep-functionp (q1346677-real-lower real))
   (tamep-functionp (q1346677-real-upper real))
   (q1346677-lower-inhabited-p real)
   (q1346677-upper-inhabited-p real)
   (q1346677-real-cut-laws-p real)))

(defun-sk q1346677-real-equal-p (left right)
  (forall (q)
    (implies
     (rationalp q)
     (and
      (iff
       (q1346677-real-lower-p left q)
       (q1346677-real-lower-p right q))
      (iff
       (q1346677-real-upper-p left q)
       (q1346677-real-upper-p right q))))))

(defun q1346677-real-in-rational-interval-p
    (real left right)
  (and
   (rationalp left)
   (rationalp right)
   (< left right)
   (q1346677-real-lower-p real left)
   (q1346677-real-upper-p real right)))

(defun q1346677-real-abs-lt-p (real bound)
  (and
   (rationalp bound)
   (< 0 bound)
   (q1346677-real-lower-p real (- bound))
   (q1346677-real-upper-p real bound)))

;; Maps and continuity.

(defun-sk q1346677-map-into-p
    (source-carrier target-carrier mapping)
  (forall (x)
    (implies
     (q1346677-member-p source-carrier x)
     (q1346677-member-p
      target-carrier
      (q1346677-value mapping x)))))

(defun-sk q1346677-preimage-representation-p
    (source-carrier mapping target-set source-set)
  (forall (x)
    (implies
     (q1346677-member-p source-carrier x)
     (iff
      (q1346677-member-p source-set x)
      (q1346677-member-p
       target-set
       (q1346677-value mapping x))))))

(defun-sk q1346677-open-preimage-exists-p
    (source-carrier source-topology mapping target-set)
  (exists (source-set)
    (and
     (q1346677-valid-set-p source-carrier source-set)
     (q1346677-preimage-representation-p
      source-carrier mapping target-set source-set)
     (q1346677-open-set-p
      source-carrier source-topology source-set))))

(defun-sk q1346677-continuity-law-p
    (source-carrier source-topology
     target-carrier target-topology mapping)
  (forall (target-set)
    (implies
     (q1346677-open-set-p
      target-carrier target-topology target-set)
     (q1346677-open-preimage-exists-p
      source-carrier source-topology
      mapping target-set))))

(defun q1346677-continuous-map-p
    (source-carrier source-topology
     target-carrier target-topology mapping)
  (and
   (tamep-functionp mapping)
   (q1346677-map-into-p
    source-carrier target-carrier mapping)
   (q1346677-continuity-law-p
    source-carrier source-topology
    target-carrier target-topology mapping)))

;; Real-valued continuity uses all rational open intervals, an exact basis for
;; the usual topology on the Dedekind reals.

(defun-sk q1346677-real-valued-map-p (carrier mapping)
  (forall (x)
    (implies
     (q1346677-member-p carrier x)
     (q1346677-real-p
      (q1346677-value mapping x)))))

(defun-sk q1346677-interval-preimage-representation-p
    (carrier mapping left right set)
  (forall (x)
    (implies
     (q1346677-member-p carrier x)
     (iff
      (q1346677-member-p set x)
      (q1346677-real-in-rational-interval-p
       (q1346677-value mapping x)
       left right)))))

(defun-sk q1346677-interval-preimage-open-exists-p
    (carrier topology mapping left right)
  (exists (set)
    (and
     (q1346677-valid-set-p carrier set)
     (q1346677-interval-preimage-representation-p
      carrier mapping left right set)
     (q1346677-open-set-p carrier topology set))))

(defun-sk q1346677-real-continuity-law-p
    (carrier topology mapping)
  (forall (left right)
    (implies
     (and
      (rationalp left)
      (rationalp right)
      (< left right))
     (q1346677-interval-preimage-open-exists-p
      carrier topology mapping left right))))

(defun-sk q1346677-uniform-abs-bound-p
    (carrier mapping bound)
  (forall (x)
    (implies
     (q1346677-member-p carrier x)
     (q1346677-real-abs-lt-p
      (q1346677-value mapping x)
      bound))))

(defun-sk q1346677-bounded-map-p (carrier mapping)
  (exists (bound)
    (and
     (rationalp bound)
     (< 0 bound)
     (q1346677-uniform-abs-bound-p
      carrier mapping bound))))

(defun q1346677-bounded-continuous-real-map-p
    (carrier topology mapping)
  (and
   (tamep-functionp mapping)
   (q1346677-real-valued-map-p carrier mapping)
   (q1346677-real-continuity-law-p
    carrier topology mapping)
   (q1346677-bounded-map-p carrier mapping)))

;; NORM-LT(q) means that some rational r < q uniformly bounds all absolute
;; values. This is exactly the rational upper cut of the supremum norm.

(defun-sk q1346677-norm-lt-p (carrier mapping q)
  (exists (r)
    (and
     (rationalp q)
     (rationalp r)
     (< 0 r)
     (< r q)
     (q1346677-uniform-abs-bound-p
      carrier mapping r))))

(defun-sk q1346677-supremum-norm-equal-p
    (left-carrier left-map right-carrier right-map)
  (forall (q)
    (implies
     (and
      (rationalp q)
      (< 0 q))
     (iff
      (q1346677-norm-lt-p
       left-carrier left-map q)
      (q1346677-norm-lt-p
       right-carrier right-map q)))))

;; Closed embeddings: injective continuous maps inducing the source topology,
;; with closed range.

(defun-sk q1346677-injective-map-p (carrier mapping)
  (forall (left right)
    (implies
     (and
      (q1346677-member-p carrier left)
      (q1346677-member-p carrier right)
      (equal
       (q1346677-value mapping left)
       (q1346677-value mapping right)))
     (equal left right))))

(defun-sk q1346677-embedding-open-witness-p
    (source-carrier source-open
     target-carrier target-topology mapping)
  (exists (target-open)
    (and
     (q1346677-open-set-p
      target-carrier target-topology target-open)
     (q1346677-preimage-representation-p
      source-carrier mapping target-open source-open))))

(defun-sk q1346677-source-topology-induced-p
    (source-carrier source-topology
     target-carrier target-topology mapping)
  (forall (source-open)
    (implies
     (q1346677-open-set-p
      source-carrier source-topology source-open)
     (q1346677-embedding-open-witness-p
      source-carrier source-open
      target-carrier target-topology mapping))))

(defun-sk q1346677-range-member-p
    (source-carrier mapping y)
  (exists (x)
    (and
     (q1346677-member-p source-carrier x)
     (equal (q1346677-value mapping x) y))))

(defun-sk q1346677-range-representation-p
    (source-carrier target-carrier mapping range)
  (forall (y)
    (implies
     (q1346677-member-p target-carrier y)
     (iff
      (q1346677-member-p range y)
      (q1346677-range-member-p
       source-carrier mapping y)))))

(defun-sk q1346677-closed-range-exists-p
    (source-carrier target-carrier target-topology mapping)
  (exists (range)
    (and
     (q1346677-valid-set-p target-carrier range)
     (q1346677-range-representation-p
      source-carrier target-carrier mapping range)
     (q1346677-closed-set-p
      target-carrier target-topology range))))

(defun q1346677-closed-embedding-p
    (source-carrier source-topology
     target-carrier target-topology mapping)
  (and
   (q1346677-continuous-map-p
    source-carrier source-topology
    target-carrier target-topology mapping)
   (q1346677-injective-map-p
    source-carrier mapping)
   (q1346677-source-topology-induced-p
    source-carrier source-topology
    target-carrier target-topology mapping)
   (q1346677-closed-range-exists-p
    source-carrier target-carrier
    target-topology mapping)))

;; Extensional equality of the extension with the source function.

(defun-sk q1346677-extension-agrees-p
    (source-carrier embedding source-map extension-map)
  (forall (x)
    (implies
     (q1346677-member-p source-carrier x)
     (q1346677-real-equal-p
      (q1346677-value
       extension-map
       (q1346677-value embedding x))
      (q1346677-value source-map x)))))

(defun-sk q1346677-extension-exists-p
    (source-carrier target-carrier target-topology
     embedding source-map)
  (exists (extension-map)
    (and
     (q1346677-bounded-continuous-real-map-p
      target-carrier target-topology extension-map)
     (q1346677-supremum-norm-equal-p
      target-carrier extension-map
      source-carrier source-map)
     (q1346677-extension-agrees-p
      source-carrier embedding
      source-map extension-map))))

(defun thousand-theorems-q1346677-tietze-extension-theorem-statement
    (source-carrier source-topology
     target-carrier target-topology
     source-map embedding)
  (implies
   (and
    (q1346677-topological-space-p
     source-carrier source-topology)
    (q1346677-normal-space-p
     target-carrier target-topology)
    (q1346677-bounded-continuous-real-map-p
     source-carrier source-topology source-map)
    (q1346677-closed-embedding-p
     source-carrier source-topology
     target-carrier target-topology embedding))
   (q1346677-extension-exists-p
    source-carrier target-carrier target-topology
    embedding source-map)))

(value-triple :itpeval-statement-checked)
:q
