;; Statement-only formalization of thousand-theorems corpus artifact
;; thousand-theorems__acl2__Q1134776, "Dilworth's theorem": for every finite
;; partial order, the minimum cardinality of a partition into chains equals
;; the maximum cardinality of an antichain. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A duplicate-free true list enumerates an arbitrary finite carrier. The
;; conservative interface below supplies the arbitrary order relation itself;
;; it is not replaced by a finite lookup table. All partial-order laws are
;; explicit hypotheses of the final statement predicate.

(defstub q1134776-leq (x y) t)

(defun q1134776-carrier-p (carrier)
  (and (true-listp carrier)
       (no-duplicatesp-equal carrier)))

(defun q1134776-reflexive-p (remaining)
  (if (consp remaining)
      (and (q1134776-leq (car remaining) (car remaining))
           (q1134776-reflexive-p (cdr remaining)))
    (equal remaining nil)))

(defun q1134776-antisymmetric-from-p (x remaining)
  (if (consp remaining)
      (and
       (implies
        (and (q1134776-leq x (car remaining))
             (q1134776-leq (car remaining) x))
        (equal x (car remaining)))
       (q1134776-antisymmetric-from-p x (cdr remaining)))
    t))

(defun q1134776-antisymmetric-p (remaining carrier)
  (if (consp remaining)
      (and
       (q1134776-antisymmetric-from-p (car remaining) carrier)
       (q1134776-antisymmetric-p (cdr remaining) carrier))
    (equal remaining nil)))

(defun q1134776-transitive-from-p (x y remaining)
  (if (consp remaining)
      (and
       (implies
        (and (q1134776-leq x y)
             (q1134776-leq y (car remaining)))
        (q1134776-leq x (car remaining)))
       (q1134776-transitive-from-p x y (cdr remaining)))
    t))

(defun q1134776-transitive-from-x-p (x remaining carrier)
  (if (consp remaining)
      (and
       (q1134776-transitive-from-p
        x (car remaining) carrier)
       (q1134776-transitive-from-x-p
        x (cdr remaining) carrier))
    (equal remaining nil)))

(defun q1134776-transitive-p (remaining carrier)
  (if (consp remaining)
      (and
       (q1134776-transitive-from-x-p
        (car remaining) carrier carrier)
       (q1134776-transitive-p (cdr remaining) carrier))
    (equal remaining nil)))

(defun q1134776-partial-order-p (carrier)
  (and
   (q1134776-reflexive-p carrier)
   (q1134776-antisymmetric-p carrier carrier)
   (q1134776-transitive-p carrier carrier)))

;; The recursively generated power set contains every subset of the finite
;; carrier exactly once, in carrier order. Applying the same construction to
;; that power set contains every set of subsets exactly once, so minima and
;; maxima below range over the full objects quantified in the Lean statement.

(defun q1134776-prepend-to-each (value sets)
  (if (consp sets)
      (cons
       (cons value (car sets))
       (q1134776-prepend-to-each value (cdr sets)))
    nil))

(defun q1134776-power-set (set)
  (if (consp set)
      (let ((tail-power-set
             (q1134776-power-set (cdr set))))
        (append
         tail-power-set
         (q1134776-prepend-to-each
          (car set) tail-power-set)))
    (list nil)))

(defun q1134776-subset-p (left right)
  (if (consp left)
      (and (member-equal (car left) right)
           (q1134776-subset-p (cdr left) right))
    t))

(defun q1134776-set-equal-p (left right)
  (and (q1134776-subset-p left right)
       (q1134776-subset-p right left)))

(defun q1134776-set-union (left right)
  (if (consp left)
      (if (member-equal (car left) right)
          (q1134776-set-union (cdr left) right)
        (cons
         (car left)
         (q1134776-set-union (cdr left) right)))
    right))

(defun q1134776-family-union (family)
  (if (consp family)
      (q1134776-set-union
       (car family)
       (q1134776-family-union (cdr family)))
    nil))

(defun q1134776-disjoint-p (left right)
  (if (consp left)
      (and (not (member-equal (car left) right))
           (q1134776-disjoint-p (cdr left) right))
    t))

(defun q1134776-disjoint-from-family-p (set family)
  (if (consp family)
      (and (q1134776-disjoint-p set (car family))
           (q1134776-disjoint-from-family-p
            set (cdr family)))
    t))

(defun q1134776-pairwise-disjoint-family-p (family)
  (if (consp family)
      (and
       (q1134776-disjoint-from-family-p
        (car family) (cdr family))
       (q1134776-pairwise-disjoint-family-p
        (cdr family)))
    (equal family nil)))

(defun q1134776-comparable-with-all-p (x remaining)
  (if (consp remaining)
      (and
       (or (q1134776-leq x (car remaining))
           (q1134776-leq (car remaining) x))
       (q1134776-comparable-with-all-p
        x (cdr remaining)))
    t))

(defun q1134776-chain-p (set)
  (if (consp set)
      (and
       (q1134776-comparable-with-all-p
        (car set) (cdr set))
       (q1134776-chain-p (cdr set)))
    (equal set nil)))

(defun q1134776-incomparable-with-all-p (x remaining)
  (if (consp remaining)
      (and
       (not (q1134776-leq x (car remaining)))
       (not (q1134776-leq (car remaining) x))
       (q1134776-incomparable-with-all-p
        x (cdr remaining)))
    t))

(defun q1134776-antichain-p (set)
  (if (consp set)
      (and
       (q1134776-incomparable-with-all-p
        (car set) (cdr set))
       (q1134776-antichain-p (cdr set)))
    (equal set nil)))

(defun q1134776-all-chains-p (family)
  (if (consp family)
      (and (q1134776-chain-p (car family))
           (q1134776-all-chains-p (cdr family)))
    (equal family nil)))

;; Pairwise disjointness together with union equal to the carrier is exactly
;; the unique-membership partition condition. Empty chains remain permitted,
;; as they are in the source's Set (Set alpha) definition, but cannot lower
;; the minimum.

(defun q1134776-chain-partition-p (family carrier)
  (and
   (q1134776-all-chains-p family)
   (q1134776-pairwise-disjoint-family-p family)
   (q1134776-set-equal-p
    (q1134776-family-union family)
    carrier)))

(defun q1134776-min-chain-partition-aux
    (families carrier best)
  (declare (xargs :measure (len families)))
  (if (consp families)
      (let ((candidate (car families)))
        (q1134776-min-chain-partition-aux
         (cdr families)
         carrier
         (if (and
              (q1134776-chain-partition-p
               candidate carrier)
              (< (len candidate) best))
             (len candidate)
           best)))
    best))

(defun q1134776-min-chain-partition-cardinality (carrier)
  (let* ((subsets (q1134776-power-set carrier))
         (families (q1134776-power-set subsets)))
    (q1134776-min-chain-partition-aux
     families carrier (len carrier))))

(defun q1134776-max-antichain-aux (subsets best)
  (declare (xargs :measure (len subsets)))
  (if (consp subsets)
      (let ((candidate (car subsets)))
        (q1134776-max-antichain-aux
         (cdr subsets)
         (if (and
              (q1134776-antichain-p candidate)
              (< best (len candidate)))
             (len candidate)
           best)))
    best))

(defun q1134776-antichain-width (carrier)
  (q1134776-max-antichain-aux
   (q1134776-power-set carrier) 0))

(defun thousand-theorems-q1134776-dilworths-theorem-statement
    (carrier)
  (implies
   (and (q1134776-carrier-p carrier)
        (q1134776-partial-order-p carrier))
   (equal
    (q1134776-min-chain-partition-cardinality carrier)
    (q1134776-antichain-width carrier))))

(value-triple :itpeval-statement-checked)
:q
