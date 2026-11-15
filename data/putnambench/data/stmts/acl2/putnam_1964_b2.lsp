;; Statement-only formalization of PutnamBench artifact putnam_1964_b2:
;; a maximal pairwise-intersecting family of subsets of a nonempty finite set
;; contains exactly half of all its subsets. This file contains no proof.

(in-package "ACL2")

;; An arbitrary nonempty finite set is represented by a duplicate-free true
;; list.  The powerset below contains each extensional subset exactly once,
;; in the order induced by the carrier.  Choosing an enumeration of any
;; source finite set gives this representation, and forgetting list order
;; recovers the source set and family, so this is a bidirectional encoding
;; rather than a restriction on the carrier or its subsets.

(defun putnam-1964-b2-adjoin-to-each (element sets)
  (if (consp sets)
      (cons (cons element (car sets))
            (putnam-1964-b2-adjoin-to-each
             element (cdr sets)))
    nil))

(defun putnam-1964-b2-powerset (carrier)
  (if (consp carrier)
      (let ((tail-powerset
             (putnam-1964-b2-powerset (cdr carrier))))
        (append
         tail-powerset
         (putnam-1964-b2-adjoin-to-each
          (car carrier) tail-powerset)))
    (list nil)))

(defun putnam-1964-b2-family-from-powerset-p
    (family powerset)
  (if (consp family)
      (and (member-equal (car family) powerset)
           (putnam-1964-b2-family-from-powerset-p
            (cdr family) powerset))
    (equal family nil)))

(defun putnam-1964-b2-intersect-p (left right)
  (if (consp left)
      (or (member-equal (car left) right)
          (putnam-1964-b2-intersect-p
           (cdr left) right))
    nil))

(defun putnam-1964-b2-intersects-every-p
    (subset family)
  (if (consp family)
      (and
       (putnam-1964-b2-intersect-p subset (car family))
       (putnam-1964-b2-intersects-every-p
        subset (cdr family)))
    t))

(defun putnam-1964-b2-pairwise-intersecting-p
    (remaining family)
  (if (consp remaining)
      (and
       (putnam-1964-b2-intersects-every-p
        (car remaining) family)
       (putnam-1964-b2-pairwise-intersecting-p
        (cdr remaining) family))
    t))

;; This ranges over the complete powerset.  It is exactly the negation of an
;; internal witness outside the family that intersects every family member.
(defun putnam-1964-b2-maximal-p
    (remaining-subsets family)
  (if (consp remaining-subsets)
      (and
       (or
        (member-equal (car remaining-subsets) family)
        (not
         (putnam-1964-b2-intersects-every-p
          (car remaining-subsets) family)))
       (putnam-1964-b2-maximal-p
        (cdr remaining-subsets) family))
    t))

(defun putnambench-putnam-1964-b2-statement
    (carrier family)
  (let ((powerset
         (putnam-1964-b2-powerset carrier)))
    (implies
     (and
      (true-listp carrier)
      (consp carrier)
      (no-duplicatesp-equal carrier)
      (true-listp family)
      (no-duplicatesp-equal family)
      (putnam-1964-b2-family-from-powerset-p
       family powerset)
      (putnam-1964-b2-pairwise-intersecting-p
       family family)
      (putnam-1964-b2-maximal-p
       powerset family))
     (equal
      (len family)
      (expt 2 (- (len carrier) 1))))))

(value-triple :itpeval-statement-checked)
:q
