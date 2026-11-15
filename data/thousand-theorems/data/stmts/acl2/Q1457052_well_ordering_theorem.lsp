;; Statement-only formalization of Thousand Theorems artifact Q1457052
;; (thousand-theorems__acl2__Q1457052), "Well-ordering theorem": every
;; arbitrary carrier admits a strict linear order under which every nonempty
;; subset has a least element.  This file contains no proof.

(in-package "ACL2")

;; Tame APPLY$ function objects represent arbitrary carriers, binary
;; relations, and subsets.  The least-element formulation below is the
;; standard predicate form of well-foundedness for a strict linear order.

(defun q1457052-member-p (predicate element)
  (if (apply$ predicate (list element)) t nil))

(defun q1457052-less-p (less left right)
  (if (apply$ less (list left right)) t nil))

(defun-sk q1457052-strict-linear-order-laws-p (carrier less)
  (forall (x y z)
    (and
      (implies
        (q1457052-member-p carrier x)
        (not (q1457052-less-p less x x)))
      (implies
        (and (q1457052-member-p carrier x)
             (q1457052-member-p carrier y))
        (or (q1457052-less-p less x y)
            (equal x y)
            (q1457052-less-p less y x)))
      (implies
        (and (q1457052-member-p carrier x)
             (q1457052-member-p carrier y)
             (q1457052-member-p carrier z)
             (q1457052-less-p less x y)
             (q1457052-less-p less y z))
        (q1457052-less-p less x z)))))

(defun q1457052-strict-linear-order-p (carrier less)
  (and (tamep-functionp carrier)
       (tamep-functionp less)
       (q1457052-strict-linear-order-laws-p carrier less)))

(defun-sk q1457052-subset-of-carrier-p (carrier subset)
  (forall (x)
    (implies
      (q1457052-member-p subset x)
      (q1457052-member-p carrier x))))

(defun-sk q1457052-subset-nonempty-p (carrier subset)
  (exists (x)
    (and (q1457052-member-p carrier x)
         (q1457052-member-p subset x))))

(defun-sk q1457052-least-below-all-p (carrier less subset least)
  (forall (other)
    (implies
      (and (q1457052-member-p carrier other)
           (q1457052-member-p subset other))
      (or (equal least other)
          (q1457052-less-p less least other)))))

(defun q1457052-least-element-p (carrier less subset least)
  (and (q1457052-member-p carrier least)
       (q1457052-member-p subset least)
       (q1457052-least-below-all-p carrier less subset least)))

(defun-sk q1457052-least-element-exists-p (carrier less subset)
  (exists (least)
    (q1457052-least-element-p carrier less subset least)))

(defun-sk q1457052-well-founded-p (carrier less)
  (forall (subset)
    (implies
      (and (tamep-functionp subset)
           (q1457052-subset-of-carrier-p carrier subset)
           (q1457052-subset-nonempty-p carrier subset))
      (q1457052-least-element-exists-p carrier less subset))))

(defun q1457052-well-order-p (carrier less)
  (and (q1457052-strict-linear-order-p carrier less)
       (q1457052-well-founded-p carrier less)))

(defun-sk q1457052-well-order-exists-p (carrier)
  (exists (less)
    (q1457052-well-order-p carrier less)))

(defun thousand-theorems-q1457052-well-ordering-theorem-statement
    (carrier)
  (implies
    (tamep-functionp carrier)
    (q1457052-well-order-exists-p carrier)))

(value-triple :itpeval-statement-checked)
:q
