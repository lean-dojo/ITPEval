;; Statement-only formalization of thousand-theorems corpus artifact Q536640,
;; "Hall's marriage theorem": an indexed family of finite sets has an
;; injective choice of representatives exactly when every finite subfamily's
;; union has cardinality at least its number of indices. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Unary tame function objects are characteristic predicates for the arbitrary
;; index and element carriers. FAMILY maps each index to a duplicate-free true
;; list representing its finite set. MATCHING maps indices to representatives.

(defun q536640-member-p (carrier object)
  (if (apply$ carrier (list object)) t nil))

(defun q536640-family-set (family index)
  (apply$ family (list index)))

(defun q536640-matching-value (matching index)
  (apply$ matching (list index)))

(defun q536640-elements-in-carrier-p (elements carrier)
  (if (consp elements)
      (and
       (q536640-member-p carrier (car elements))
       (q536640-elements-in-carrier-p (cdr elements) carrier))
    (equal elements nil)))

(defun q536640-finite-set-over-p (elements carrier)
  (and
   (true-listp elements)
   (no-duplicatesp-equal elements)
   (q536640-elements-in-carrier-p elements carrier)))

(defun-sk q536640-family-well-formed-p
    (index-carrier element-carrier family)
  (forall (index)
    (implies
     (q536640-member-p index-carrier index)
     (q536640-finite-set-over-p
      (q536640-family-set family index)
      element-carrier))))

;; Every finite subset of the arbitrary index carrier is represented
;; extensionally by a duplicate-free true list.

(defun q536640-finite-index-subset-p (indices index-carrier)
  (q536640-finite-set-over-p indices index-carrier))

(defun q536640-family-union (indices family)
  (if (consp indices)
      (union-equal
       (q536640-family-set family (car indices))
       (q536640-family-union (cdr indices) family))
    nil))

(defun-sk q536640-hall-condition-p (index-carrier family)
  (forall (indices)
    (implies
     (q536640-finite-index-subset-p indices index-carrier)
     (<=
      (len indices)
      (len (q536640-family-union indices family))))))

;; The representative function is existentially quantified inside the
;; statement. Its values lie in the corresponding finite sets and it is
;; injective on the entire, potentially infinite, index carrier.

(defun-sk q536640-matching-selects-p
    (index-carrier element-carrier family matching)
  (forall (index)
    (implies
     (q536640-member-p index-carrier index)
     (and
      (q536640-member-p
       element-carrier
       (q536640-matching-value matching index))
      (member-equal
       (q536640-matching-value matching index)
       (q536640-family-set family index))))))

(defun-sk q536640-matching-injective-p
    (index-carrier matching)
  (forall (left-index right-index)
    (implies
     (and
      (q536640-member-p index-carrier left-index)
      (q536640-member-p index-carrier right-index)
      (equal
       (q536640-matching-value matching left-index)
       (q536640-matching-value matching right-index)))
     (equal left-index right-index))))

(defun q536640-matching-p
    (index-carrier element-carrier family matching)
  (and
   (tamep-functionp matching)
   (q536640-matching-selects-p
    index-carrier element-carrier family matching)
   (q536640-matching-injective-p
    index-carrier matching)))

(defun-sk q536640-matching-exists-p
    (index-carrier element-carrier family)
  (exists (matching)
    (q536640-matching-p
     index-carrier element-carrier family matching)))

(defun thousand-theorems-q536640-hall-s-marriage-theorem-statement
    (index-carrier element-carrier family)
  (implies
   (and
    (tamep-functionp index-carrier)
    (tamep-functionp element-carrier)
    (tamep-functionp family)
    (q536640-family-well-formed-p
     index-carrier element-carrier family))
   (iff
    (q536640-hall-condition-p index-carrier family)
    (q536640-matching-exists-p
     index-carrier element-carrier family))))

(value-triple :itpeval-statement-checked)
:q
