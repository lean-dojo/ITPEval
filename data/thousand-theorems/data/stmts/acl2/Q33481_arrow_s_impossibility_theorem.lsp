;; Statement-only formalization of thousand-theorems corpus artifact Q33481
;; (thousand-theorems__acl2__Q33481), "Arrow's impossibility theorem": every
;; social welfare function on a finite electorate and at least three
;; alternatives that satisfies weak Pareto and independence of irrelevant
;; alternatives is dictatorial. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; STATES is an arbitrary, potentially infinite carrier.  INDIVIDUALS is a
;; duplicate-free enumeration of the source Fintype, and a profile is the
;; corresponding list of arbitrary APPLY$ preference relations.  The
;; conservative welfare interface represents an arbitrary function from such
;; profiles to preference relations; all typing and order laws are explicit.

(defstub q33481-state-member-p (states value) t)
(defstub q33481-welfare-order (welfare profile) t)

(defun q33481-relation-holds-p (relation left right)
  (if (apply$ relation (list left right))
      t
    nil))

(defun-sk q33481-preference-order-laws-p (states relation)
  (forall (x y z)
    (and
     (implies
      (q33481-state-member-p states x)
      (q33481-relation-holds-p relation x x))
     (implies
      (and
       (q33481-state-member-p states x)
       (q33481-state-member-p states y))
      (or
       (q33481-relation-holds-p relation x y)
       (q33481-relation-holds-p relation y x)))
     (implies
      (and
       (q33481-state-member-p states x)
       (q33481-state-member-p states y)
       (q33481-state-member-p states z)
       (q33481-relation-holds-p relation x y)
       (q33481-relation-holds-p relation y z))
      (q33481-relation-holds-p relation x z)))))

(defun q33481-preference-order-p (states relation)
  (and
   (tamep-functionp relation)
   (q33481-preference-order-laws-p states relation)))

(defun q33481-individual-type-p (individuals)
  (and
   (true-listp individuals)
   (no-duplicatesp-equal individuals)))

(defun q33481-alternatives-in-states-p (states alternatives)
  (if (consp alternatives)
      (and
       (q33481-state-member-p states (car alternatives))
       (q33481-alternatives-in-states-p
        states (cdr alternatives)))
    (equal alternatives nil)))

(defun q33481-alternative-set-p (states alternatives)
  (and
   (true-listp alternatives)
   (no-duplicatesp-equal alternatives)
   (q33481-alternatives-in-states-p states alternatives)))

(defun q33481-profile-p (states individuals profile)
  (if (consp individuals)
      (and
       (consp profile)
       (q33481-preference-order-p states (car profile))
       (q33481-profile-p
        states (cdr individuals) (cdr profile)))
    (equal profile nil)))

(defun q33481-strictly-prefers-p
    (relation preferred dispreferred)
  (and
   (q33481-relation-holds-p
    relation preferred dispreferred)
   (not
    (q33481-relation-holds-p
     relation dispreferred preferred))))

;; Agreement on both directions of the weak relation is equivalent, for total
;; preorders, to agreement on the strict and indifferent ordering of the pair.

(defun q33481-same-order-on-pair-p
    (left-relation right-relation x y)
  (and
   (iff
    (q33481-relation-holds-p left-relation x y)
    (q33481-relation-holds-p right-relation x y))
   (iff
    (q33481-relation-holds-p left-relation y x)
    (q33481-relation-holds-p right-relation y x))))

(defun q33481-all-individuals-strictly-prefer-p
    (profile x y)
  (if (consp profile)
      (and
       (q33481-strictly-prefers-p (car profile) x y)
       (q33481-all-individuals-strictly-prefer-p
        (cdr profile) x y))
    (equal profile nil)))

(defun q33481-profiles-same-order-on-pair-p
    (left-profile right-profile x y)
  (if (consp left-profile)
      (and
       (consp right-profile)
       (q33481-same-order-on-pair-p
        (car left-profile) (car right-profile) x y)
       (q33481-profiles-same-order-on-pair-p
        (cdr left-profile) (cdr right-profile) x y))
    (equal right-profile nil)))

(defun-sk q33481-social-welfare-function-p
    (states individuals welfare)
  (forall (profile)
    (implies
     (q33481-profile-p states individuals profile)
     (q33481-preference-order-p
      states
      (q33481-welfare-order welfare profile)))))

(defun-sk q33481-weak-pareto-p
    (states individuals alternatives welfare)
  (forall (x y profile)
    (implies
     (and
      (member-equal x alternatives)
      (member-equal y alternatives)
      (q33481-profile-p states individuals profile)
      (q33481-all-individuals-strictly-prefer-p
       profile x y))
     (q33481-strictly-prefers-p
      (q33481-welfare-order welfare profile)
      x y))))

(defun-sk q33481-independence-of-irrelevant-alternatives-p
    (states individuals alternatives welfare)
  (forall (left-profile right-profile x y)
    (implies
     (and
      (member-equal x alternatives)
      (member-equal y alternatives)
      (q33481-profile-p
       states individuals left-profile)
      (q33481-profile-p
       states individuals right-profile)
      (q33481-profiles-same-order-on-pair-p
       left-profile right-profile x y))
     (q33481-same-order-on-pair-p
      (q33481-welfare-order welfare left-profile)
      (q33481-welfare-order welfare right-profile)
      x y))))

(defun-sk q33481-dictator-at-p
    (states individuals alternatives welfare dictator-index)
  (forall (x y profile)
    (implies
     (and
      (member-equal x alternatives)
      (member-equal y alternatives)
      (q33481-profile-p states individuals profile)
      (q33481-strictly-prefers-p
       (nth dictator-index profile) x y))
     (q33481-strictly-prefers-p
      (q33481-welfare-order welfare profile)
      x y))))

(defun-sk q33481-dictatorship-p
    (states individuals alternatives welfare)
  (exists (dictator-index)
    (and
     (natp dictator-index)
     (< dictator-index (len individuals))
     (q33481-dictator-at-p
      states individuals alternatives welfare dictator-index))))

(defun thousand-theorems-q33481-arrows-impossibility-theorem-statement
    (states individuals alternatives welfare)
  (implies
   (and
    (q33481-individual-type-p individuals)
    (q33481-alternative-set-p states alternatives)
    (<= 3 (len alternatives))
    (q33481-social-welfare-function-p
     states individuals welfare)
    (q33481-weak-pareto-p
     states individuals alternatives welfare)
    (q33481-independence-of-irrelevant-alternatives-p
     states individuals alternatives welfare))
   (q33481-dictatorship-p
    states individuals alternatives welfare)))

(value-triple :itpeval-statement-checked)
:q
