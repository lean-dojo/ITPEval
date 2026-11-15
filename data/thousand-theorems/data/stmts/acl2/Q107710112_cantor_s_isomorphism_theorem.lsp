;; Statement-only formalization of Thousand Theorems corpus artifact Q107710112
;; (thousand-theorems__acl2__Q107710112), "Cantor's isomorphism theorem": any
;; two countable, dense, nonempty linear orders without endpoints are order
;; isomorphic. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ function objects represent arbitrary carriers, strict order
;; relations, countability codes, and the maps of an order isomorphism.
;; DEFUN-SK keeps the countability and isomorphism witnesses internal.

(defun q107710112-member-p (carrier element)
  (if (apply$ carrier (list element))
      t
    nil))

(defun q107710112-less-p (less left right)
  (if (apply$ less (list left right))
      t
    nil))

(defun q107710112-unary-value (function argument)
  (apply$ function (list argument)))

;; Irreflexivity, transitivity, and trichotomy give the strict-order
;; presentation equivalent to a linear order.

(defun-sk q107710112-strict-linear-order-laws-p (carrier less)
  (forall (x y z)
    (and
     (implies
      (q107710112-member-p carrier x)
      (not (q107710112-less-p less x x)))
     (implies
      (and
       (q107710112-member-p carrier x)
       (q107710112-member-p carrier y))
      (or
       (q107710112-less-p less x y)
       (equal x y)
       (q107710112-less-p less y x)))
     (implies
      (and
       (q107710112-member-p carrier x)
       (q107710112-member-p carrier y)
       (q107710112-member-p carrier z)
       (q107710112-less-p less x y)
       (q107710112-less-p less y z))
      (q107710112-less-p less x z)))))

(defun q107710112-linear-order-p (carrier less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp less)
   (q107710112-strict-linear-order-laws-p carrier less)))

;; Density and the absence of endpoints retain their existential witnesses
;; under the universal quantifiers over carrier elements.

(defun-sk q107710112-between-exists-p
    (carrier less left right)
  (exists (middle)
    (and
     (q107710112-member-p carrier middle)
     (q107710112-less-p less left middle)
     (q107710112-less-p less middle right))))

(defun-sk q107710112-densely-ordered-p (carrier less)
  (forall (left right)
    (implies
     (and
      (q107710112-member-p carrier left)
      (q107710112-member-p carrier right)
      (q107710112-less-p less left right))
     (q107710112-between-exists-p
      carrier less left right))))

(defun-sk q107710112-smaller-exists-p
    (carrier less element)
  (exists (smaller)
    (and
     (q107710112-member-p carrier smaller)
     (q107710112-less-p less smaller element))))

(defun-sk q107710112-no-min-order-p (carrier less)
  (forall (element)
    (implies
     (q107710112-member-p carrier element)
     (q107710112-smaller-exists-p
      carrier less element))))

(defun-sk q107710112-larger-exists-p
    (carrier less element)
  (exists (larger)
    (and
     (q107710112-member-p carrier larger)
     (q107710112-less-p less element larger))))

(defun-sk q107710112-no-max-order-p (carrier less)
  (forall (element)
    (implies
     (q107710112-member-p carrier element)
     (q107710112-larger-exists-p
      carrier less element))))

(defun-sk q107710112-nonempty-p (carrier)
  (exists (element)
    (q107710112-member-p carrier element)))

;; A countability code is an injective map from the carrier into the natural
;; numbers. Its existence is quantified inside Q107710112-COUNTABLE-P.

(defun-sk q107710112-countability-code-laws-p
    (carrier code)
  (forall (x y)
    (and
     (implies
      (q107710112-member-p carrier x)
      (natp (q107710112-unary-value code x)))
     (implies
      (and
       (q107710112-member-p carrier x)
       (q107710112-member-p carrier y)
       (equal
        (q107710112-unary-value code x)
        (q107710112-unary-value code y)))
      (equal x y)))))

(defun q107710112-countability-code-p (carrier code)
  (and
   (tamep-functionp code)
   (q107710112-countability-code-laws-p carrier code)))

(defun-sk q107710112-countable-p (carrier)
  (exists (code)
    (q107710112-countability-code-p carrier code)))

;; The two tame maps, their inverse equations, and strict-order equivalence
;; are exactly an order isomorphism between the two arbitrary carriers.

(defun-sk q107710112-order-isomorphism-laws-p
    (alpha alpha-less beta beta-less forward inverse)
  (forall (x y)
    (and
     (implies
      (q107710112-member-p alpha x)
      (and
       (q107710112-member-p
        beta
        (q107710112-unary-value forward x))
       (equal
        (q107710112-unary-value
         inverse
         (q107710112-unary-value forward x))
        x)))
     (implies
      (q107710112-member-p beta y)
      (and
       (q107710112-member-p
        alpha
        (q107710112-unary-value inverse y))
       (equal
        (q107710112-unary-value
         forward
         (q107710112-unary-value inverse y))
        y)))
     (implies
      (and
       (q107710112-member-p alpha x)
       (q107710112-member-p alpha y))
      (iff
       (q107710112-less-p alpha-less x y)
       (q107710112-less-p
        beta-less
        (q107710112-unary-value forward x)
        (q107710112-unary-value forward y)))))))

(defun q107710112-order-isomorphism-p
    (alpha alpha-less beta beta-less forward inverse)
  (and
   (tamep-functionp forward)
   (tamep-functionp inverse)
   (q107710112-order-isomorphism-laws-p
    alpha alpha-less beta beta-less forward inverse)))

(defun-sk q107710112-order-isomorphism-exists-p
    (alpha alpha-less beta beta-less)
  (exists (forward inverse)
    (q107710112-order-isomorphism-p
     alpha alpha-less beta beta-less forward inverse)))

(defun thousand-theorems-q107710112-cantor-isomorphism-statement
    (alpha alpha-less beta beta-less)
  (implies
   (and
    (q107710112-linear-order-p alpha alpha-less)
    (q107710112-countable-p alpha)
    (q107710112-densely-ordered-p alpha alpha-less)
    (q107710112-no-min-order-p alpha alpha-less)
    (q107710112-no-max-order-p alpha alpha-less)
    (q107710112-nonempty-p alpha)
    (q107710112-linear-order-p beta beta-less)
    (q107710112-countable-p beta)
    (q107710112-densely-ordered-p beta beta-less)
    (q107710112-no-min-order-p beta beta-less)
    (q107710112-no-max-order-p beta beta-less)
    (q107710112-nonempty-p beta))
   (q107710112-order-isomorphism-exists-p
    alpha alpha-less beta beta-less)))

(value-triple :itpeval-statement-checked)
:q
