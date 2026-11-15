;; Statement-only formalization of thousand-theorems corpus artifact Q869647
;; (thousand-theorems__acl2__Q869647), "Szpilrajn extension theorem": every
;; partial order on an arbitrary carrier extends to a linear order. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ function objects represent the arbitrary carrier and binary
;; relations extensionally, without finite enumerations or lookup tables.
;; DEFUN-SK keeps the extending linear order existentially quantified.

(defun q869647-member-p (carrier element)
  (if (apply$ carrier (list element))
      t
    nil))

(defun q869647-related-p (carrier relation left right)
  (and
   (q869647-member-p carrier left)
   (q869647-member-p carrier right)
   (if (apply$ relation (list left right))
       t
     nil)))

(defun-sk q869647-partial-order-laws-p (carrier relation)
  (forall (x y z)
    (and
     (implies
      (q869647-member-p carrier x)
      (q869647-related-p carrier relation x x))
     (implies
      (and
       (q869647-related-p carrier relation x y)
       (q869647-related-p carrier relation y x))
      (equal x y))
     (implies
      (and
       (q869647-related-p carrier relation x y)
       (q869647-related-p carrier relation y z))
      (q869647-related-p carrier relation x z)))))

(defun q869647-partial-order-p (carrier relation)
  (and
   (tamep-functionp carrier)
   (tamep-functionp relation)
   (q869647-partial-order-laws-p carrier relation)))

(defun-sk q869647-total-p (carrier relation)
  (forall (x y)
    (implies
     (and
      (q869647-member-p carrier x)
      (q869647-member-p carrier y))
     (or
      (q869647-related-p carrier relation x y)
      (q869647-related-p carrier relation y x)))))

(defun q869647-linear-order-p (carrier relation)
  (and
   (q869647-partial-order-p carrier relation)
   (q869647-total-p carrier relation)))

(defun-sk q869647-relation-extends-p
    (carrier original extension)
  (forall (x y)
    (implies
     (q869647-related-p carrier original x y)
     (q869647-related-p carrier extension x y))))

(defun q869647-linear-extension-p
    (carrier original extension)
  (and
   (q869647-linear-order-p carrier extension)
   (q869647-relation-extends-p
    carrier original extension)))

(defun-sk q869647-linear-extension-exists-p
    (carrier original)
  (exists (extension)
    (q869647-linear-extension-p
     carrier original extension)))

(defun thousand-theorems-q869647-szpilrajn-extension-theorem-statement
    (carrier relation)
  (implies
   (q869647-partial-order-p carrier relation)
   (q869647-linear-extension-exists-p carrier relation)))

(value-triple :itpeval-statement-checked)
:q
