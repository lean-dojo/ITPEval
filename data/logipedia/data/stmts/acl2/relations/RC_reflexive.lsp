;; Statement-only formalization of Logipedia corpus artifact
;; relations.RC_reflexive, catalog title "relations.RC_reflexive": adjoining
;; equality to an arbitrary binary relation makes it reflexive on its
;; arbitrary carrier. This file contains no proof.

(in-package "ACL2")

;; These unconstrained interfaces represent an arbitrary carrier and relation.
(defstub logipedia-relations-rc-reflexive-member-p (element) t)
(defstub logipedia-relations-rc-reflexive-relation-p (left right) t)

(defun logipedia-relations-rc-reflexive-rc-p (left right)
  (or
   (logipedia-relations-rc-reflexive-relation-p left right)
   (equal left right)))

(defun-sk logipedia-relations-rc-reflexive-statement ()
  (forall (element)
    (implies
     (logipedia-relations-rc-reflexive-member-p element)
     (logipedia-relations-rc-reflexive-rc-p element element))))

(value-triple :itpeval-statement-checked)
:q
