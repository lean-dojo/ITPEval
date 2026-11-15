;; Statement-only formalization of thousand-theorems corpus artifact Q1033910,
;; "Cantor–Bernstein–Schroeder theorem": injections in both directions between
;; two arbitrary carriers imply the existence of a bijection between them.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Unary tame function objects represent arbitrary carriers.  Tame function
;; objects also represent maps, and DEFUN-SK keeps every element and map
;; witness quantified inside the statement.

(defun q1033910-member-p (carrier element)
  (if (apply$ carrier (list element)) t nil))

(defun q1033910-map-value (map element)
  (apply$ map (list element)))

(defun-sk q1033910-map-total-p (domain codomain map)
  (forall (element)
    (implies
     (q1033910-member-p domain element)
     (q1033910-member-p
      codomain
      (q1033910-map-value map element)))))

(defun-sk q1033910-map-injective-p (domain map)
  (forall (left right)
    (implies
     (and
      (q1033910-member-p domain left)
      (q1033910-member-p domain right)
      (equal
       (q1033910-map-value map left)
       (q1033910-map-value map right)))
     (equal left right))))

(defun q1033910-injection-p (domain codomain map)
  (and
   (tamep-functionp domain)
   (tamep-functionp codomain)
   (tamep-functionp map)
   (q1033910-map-total-p domain codomain map)
   (q1033910-map-injective-p domain map)))

(defun-sk q1033910-preimage-exists-p (target domain map)
  (exists (source)
    (and
     (q1033910-member-p domain source)
     (equal (q1033910-map-value map source) target))))

(defun-sk q1033910-map-surjective-p (domain codomain map)
  (forall (target)
    (implies
     (q1033910-member-p codomain target)
     (q1033910-preimage-exists-p target domain map))))

(defun q1033910-bijection-p (domain codomain map)
  (and
   (tamep-functionp domain)
   (tamep-functionp codomain)
   (tamep-functionp map)
   (q1033910-map-total-p domain codomain map)
   (q1033910-map-injective-p domain map)
   (q1033910-map-surjective-p domain codomain map)))

(defun-sk q1033910-bijection-exists-p (domain codomain)
  (exists (map)
    (q1033910-bijection-p domain codomain map)))

(defun thousand-theorems-q1033910-cantor-bernstein-schroeder-statement
    (domain codomain forward backward)
  (implies
   (and
    (q1033910-injection-p domain codomain forward)
    (q1033910-injection-p codomain domain backward))
   (q1033910-bijection-exists-p domain codomain)))

(value-triple :itpeval-statement-checked)
:q
