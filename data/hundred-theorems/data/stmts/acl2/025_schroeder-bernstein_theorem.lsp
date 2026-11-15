;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__025, "Schroeder-Bernstein Theorem": injections in
;; both directions between two arbitrary carriers imply the existence of a
;; bijection between them. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Unary tame function objects represent arbitrary carriers. Tame function
;; objects also represent maps, and DEFUN-SK keeps every element and map
;; witness quantified inside the statement.

(defun ht025-member-p (carrier element)
  (if (apply$ carrier (list element)) t nil))

(defun ht025-map-value (map element)
  (apply$ map (list element)))

(defun-sk ht025-map-total-p (domain codomain map)
  (forall (element)
    (implies
     (ht025-member-p domain element)
     (ht025-member-p
      codomain
      (ht025-map-value map element)))))

(defun-sk ht025-map-injective-p (domain map)
  (forall (left right)
    (implies
     (and
      (ht025-member-p domain left)
      (ht025-member-p domain right)
      (equal
       (ht025-map-value map left)
       (ht025-map-value map right)))
     (equal left right))))

(defun ht025-injection-p (domain codomain map)
  (and
   (tamep-functionp domain)
   (tamep-functionp codomain)
   (tamep-functionp map)
   (ht025-map-total-p domain codomain map)
   (ht025-map-injective-p domain map)))

(defun-sk ht025-preimage-exists-p (target domain map)
  (exists (source)
    (and
     (ht025-member-p domain source)
     (equal (ht025-map-value map source) target))))

(defun-sk ht025-map-surjective-p (domain codomain map)
  (forall (target)
    (implies
     (ht025-member-p codomain target)
     (ht025-preimage-exists-p target domain map))))

(defun ht025-bijection-p (domain codomain map)
  (and
   (tamep-functionp domain)
   (tamep-functionp codomain)
   (tamep-functionp map)
   (ht025-map-total-p domain codomain map)
   (ht025-map-injective-p domain map)
   (ht025-map-surjective-p domain codomain map)))

(defun-sk ht025-bijection-exists-p (domain codomain)
  (exists (map)
    (ht025-bijection-p domain codomain map)))

(defun hundred-theorems-025-schroeder-bernstein-statement
    (domain codomain forward backward)
  (implies
   (and
    (ht025-injection-p domain codomain forward)
    (ht025-injection-p codomain domain backward))
   (ht025-bijection-exists-p domain codomain)))

(value-triple :itpeval-statement-checked)
:q
