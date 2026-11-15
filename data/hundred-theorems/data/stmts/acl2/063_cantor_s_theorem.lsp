;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__063, "Cantor's Theorem": no map from an arbitrary
;; carrier onto its full powerset is surjective, because its complemented
;; diagonal subset has no preimage. This file contains no proof.

(in-package "ACL2")

;; CARRIER is the characteristic predicate of an arbitrary domain A.
;; MAPPING represents a map f : A -> P(A) extensionally: MAPPING(SOURCE,
;; ELEMENT) says that ELEMENT belongs to f(SOURCE).

(defun ht063-carrier-member-p (carrier element)
  (if (apply$ carrier (list element))
      t
    nil))

(defun ht063-image-member-p (carrier mapping source element)
  (and
   (ht063-carrier-member-p carrier element)
   (if (apply$ mapping (list source element))
       t
     nil)))

;; The diagonal subset D of A is {x in A | x is not in f(x)}.

(defun ht063-diagonal-member-p (carrier mapping element)
  (and
   (ht063-carrier-member-p carrier element)
   (not
    (ht063-image-member-p
     carrier mapping element element))))

;; Extensional equality of f(SOURCE) and D quantifies over every element of
;; the carrier; the possible preimage SOURCE is also quantified internally.

(defun-sk ht063-image-row-equals-diagonal-p
    (carrier mapping source)
  (forall
   (element)
   (iff
    (ht063-image-member-p
     carrier mapping source element)
    (ht063-diagonal-member-p
     carrier mapping element))))

(defun-sk ht063-diagonal-preimage-exists-p
    (carrier mapping)
  (exists
   (source)
   (and
    (ht063-carrier-member-p carrier source)
    (ht063-image-row-equals-diagonal-p
     carrier mapping source))))

(defun hundred-theorems-063-cantor-s-theorem-statement
    (carrier mapping)
  (implies
   (and
    (tamep-functionp carrier)
    (tamep-functionp mapping))
   (not
    (ht063-diagonal-preimage-exists-p
     carrier mapping))))

(value-triple :itpeval-statement-checked)
:q
