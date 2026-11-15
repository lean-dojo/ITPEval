;; Statement-only formalization of thousand-theorems corpus artifact Q474881,
;; "Cantor's theorem": for every function from an arbitrary carrier to its
;; full powerset, the complemented diagonal subset has no preimage, so the
;; function is not surjective. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent an arbitrary type by its carrier
;; predicate and an arbitrary function into its powerset by the binary
;; membership relation SOURCE |-> {ELEMENT | Q474881-IMAGE-MEMBERSHIP holds}.

(defstub q474881-carrier-p (element) t)

(defstub q474881-image-membership (source element) t)

(defun q474881-member-p (element)
  (if (q474881-carrier-p element)
      t
    nil))

(defun q474881-image-member-p (source element)
  (if (q474881-image-membership source element)
      t
    nil))

;; This is the subset {ELEMENT in alpha | ELEMENT is not in f(ELEMENT)}.

(defun q474881-diagonal-member-p (element)
  (and
   (q474881-member-p element)
   (not (q474881-image-member-p element element))))

;; A source maps to the diagonal exactly when its image row and the diagonal
;; have the same membership truth value at every element of the carrier.

(defun-sk q474881-row-equals-diagonal-p (source)
  (forall (element)
    (implies
     (q474881-member-p element)
     (equal
      (q474881-image-member-p source element)
      (q474881-diagonal-member-p element)))))

;; Every source in the carrier fails that equality (at ELEMENT = SOURCE);
;; hence the diagonal subset has no preimage and the map is not surjective.

(defun-sk thousand-theorems-q474881-cantor-surjective-statement ()
  (forall (source)
    (implies
     (q474881-member-p source)
     (not (q474881-row-equals-diagonal-p source)))))

(value-triple :itpeval-statement-checked)
:q
