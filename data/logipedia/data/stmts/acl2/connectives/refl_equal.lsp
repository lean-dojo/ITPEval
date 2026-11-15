;; Statement-only formalization of Logipedia corpus artifact
;; connectives.refl_equal, catalog title "connectives.refl_equal":
;; for every type and every element of that type, the module's abstract
;; equality relates the element to itself. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify arbitrary source types, their carriers, and
;; the module's abstract equality. The type tag and element remain universally
;; quantified in the statement below.
(defstub logipedia-connectives-refl-equal-member-p
  (a-type value)
  t)

(defstub logipedia-connectives-refl-equal-source-equal-p
  (a-type left right)
  t)

(defun-sk logipedia-connectives-refl-equal-statement ()
  (forall (a-type x)
    (implies
     (logipedia-connectives-refl-equal-member-p a-type x)
     (logipedia-connectives-refl-equal-source-equal-p
      a-type x x))))

(value-triple :itpeval-statement-checked)
:q
