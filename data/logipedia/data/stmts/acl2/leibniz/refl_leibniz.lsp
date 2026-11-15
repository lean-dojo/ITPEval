;; Statement-only formalization of Logipedia corpus artifact
;; leibniz.refl_leibniz, catalog title "leibniz.refl_leibniz": for every
;; type and element of that type, Leibniz equality relates the element to
;; itself. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify arbitrary source types, their carriers, and
;; proposition-valued predicates. Type and predicate tags remain universally
;; quantified in the definitions below.

(defstub logipedia-leibniz-refl-member-p
  (a-type value)
  t)

(defstub logipedia-leibniz-refl-predicate-holds-p
  (a-type predicate value)
  t)

(defun-sk logipedia-leibniz-refl-leibniz-p
    (a-type x y)
  (forall (predicate)
    (implies
     (logipedia-leibniz-refl-predicate-holds-p
      a-type predicate x)
     (logipedia-leibniz-refl-predicate-holds-p
      a-type predicate y))))

(defun-sk logipedia-leibniz-refl-statement ()
  (forall (a-type x)
    (implies
     (logipedia-leibniz-refl-member-p a-type x)
     (logipedia-leibniz-refl-leibniz-p a-type x x))))

(value-triple :itpeval-statement-checked)
:q
