;; Statement-only formalization of Logipedia corpus artifact
;; connectives.equal_leibniz, catalog title "connectives.equal_leibniz":
;; for every type, elements x and y, and predicate P, the module's abstract
;; equality of x and y transports P x to P y. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify arbitrary source types, their carriers, the
;; module's abstract equality, and proposition-valued predicates. Type and
;; predicate tags remain universally quantified in the statement below.

(defstub logipedia-connectives-equal-leibniz-member-p
  (a-type value)
  t)

(defstub logipedia-connectives-equal-leibniz-source-equal-p
  (a-type left right)
  t)

(defstub logipedia-connectives-equal-leibniz-predicate-holds-p
  (a-type predicate value)
  t)

(defun-sk logipedia-connectives-equal-leibniz-statement ()
  (forall (a-type x y predicate)
    (implies
     (and
      (logipedia-connectives-equal-leibniz-member-p a-type x)
      (logipedia-connectives-equal-leibniz-member-p a-type y)
      (logipedia-connectives-equal-leibniz-source-equal-p
       a-type x y))
     (implies
      (logipedia-connectives-equal-leibniz-predicate-holds-p
       a-type predicate x)
      (logipedia-connectives-equal-leibniz-predicate-holds-p
       a-type predicate y)))))

(value-triple :itpeval-statement-checked)
:q
