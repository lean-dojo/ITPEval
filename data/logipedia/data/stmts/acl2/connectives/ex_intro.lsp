;; Statement-only formalization of Logipedia corpus artifact
;; connectives.ex_intro, catalog title "connectives.ex_intro": for every type,
;; predicate, and element satisfying that predicate, the module's abstract
;; existential proposition for the type and predicate holds. This file
;; contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify arbitrary source types, their carriers,
;; proposition-valued predicates, and the truth of the module's abstract
;; existential proposition. Type and predicate tags remain universally
;; quantified in the statement below.

(defstub logipedia-connectives-ex-intro-member-p
  (a-type value)
  t)

(defstub logipedia-connectives-ex-intro-predicate-holds-p
  (a-type predicate value)
  t)

(defstub logipedia-connectives-ex-intro-ex-holds-p
  (a-type predicate)
  t)

(defun-sk logipedia-connectives-ex-intro-statement ()
  (forall (a-type predicate x)
    (implies
     (and
      (logipedia-connectives-ex-intro-member-p a-type x)
      (logipedia-connectives-ex-intro-predicate-holds-p
       a-type predicate x))
     (logipedia-connectives-ex-intro-ex-holds-p
      a-type predicate))))

(value-triple :itpeval-statement-checked)
:q
