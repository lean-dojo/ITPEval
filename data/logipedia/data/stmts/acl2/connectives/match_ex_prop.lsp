;; Statement-only formalization of Logipedia corpus artifact
;; connectives.match_ex_prop, catalog title "connectives.match_ex_prop":
;; elimination for the module's abstract existential connective, stating that
;; a continuation from every element satisfying P to an arbitrary return
;; proposition, together with ex A P, entails that proposition. This file
;; contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify arbitrary source types, their carriers,
;; proposition-valued predicates, proposition truth, and the truth of the
;; module's abstract existential proposition. Type and predicate tags remain
;; universally quantified in the statement below.
(defstub logipedia-connectives-match-ex-prop-member-p
  (a-type value)
  t)

(defstub logipedia-connectives-match-ex-prop-predicate-holds-p
  (a-type predicate value)
  t)

(defstub logipedia-connectives-match-ex-prop-proposition-holds-p
  (proposition)
  t)

(defstub logipedia-connectives-match-ex-prop-ex-holds-p
  (a-type predicate)
  t)

(defun-sk logipedia-connectives-match-ex-prop-continuation-p
  (a-type predicate return-proposition)
  (forall (x)
    (implies
     (logipedia-connectives-match-ex-prop-member-p a-type x)
     (implies
      (logipedia-connectives-match-ex-prop-predicate-holds-p
       a-type predicate x)
      (logipedia-connectives-match-ex-prop-proposition-holds-p
       return-proposition)))))

(defun-sk logipedia-connectives-match-ex-prop-statement ()
  (forall (a-type predicate return-proposition)
    (implies
     (logipedia-connectives-match-ex-prop-continuation-p
      a-type predicate return-proposition)
     (implies
      (logipedia-connectives-match-ex-prop-ex-holds-p
       a-type predicate)
      (logipedia-connectives-match-ex-prop-proposition-holds-p
       return-proposition)))))

(value-triple :itpeval-statement-checked)
:q
