;; Statement-only formalization of Logipedia corpus artifact
;; nat.match_nat_prop, catalog title "nat.match_nat_prop": a predicate on
;; natural numbers that holds at zero and every successor holds at every
;; natural number. This file contains no proof.

(in-package "ACL2")

;; This conservative interface represents the source's arbitrary predicate
;; nat -> Prop. Its use in Boolean positions imposes no additional law.
(defstub logipedia-nat-match-prop-return-p (natural-value) t)

(defun-sk logipedia-nat-match-prop-successors-p ()
  (forall (n)
    (implies
     (natp n)
     (logipedia-nat-match-prop-return-p (+ 1 n)))))

(defun-sk logipedia-nat-match-prop-all-p ()
  (forall (z)
    (implies
     (natp z)
     (logipedia-nat-match-prop-return-p z))))

(defun logipedia-nat-match-prop-statement ()
  (implies
   (logipedia-nat-match-prop-return-p 0)
   (implies
    (logipedia-nat-match-prop-successors-p)
    (logipedia-nat-match-prop-all-p))))

(value-triple :itpeval-statement-checked)
:q
