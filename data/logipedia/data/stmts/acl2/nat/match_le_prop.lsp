;; Statement-only formalization of Logipedia corpus artifact
;; nat.match_le_prop, catalog title "nat.match_le_prop": a predicate holding
;; at a natural lower bound and at every successor holds at every natural
;; number above that bound. This file contains no proof.

(in-package "ACL2")

;; This conservative interface represents the source's arbitrary predicate
;; nat -> Prop. Its use in Boolean positions imposes no additional law.
(defstub logipedia-nat-match-le-prop-predicate (m) t)

(defun-sk logipedia-nat-match-le-prop-successor-premise-p ()
  (forall (m)
    (implies
     (natp m)
     (logipedia-nat-match-le-prop-predicate (+ 1 m)))))

(defun-sk logipedia-nat-match-le-prop-conclusion-p (n)
  (forall (m)
    (implies
     (and
      (natp m)
      (<= n m))
     (logipedia-nat-match-le-prop-predicate m))))

(defun-sk logipedia-nat-match-le-prop-statement ()
  (forall (n)
    (implies
     (natp n)
     (implies
      (logipedia-nat-match-le-prop-predicate n)
      (implies
       (logipedia-nat-match-le-prop-successor-premise-p)
       (logipedia-nat-match-le-prop-conclusion-p n))))))

(value-triple :itpeval-statement-checked)
:q
