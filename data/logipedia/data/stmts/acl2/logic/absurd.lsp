;; Statement-only formalization of Logipedia corpus artifact logic.absurd,
;; catalog title "logic.absurd": for every proposition A, if A and the
;; module's abstract Not A hold, then its abstract False proposition holds.
;; This file contains no proof.

(in-package "ACL2")

;; ACL2 objects form the carrier of source propositions. These conservative
;; interfaces expose proposition truth and the source module's abstract False
;; and Not constants without imposing additional laws on them.
(defstub logipedia-logic-absurd-holds-p
  (proposition)
  t)

(defstub logipedia-logic-absurd-false-proposition
  ()
  t)

(defstub logipedia-logic-absurd-not-proposition
  (proposition)
  t)

(defun-sk logipedia-logic-absurd-statement ()
  (forall (a)
    (implies
     (logipedia-logic-absurd-holds-p a)
     (implies
      (logipedia-logic-absurd-holds-p
       (logipedia-logic-absurd-not-proposition a))
      (logipedia-logic-absurd-holds-p
       (logipedia-logic-absurd-false-proposition))))))

(value-triple :itpeval-statement-checked)
:q
