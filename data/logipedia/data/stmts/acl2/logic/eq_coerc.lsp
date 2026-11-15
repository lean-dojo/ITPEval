;; Statement-only formalization of Logipedia corpus artifact logic.eq_coerc,
;; catalog title "logic.eq_coerc": equality between propositions transports
;; truth from the first proposition to the second. This file contains no proof.

(in-package "ACL2")

;; ACL2 objects form the unrestricted carrier of source propositions. These
;; conservative interfaces expose proposition truth and the logic module's
;; abstract equality specialized to propositions, without adding equality laws.
(defstub logipedia-logic-eq-coerc-holds-p
  (proposition)
  t)

(defstub logipedia-logic-eq-coerc-source-equal-p
  (left-proposition right-proposition)
  t)

(defun logipedia-logic-eq-coerc-statement (a b)
  (implies
   (logipedia-logic-eq-coerc-holds-p a)
   (implies
    (logipedia-logic-eq-coerc-source-equal-p a b)
    (logipedia-logic-eq-coerc-holds-p b))))

(value-triple :itpeval-statement-checked)
:q
