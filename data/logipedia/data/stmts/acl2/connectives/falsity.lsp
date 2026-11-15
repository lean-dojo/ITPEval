;; Statement-only formalization of Logipedia corpus artifact
;; connectives.falsity, catalog title "connectives.falsity": for every
;; proposition, the module's opaque False proposition implies that
;; proposition. This file contains no proof.

(in-package "ACL2")

;; ACL2's NIL is the target-native false proposition. Mapping the source
;; logical constant to NIL preserves its eliminator without adding an axiom.
(defun logipedia-connectives-falsity-holds-p (proposition)
  (not (equal proposition nil)))

(defun logipedia-connectives-falsity-false-proposition ()
  nil)

(defun-sk logipedia-connectives-falsity-statement ()
  (forall (proposition)
    (implies
     (logipedia-connectives-falsity-holds-p
      (logipedia-connectives-falsity-false-proposition))
     (logipedia-connectives-falsity-holds-p proposition))))

(value-triple :itpeval-statement-checked)
:q
