;; Statement-only formalization of Logipedia corpus artifact connectives.I,
;; catalog title "connectives.I": the distinguished nullary proposition
;; connectives.True holds. This file contains no proof.

(in-package "ACL2")

;; Conservative interface for the source module's proposition parameter
;; connectives.True.
(defstub logipedia-connectives-true-p () t)

(defun logipedia-connectives-i-statement ()
  (logipedia-connectives-true-p))

(value-triple :itpeval-statement-checked)
:q
