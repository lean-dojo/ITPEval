;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sf_HoareLogic_reduce_to_zeroqtvc: the reduce-to-zero loop verification
;; condition over unbounded mathematical integers, preserving nonnegativity
;; while decrementing by one until the zero exit case. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; This is the universally quantified loop preservation and exit obligation.
;; The integer guard preserves the source quantifier domain exactly.

(defun-sk sf-reduce-to-zero-loop-obligation-p ()
  (forall (x1)
    (implies
     (and
      (integerp x1)
      (<= 0 x1))
     (if (not (equal x1 0))
         (and
          (and
           (<= 0 x1)
           (< (- x1 1) x1))
          (<= 0 (- x1 1)))
       (equal x1 0)))))

;; The source's integer parameter and nonnegativity hypothesis are explicit.
;; The conclusion retains both the initialized invariant and the complete
;; universally quantified loop obligation.

(defun ntp4vc-pearl-sf-hoarelogic-reduce-to-zeroqtvc-statement (x)
  (implies
   (and
    (integerp x)
    (<= 0 x))
   (and
    (<= 0 x)
    (sf-reduce-to-zero-loop-obligation-p))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
