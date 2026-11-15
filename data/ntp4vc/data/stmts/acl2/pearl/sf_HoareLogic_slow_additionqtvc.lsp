;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sf_HoareLogic_slow_additionqtvc: the slow-addition loop verification
;; condition over unbounded mathematical integers, preserving nonnegativity
;; and the invariant z + x1 = z1 + x while decrementing x1. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; This is the universally quantified loop preservation and exit obligation.
;; Integer guards preserve the source quantifier domains exactly.

(defun-sk sf-slow-addition-loop-obligation-p (x z1)
  (forall (z x1)
    (implies
     (and
      (integerp z)
      (integerp x1))
     (implies
      (and
       (<= 0 x1)
       (equal (+ z x1) (+ z1 x)))
      (if (not (equal x1 0))
          (and
           (and
            (<= 0 x1)
            (< (- x1 1) x1))
           (<= 0 (- x1 1))
           (equal
            (+ (+ z 1) (- x1 1))
            (+ z1 x)))
        (equal z (+ z1 x)))))))

;; The outer universal quantifier and implication encode the source integer
;; parameters and its sole hypothesis. The conclusion retains the initialized
;; invariant and the complete loop obligation.

(defun-sk
  ntp4vc-pearl-sf-hoarelogic-slow-additionqtvc-statement
  ()
  (forall (x z1)
    (implies
     (and
      (integerp x)
      (integerp z1)
      (<= 0 x))
     (and
      (<= 0 x)
      (sf-slow-addition-loop-obligation-p x z1)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
