;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sf_HoareLogic_factorialqtvc: the factorial loop verification
;; condition using the zero value and positive recurrence of integer
;; factorial. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; FACT is the source's arbitrary integer-valued function. Its source typing
;; and axioms are explicit hypotheses of the statement.

(defstub shlf-fact (n) t)

(defun-sk shlf-fact-integer-valued-p ()
  (forall (n)
    (implies
     (integerp n)
     (integerp (shlf-fact n)))))

(defun shlf-fact-zero-law-p ()
  (equal (shlf-fact 0) 1))

(defun-sk shlf-fact-positive-recurrence-p ()
  (forall (n)
    (implies
     (and
      (integerp n)
      (< 0 n))
     (equal
      (shlf-fact n)
      (* n (shlf-fact (- n 1)))))))

(defun shlf-fact-laws-p ()
  (and
   (shlf-fact-integer-valued-p)
   (shlf-fact-zero-law-p)
   (shlf-fact-positive-recurrence-p)))

;; This keeps z and y universally quantified inside the third conjunct of the
;; verification condition.

(defun-sk shlf-loop-step-p (x)
  (forall (z y)
    (implies
     (and
      (integerp z)
      (integerp y)
      (<= 0 z)
      (equal
       (* y (shlf-fact z))
       (shlf-fact x)))
     (if (not (equal z 0))
         (and
          (and
           (<= 0 z)
           (< (- z 1) z))
          (<= 0 (- z 1))
          (equal
           (* (* y z)
              (shlf-fact (- z 1)))
           (shlf-fact x)))
       (equal y (shlf-fact x))))))

(defun-sk
  ntp4vc-pearl-sf-hoarelogic-factorialqtvc-statement
  ()
  (forall (x)
    (implies
     (and
      (shlf-fact-laws-p)
      (integerp x)
      (<= 0 x))
     (and
      (<= 0 x)
      (equal
       (* 1 (shlf-fact x))
       (shlf-fact x))
      (shlf-loop-step-p x)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
