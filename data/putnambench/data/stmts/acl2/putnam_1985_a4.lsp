;; Statement-only formalization of PutnamBench corpus artifact putnam_1985_a4:
;; the sequence a_1 = 3 and a_(i+1) = 3^(a_i) has 87 as the unique
;; last-two-digit residue occurring infinitely often. This file contains no proof.

(in-package "ACL2")

;; This is an arbitrary sequence. Its natural-number codomain, initial value,
;; and recurrence are explicit hypotheses of the statement below.
(defstub putnam-1985-a4-sequence (index) t)

(defun-sk putnam-1985-a4-natural-valued-p ()
  (forall (index)
    (implies
     (natp index)
     (natp (putnam-1985-a4-sequence index)))))

(defun-sk putnam-1985-a4-recurrence-p ()
  (forall (index)
    (implies
     (and
      (natp index)
      (<= 1 index))
     (equal
      (putnam-1985-a4-sequence (+ index 1))
      (expt 3 (putnam-1985-a4-sequence index))))))

;; For fixed RESIDUE and BOUND, this retains the source's existential index.
(defun-sk putnam-1985-a4-occurs-after-p (residue bound)
  (exists (index)
    (and
     (natp index)
     (<= bound index)
     (equal
      (mod (putnam-1985-a4-sequence index) 100)
      residue))))

;; A residue occurs infinitely often exactly when it occurs beyond every
;; natural-number bound.
(defun-sk putnam-1985-a4-occurs-infinitely-often-p (residue)
  (forall (bound)
    (implies
     (natp bound)
     (putnam-1985-a4-occurs-after-p residue bound))))

;; Extensional equality of the source set with the singleton set {87}.
(defun-sk putnam-1985-a4-solution-set-p ()
  (forall (residue)
    (implies
     (natp residue)
     (iff
      (and
       (< residue 100)
       (putnam-1985-a4-occurs-infinitely-often-p residue))
      (equal residue 87)))))

(defun putnambench-putnam-1985-a4-statement ()
  (implies
   (and
    (putnam-1985-a4-natural-valued-p)
    (equal (putnam-1985-a4-sequence 1) 3)
    (putnam-1985-a4-recurrence-p))
   (putnam-1985-a4-solution-set-p)))

(value-triple :itpeval-statement-checked)
:q
