;; Statement-only formalization of PutnamBench corpus artifact putnam_2015_b2:
;; existence of a sum ending in 2015 in the sequence formed by repeatedly
;; crossing off the three least remaining positive integers and their sum.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; REMOVED is the finite set of positive integers crossed off before a round,
;; represented extensionally by membership in a list.  A list of length k
;; cannot contain every integer from 1 through k+1, so the bounded sequential
;; search below returns the least positive integer not in REMOVED.  The bound
;; is derived from the current state rather than imposing any bound on the
;; number of rounds or on the values in the sequence.

(defun putnam-2015-b2-first-available-aux
    (candidate fuel removed)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      candidate
    (if (member-equal candidate removed)
        (putnam-2015-b2-first-available-aux
         (+ candidate 1)
         (- fuel 1)
         removed)
      candidate)))

(defun putnam-2015-b2-first-available (removed)
  (putnam-2015-b2-first-available-aux
   1
   (+ (len removed) 1)
   removed))

;; A round selects the three successive minima of the remaining positive
;; integers and records their sum.

(defun putnam-2015-b2-round-values (removed)
  (let* ((first
          (putnam-2015-b2-first-available removed))
         (second
          (putnam-2015-b2-first-available
           (cons first removed)))
         (third
          (putnam-2015-b2-first-available
           (cons second (cons first removed))))
         (sum (+ first second third)))
    (list first second third sum)))

(defun putnam-2015-b2-next-state (removed)
  (let ((round
         (putnam-2015-b2-round-values removed)))
    (cons
     (nth 3 round)
     (cons
      (nth 2 round)
      (cons
       (nth 1 round)
       (cons (nth 0 round) removed))))))

;; STATE n is exactly the finite complement, within the positive integers, of
;; the source set SETS n.  Thus the recursion is definitionally equivalent to
;; starting with {1,2,3,...} and applying the source's exact set update at each
;; round.

(defun putnam-2015-b2-state (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (putnam-2015-b2-next-state
     (putnam-2015-b2-state (- n 1)))))

(defun putnam-2015-b2-sum (n)
  (nth
   3
   (putnam-2015-b2-round-values
    (putnam-2015-b2-state n))))

;; This is the solution constant recorded by the source formalizations.

(defun putnam-2015-b2-solution ()
  t)

;; The round index remains an internal, unbounded natural-number witness.

(defun-sk putnam-2015-b2-sum-ending-in-2015-p ()
  (exists (n)
    (and
     (natp n)
     (equal
      (mod (putnam-2015-b2-sum n) 10000)
      2015))))

(defun putnambench-putnam-2015-b2-statement ()
  (iff
   (putnam-2015-b2-sum-ending-in-2015-p)
   (putnam-2015-b2-solution)))

(value-triple :itpeval-statement-checked)
:q
