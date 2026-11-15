;; Statement-only formalization of miniF2F corpus artifact amc12a_2021_p8:
;; the unique natural-number sequence with d(0)=0, d(1)=0, d(2)=1 and
;; d(n)=d(n-1)+d(n-3) for every n>=3 is even at indices 2021 and 2023
;; and odd at index 2022. This file contains no proof.

(in-package "ACL2")

;; The source quantifies over every natural-valued function satisfying the
;; initial values and recurrence. Those conditions determine exactly one
;; function by induction. The transition
;;
;;   (d(n), d(n+1), d(n+2)) -> (d(n+1), d(n+2), d(n+2)+d(n))
;;
;; defines that function at every natural index, so the closed predicate below
;; is equivalent in both directions to the source's universally quantified
;; implication.
(defun amc12a-2021-p8-sequence-aux (steps a b c)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      a
    (amc12a-2021-p8-sequence-aux
     (- steps 1)
     b
     c
     (+ c a))))

(defun amc12a-2021-p8-sequence (n)
  (if (natp n)
      (amc12a-2021-p8-sequence-aux n 0 0 1)
    0))

(defun amc12a-2021-p8-statement ()
  (and
   (equal (mod (amc12a-2021-p8-sequence 2021) 2) 0)
   (equal (mod (amc12a-2021-p8-sequence 2022) 2) 1)
   (equal (mod (amc12a-2021-p8-sequence 2023) 2) 0)))

(value-triple :itpeval-statement-checked)
:q
