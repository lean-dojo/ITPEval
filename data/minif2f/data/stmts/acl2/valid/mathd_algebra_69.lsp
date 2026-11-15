;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_69:
;; natural numbers of rows and seats satisfying two equal total-seat counts
;; have exactly 25 rows. This file contains no proof.

(in-package "ACL2")

;; NFIX encodes the truncated natural-number subtraction in seats - 3.
(defun mathd-algebra-69-statement (rows seats)
  (implies
   (and (natp rows)
        (natp seats)
        (equal (* rows seats) 450)
        (equal (* (+ rows 5)
                  (nfix (- seats 3)))
               450))
   (equal rows 25)))

(value-triple :itpeval-statement-checked)
:q
