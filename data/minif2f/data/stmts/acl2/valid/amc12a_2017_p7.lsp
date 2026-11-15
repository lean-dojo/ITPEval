;; Statement-only formalization of miniF2F corpus artifact amc12a_2017_p7:
;; every real-valued sequence with f(1) = 2, increasing by 1 from the
;; preceding term at even indices greater than 1 and by 2 from the term two
;; places earlier at odd indices greater than 1, has f(2017) = 2018. This
;; file contains no proof.
;;
;; The hypotheses uniquely determine every positive-indexed term. Every
;; satisfying source sequence therefore agrees there with the recursive
;; sequence below; conversely, this sequence, with the unconstrained value at
;; index 0 set to 0, satisfies the hypotheses. All determined terms are
;; integers embedded in the reals, so ACL2's exact integer arithmetic
;; preserves the sequence. Thus the closed predicate is bidirectionally
;; equivalent to the universally quantified source implication.

(in-package "ACL2")

(defun amc12a-2017-p7-sequence (n)
  (declare (xargs :measure (nfix n)))
  (if (not (natp n))
      0
    (cond ((equal n 0) 0)
          ((equal n 1) 2)
          ((equal (mod n 2) 0)
           (+ (amc12a-2017-p7-sequence (- n 1)) 1))
          (t
           (+ (amc12a-2017-p7-sequence (- n 2)) 2)))))

(defun amc12a-2017-p7-statement ()
  (equal (amc12a-2017-p7-sequence 2017)
         2018))

(value-triple :itpeval-statement-checked)
:q
