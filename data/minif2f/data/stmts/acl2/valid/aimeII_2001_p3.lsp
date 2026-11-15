;; Statement-only formalization of miniF2F valid artifact aimeII_2001_p3:
;; the integer sequence with initial values 211, 375, 420, 523 and the given
;; fourth-order recurrence has terms at indices 531, 753, and 975 summing to
;; 898. This file contains no proof.
;;
;; The hypotheses uniquely determine every positive-indexed term. Every source
;; sequence therefore agrees there with the recursive sequence below; conversely
;; this sequence, with the source's unconstrained and unused index 0 set to 0,
;; satisfies all source hypotheses. Thus the predicate is bidirectionally
;; equivalent to the universally quantified source implication.

(in-package "ACL2")

(defun aime-ii-2001-p3-sequence (n)
  (declare (xargs :measure (nfix n)))
  (if (natp n)
      (cond ((equal n 1) 211)
            ((equal n 2) 375)
            ((equal n 3) 420)
            ((equal n 4) 523)
            ((<= 5 n)
             (- (+ (- (aime-ii-2001-p3-sequence (- n 1))
                      (aime-ii-2001-p3-sequence (- n 2)))
                   (aime-ii-2001-p3-sequence (- n 3)))
                (aime-ii-2001-p3-sequence (- n 4))))
            (t 0))
    0))

(defun aime-ii-2001-p3-statement ()
  (equal (+ (aime-ii-2001-p3-sequence 531)
            (aime-ii-2001-p3-sequence 753)
            (aime-ii-2001-p3-sequence 975))
         898))

(value-triple :itpeval-statement-checked)
:q
