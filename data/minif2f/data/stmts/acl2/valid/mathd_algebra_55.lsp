;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_55:
;; the ratio of two real numbers defined by alternating arithmetic sums is
;; 2/3. This file contains no proof.
;;
;; The defining equalities force q = 8 and p = 12, so every satisfying real
;; assignment is rational. Conversely, each guarded ACL2 assignment embeds
;; unchanged into the reals. Thus the rational guards preserve exactly the
;; source implication.

(in-package "ACL2")

(defun mathd-algebra-55-statement (q p)
  (implies
   (and (rationalp q)
        (rationalp p)
        (equal q
               (+ (- (+ (- (+ (- 2 4) 6) 8) 10) 12) 14))
        (equal p
               (+ (- (+ (- (+ (- 3 6) 9) 12) 15) 18) 21)))
   (equal (/ q p)
          (/ 2 3))))

(value-triple :itpeval-statement-checked)
:q
