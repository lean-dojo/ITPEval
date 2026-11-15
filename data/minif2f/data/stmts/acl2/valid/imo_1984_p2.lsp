;; Statement-only formalization of miniF2F corpus artifact imo_1984_p2:
;; positive integers a and b satisfying the stated nondivisibility and
;; seventh-power divisibility conditions have a + b at least 19.
;; This file contains no proof.

(in-package "ACL2")

(defun imo-1984-p2-statement (a b)
  (implies
   (and (integerp a)
        (integerp b)
        (< 0 a)
        (< 0 b)
        (not (equal (mod a 7) 0))
        (not (equal (mod b 7) 0))
        (not (equal (mod (+ a b) 7) 0))
        (equal
         (mod
          (- (- (expt (+ a b) 7)
                (expt a 7))
             (expt b 7))
          (expt 7 7))
         0))
   (<= 19 (+ a b))))

(value-triple :itpeval-statement-checked)
:q
