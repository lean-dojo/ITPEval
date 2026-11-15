;; Statement-only formalization of miniF2F artifact amc12a_2003_p5:
;; for natural-number digits A, M, and C bounded above by 9, if the base-10
;; digit sequences (A,M,C,1,0) and (A,M,C,1,2) sum to 123422, then A+M+C=14.
;; This file contains no proof.

(in-package "ACL2")

(defun amc12a-2003-p5-decimal (a m c units)
  (+ (* 10
        (+ (* 10
              (+ (* 10
                    (+ (* 10 a) m))
                 c))
           1))
     units))

(defun amc12a-2003-p5-statement (a m c)
  (implies
   (and (natp a)
        (natp m)
        (natp c)
        (<= a 9)
        (<= m 9)
        (<= c 9)
        (equal (+ (amc12a-2003-p5-decimal a m c 0)
                  (amc12a-2003-p5-decimal a m c 2))
               123422))
   (equal (+ a (+ m c)) 14)))

(value-triple :itpeval-statement-checked)
:q
