;; Statement-only formalization of PutnamBench corpus artifact putnam_1982_a5:
;; a strict lower bound for the positive gap below one of a sum of two
;; rational ratios of positive integers. This file contains no proof.

(in-package "ACL2")

(defun putnambench-putnam-1982-a5-statement (a b c d)
  (implies
   (and (integerp a)
        (integerp b)
        (integerp c)
        (integerp d)
        (< 0 a)
        (< 0 b)
        (< 0 c)
        (< 0 d)
        (<= (+ a c) 1982)
        (< (+ (/ a b) (/ c d)) 1))
   (< (/ 1 (expt 1983 3))
      (- (- 1 (/ a b))
         (/ c d)))))

(value-triple :itpeval-statement-checked)
:q
