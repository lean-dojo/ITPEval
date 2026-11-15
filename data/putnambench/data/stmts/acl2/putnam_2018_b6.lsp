;; Statement-only formalization of PutnamBench corpus artifact putnam_2018_b6:
;; the number of length-2018 sequences over {1,2,3,4,5,6,10} with sum 3860
;; is at most 2^3860 times (2018/2048)^2018. This file contains no proof.

(in-package "ACL2")

;; At each positive LENGTH, the seven recursive calls choose the next term.
;; Thus this counts every sequence over the stated alphabet exactly once, and
;; the base case accepts exactly those choices whose total is TARGET.
(defun putnam-2018-b6-sequence-count (length target)
  (declare (xargs :measure (nfix length)))
  (if (zp length)
      (if (equal target 0) 1 0)
    (+
     (putnam-2018-b6-sequence-count
      (- length 1) (- target 1))
     (putnam-2018-b6-sequence-count
      (- length 1) (- target 2))
     (putnam-2018-b6-sequence-count
      (- length 1) (- target 3))
     (putnam-2018-b6-sequence-count
      (- length 1) (- target 4))
     (putnam-2018-b6-sequence-count
      (- length 1) (- target 5))
     (putnam-2018-b6-sequence-count
      (- length 1) (- target 6))
     (putnam-2018-b6-sequence-count
      (- length 1) (- target 10)))))

;; ACL2 rationals are exact, so this is the source real inequality because
;; both the cardinality and the displayed upper bound are rational numbers.
(defun putnambench-putnam-2018-b6-statement ()
  (<=
   (putnam-2018-b6-sequence-count 2018 3860)
   (*
    (expt 2 3860)
    (expt (/ 2018 2048) 2018))))

(value-triple :itpeval-statement-checked)
:q
