;; Statement-only formalization of PutnamBench corpus artifact putnam_2002_a3:
;; for every integer n at least 2, the number Tn of nonempty subsets of
;; {1,...,n} having integer average satisfies that Tn-n is even. This file
;; contains no proof.

(in-package "ACL2")

;; Each branch makes the next interval element absent or present. At a leaf,
;; CHOSEN-COUNT and CHOSEN-SUM are exactly the cardinality and sum of one
;; subset. For a nonempty integer subset, its real average is an integer
;; exactly when its cardinality divides its sum.

(defun putnam-2002-a3-count-integer-average-subsets
    (next remaining chosen-count chosen-sum)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (if (and (< 0 chosen-count)
               (equal (mod chosen-sum chosen-count) 0))
          1
        0)
    (+
     (putnam-2002-a3-count-integer-average-subsets
      (+ next 1)
      (- remaining 1)
      chosen-count
      chosen-sum)
     (putnam-2002-a3-count-integer-average-subsets
      (+ next 1)
      (- remaining 1)
      (+ chosen-count 1)
      (+ chosen-sum next)))))

(defun putnam-2002-a3-tn (n)
  (putnam-2002-a3-count-integer-average-subsets
   1 n 0 0))

(defun putnambench-putnam-2002-a3-statement (n tn)
  (implies
   (and
    (integerp n)
    (integerp tn)
    (<= 2 n)
    (equal tn (putnam-2002-a3-tn n)))
   (equal (mod (- tn n) 2) 0)))

(value-triple :itpeval-statement-checked)
:q
