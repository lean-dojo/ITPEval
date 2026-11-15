;; Statement-only formalization of PutnamBench corpus artifact putnam_2020_a5:
;; the greatest integer having exactly 2020 representations as a sum of
;; Fibonacci numbers at distinct positive indices is F_4040 - 1. This file
;; contains no proof.

(in-package "ACL2")

;; This is the source Fibonacci sequence, including F_0 = 0, F_1 = 1.
(defun putnam-2020-a5-fibonacci (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (if (equal n 1)
        1
      (+ (putnam-2020-a5-fibonacci (- n 1))
         (putnam-2020-a5-fibonacci (- n 2))))))

;; Count subsets of {1,...,INDEX} whose Fibonacci values sum to REMAINING.
;; The two recursive branches omit or include INDEX, so each extensional
;; subset is counted exactly once; in particular the two indices with value
;; one remain distinct choices.
(defun putnam-2020-a5-subset-count-through (index remaining)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (if (equal remaining 0) 1 0)
    (let* ((current (nfix index))
           (weight (putnam-2020-a5-fibonacci current))
           (previous (- current 1)))
      (+ (putnam-2020-a5-subset-count-through
          previous remaining)
         (if (and (integerp remaining)
                  (<= weight remaining))
             (putnam-2020-a5-subset-count-through
              previous (- remaining weight))
           0)))))

;; For every positive k, F_k >= k-1. Hence a set with Fibonacci sum n cannot
;; contain an index above n+1. Enumerating subsets through n+1 is therefore
;; exactly the source cardinality over all finite sets, not a bounded-domain
;; approximation. For negative n the source set is empty and its cardinality
;; is zero.
(defun putnam-2020-a5-representation-count (n)
  (if (natp n)
      (putnam-2020-a5-subset-count-through (+ n 1) n)
    0))

(defun putnam-2020-a5-solution ()
  (- (putnam-2020-a5-fibonacci 4040) 1))

;; The source assumption uniquely defines a(n), so it is inlined above.
;; ACL2 universally closes N: the first conjunct places the designated
;; solution in {n | a(n)=2020}, and the implication says every member of that
;; set is at most the solution. Together these are exactly IsGreatest.
(defun putnambench-putnam-2020-a5-statement (n)
  (let ((solution (putnam-2020-a5-solution)))
    (and
     (equal
      (putnam-2020-a5-representation-count solution)
      2020)
     (implies
      (and
       (integerp n)
       (equal
        (putnam-2020-a5-representation-count n)
        2020))
      (<= n solution)))))

(value-triple :itpeval-statement-checked)
:q
