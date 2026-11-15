;; Statement-only formalization of PutnamBench corpus artifact putnam_2018_b3:
;; the positive integers below 10^100 satisfying three simultaneous
;; divisibility conditions are exactly 2^2, 2^4, 2^16, and 2^256. This file
;; contains no proof.

(in-package "ACL2")

;; This is integer divisibility, including the source-relevant zero-divisor
;; case: 0 divides a value exactly when that value is 0.
(defun putnam-2018-b3-divides-p (divisor value)
  (and
   (integerp divisor)
   (integerp value)
   (if (equal divisor 0)
       (equal value 0)
     (equal (mod value divisor) 0))))

(defun putnam-2018-b3-qualifying-p (n)
  (and
   (integerp n)
   (< 0 n)
   (< n (expt 10 100))
   (putnam-2018-b3-divides-p
    n
    (expt 2 n))
   (putnam-2018-b3-divides-p
    (- n 1)
    (- (expt 2 n) 1))
   (putnam-2018-b3-divides-p
    (- n 2)
    (- (expt 2 n) 2))))

(defun putnam-2018-b3-solution-member-p (n)
  (or
   (equal n (expt 2 2))
   (equal n (expt 2 4))
   (equal n (expt 2 16))
   (equal n (expt 2 256))))

;; ACL2 universally closes N. This pointwise IFF is the source set equality.
;; Isabelle uses N>3 instead of positivity; N=1,2,3 fail the displayed
;; divisibility conditions, so the two characterizations are equivalent.
(defun putnambench-putnam-2018-b3-statement (n)
  (implies
   (integerp n)
   (iff
    (putnam-2018-b3-qualifying-p n)
    (putnam-2018-b3-solution-member-p n))))

(value-triple :itpeval-statement-checked)
:q
