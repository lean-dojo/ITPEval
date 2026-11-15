;; Statement-only formalization of PutnamBench corpus artifact putnam_2018_b1:
;; the integer vectors whose removal from the 3 by 101 grid leaves a partition
;; into two sets of equal size and equal vector sum. This file contains no proof.

(in-package "ACL2")

;; Index I names the grid point (floor(I/101), I mod 101). Recursing over all
;; 303 indices and choosing Q or R for every point other than the omitted one
;; ranges bijectively over every partition of P \ {v}. The accumulated
;; cardinalities and coordinate sums therefore encode exactly the source's
;; internal existentially quantified sets Q and R.
(defun putnam-2018-b1-partition-exists-p
    (remaining omitted-a omitted-b
               q-card q-sum-a q-sum-b
               r-card r-sum-a r-sum-b)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (and
       (equal q-card r-card)
       (equal q-sum-a r-sum-a)
       (equal q-sum-b r-sum-b))
    (let* ((index (- remaining 1))
           (a (floor index 101))
           (b (mod index 101))
           (next (- remaining 1)))
      (if (and (equal a omitted-a)
               (equal b omitted-b))
          (putnam-2018-b1-partition-exists-p
           next omitted-a omitted-b
           q-card q-sum-a q-sum-b
           r-card r-sum-a r-sum-b)
        (or
         (putnam-2018-b1-partition-exists-p
          next omitted-a omitted-b
          (+ q-card 1) (+ q-sum-a a) (+ q-sum-b b)
          r-card r-sum-a r-sum-b)
         (putnam-2018-b1-partition-exists-p
          next omitted-a omitted-b
          q-card q-sum-a q-sum-b
          (+ r-card 1) (+ r-sum-a a) (+ r-sum-b b)))))))

(defun putnam-2018-b1-grid-member-p (a b)
  (and
   (integerp a)
   (integerp b)
   (<= 0 a)
   (<= a 2)
   (<= 0 b)
   (<= b 100)))

(defun putnam-2018-b1-solution-member-p (a b)
  (and
   (integerp a)
   (integerp b)
   (equal a 1)
   (<= 0 b)
   (<= b 100)
   (equal (mod b 2) 0)))

(defun putnambench-putnam-2018-b1-statement (a b)
  (implies
   (and (integerp a)
        (integerp b))
   (equal
    (and
     (putnam-2018-b1-grid-member-p a b)
     (putnam-2018-b1-partition-exists-p
      303 a b
      0 0 0
      0 0 0))
    (putnam-2018-b1-solution-member-p a b))))

(value-triple :itpeval-statement-checked)
:q
