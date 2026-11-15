;; Statement-only formalization of PutnamBench corpus artifact putnam_1978_b6:
;; an upper bound for the square of a weighted sum of a doubly indexed family
;; of real numbers in the unit interval. This file contains no proof.

(in-package "ACL2")

;; For fixed positive m and n, the source expression uses exactly the entries
;; a(i,j) with 1 <= i <= n and 1 <= j <= m*i. A rational ragged row list
;; records precisely these finitely many coordinates.
;;
;; This representation is bidirectionally equivalent to the source statement.
;; Every rational row list extends to a total real-valued family by assigning
;; zero outside the recorded coordinates. Conversely, if a real family were a
;; counterexample, its finite restriction would make the inequality fail
;; strictly. The difference between the two sides is a polynomial in those
;; finitely many entries, hence is continuous, so rational density in the
;; unit cube gives a rational row-list counterexample.

(defun putnam-1978-b6-unit-rational-list-p (values)
  (if (consp values)
      (and (rationalp (car values))
           (<= 0 (car values))
           (<= (car values) 1)
           (putnam-1978-b6-unit-rational-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1978-b6-rows-p (rows m i remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (equal rows nil)
    (and (consp rows)
         (true-listp (car rows))
         (equal (len (car rows)) (* m i))
         (putnam-1978-b6-unit-rational-list-p (car rows))
         (putnam-1978-b6-rows-p
          (cdr rows) m (+ i 1) (- remaining 1)))))

(defun putnam-1978-b6-sum (values)
  (if (consp values)
      (+ (car values)
         (putnam-1978-b6-sum (cdr values)))
    0))

(defun putnam-1978-b6-weighted-sum (rows i)
  (if (consp rows)
      (+ (/ (putnam-1978-b6-sum (car rows)) i)
         (putnam-1978-b6-weighted-sum (cdr rows) (+ i 1)))
    0))

(defun putnam-1978-b6-unweighted-sum (rows)
  (if (consp rows)
      (+ (putnam-1978-b6-sum (car rows))
         (putnam-1978-b6-unweighted-sum (cdr rows)))
    0))

(defun putnambench-putnam-1978-b6-statement (rows m n)
  (implies
   (and (natp m)
        (< 0 m)
        (natp n)
        (< 0 n)
        (putnam-1978-b6-rows-p rows m 1 n))
   (<= (expt (putnam-1978-b6-weighted-sum rows 1) 2)
       (* 2 m (putnam-1978-b6-unweighted-sum rows)))))

(value-triple :itpeval-statement-checked)
:q
