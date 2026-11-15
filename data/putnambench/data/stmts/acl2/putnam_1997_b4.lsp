;; Statement-only formalization of PutnamBench corpus artifact putnam_1997_b4:
;; coefficients of (1+x+x^2)^m give an alternating finite sum between zero
;; and one for every natural k. This file contains no proof.

(in-package "ACL2")

;; This recurrence is exactly the coefficient of x^n in (1+x+x^2)^m.
(defun putnam-1997-b4-trinomial-coefficient (m n)
  (declare (xargs :measure (nfix m)))
  (if (or (not (natp m))
          (not (natp n)))
      0
    (if (zp m)
        (if (zp n) 1 0)
      (+ (putnam-1997-b4-trinomial-coefficient (- m 1) n)
         (putnam-1997-b4-trinomial-coefficient
          (- m 1) (- n 1))
         (putnam-1997-b4-trinomial-coefficient
          (- m 1) (- n 2))))))

;; Inclusive sum from i = 0 through upper of
;; (-1)^i times the coefficient of x^i in (1+x+x^2)^(k-i).
(defun putnam-1997-b4-alternating-sum (k upper)
  (declare (xargs :measure (nfix upper)))
  (if (zp upper)
      (putnam-1997-b4-trinomial-coefficient k 0)
    (+ (putnam-1997-b4-alternating-sum k (- upper 1))
       (* (expt -1 upper)
          (putnam-1997-b4-trinomial-coefficient
           (- k upper) upper)))))

(defun putnambench-putnam-1997-b4-statement (k)
  (implies
   (natp k)
   (let ((sum
          (putnam-1997-b4-alternating-sum
           k (floor (* 2 k) 3))))
     (and (<= 0 sum)
          (<= sum 1)))))

(value-triple :itpeval-statement-checked)
:q
