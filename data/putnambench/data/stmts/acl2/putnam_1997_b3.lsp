;; Statement-only formalization of PutnamBench corpus artifact putnam_1997_b3:
;; the positive integers whose exact harmonic sum has reduced denominator not
;; divisible by 5 are exactly 1 through 4, 20 through 24, 100 through 104,
;; and 120 through 124. This file contains no proof.

(in-package "ACL2")

(defun putnam-1997-b3-harmonic-sum (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (putnam-1997-b3-harmonic-sum (- n 1))
       (/ 1 n))))

(defun putnam-1997-b3-listed-solution-p (n)
  (or (and (<= 1 n)
           (<= n 4))
      (and (<= 20 n)
           (<= n 24))
      (and (<= 100 n)
           (<= n 104))
      (and (<= 120 n)
           (<= n 124))))

;; ACL2 represents every rational in canonical reduced form, with a positive
;; denominator. Thus DENOMINATOR applied to this exact finite sum is q_n from
;; the source statement.
(defun putnambench-putnam-1997-b3-statement (n)
  (implies
   (posp n)
   (iff
    (putnam-1997-b3-listed-solution-p n)
    (not
     (equal
      (mod (denominator (putnam-1997-b3-harmonic-sum n)) 5)
      0)))))

(value-triple :itpeval-statement-checked)
:q
