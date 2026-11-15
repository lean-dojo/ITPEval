;; Statement-only formalization of PutnamBench corpus artifact putnam_1998_b4:
;; for positive natural m and n, an alternating floor-quotient sum vanishes
;; exactly when m and n have different 2-adic valuations. This file contains
;; no proof.

(in-package "ACL2")

;; For positive n, this is the greatest exponent k such that 2^k divides n.
(defun putnam-1998-b4-two-adic-valuation (n)
  (declare (xargs :measure (nfix n)))
  (if (and (posp n)
           (equal (mod n 2) 0))
      (+ 1
         (putnam-1998-b4-two-adic-valuation
          (floor n 2)))
    0))

;; Inclusive sum from i = 0 through upper of
;; (-1)^(floor(i/m) + floor(i/n)).
(defun putnam-1998-b4-alternating-sum-through (m n upper)
  (declare (xargs :measure (nfix upper)))
  (let ((term
         (expt -1
               (+ (floor upper m)
                  (floor upper n)))))
    (if (zp upper)
        term
      (+ (putnam-1998-b4-alternating-sum-through
          m n (- upper 1))
         term))))

(defun putnam-1998-b4-solution-p (m n)
  (not
   (equal
    (putnam-1998-b4-two-adic-valuation m)
    (putnam-1998-b4-two-adic-valuation n))))

(defun putnambench-putnam-1998-b4-statement (m n)
  (implies
   (and (posp m)
        (posp n))
   (iff
    (equal
     (putnam-1998-b4-alternating-sum-through
      m n (- (* m n) 1))
     0)
    (putnam-1998-b4-solution-p m n))))

(value-triple :itpeval-statement-checked)
:q
