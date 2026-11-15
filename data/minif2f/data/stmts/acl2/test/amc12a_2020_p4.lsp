;; Statement-only formalization of miniF2F corpus artifact amc12a_2020_p4:
;; exactly 100 four-digit natural numbers have only even decimal digits and
;; are divisible by 5. This file contains no proof.

(in-package "ACL2")

(defun amc12a-2020-p4-even-decimal-digit-p (digit)
  (and (natp digit)
       (< digit 10)
       (equal (mod digit 2) 0)))

(defun amc12a-2020-p4-qualifying-number-p (n)
  (and (natp n)
       (<= 1000 n)
       (<= n 9999)
       (amc12a-2020-p4-even-decimal-digit-p
        (floor n 1000))
       (amc12a-2020-p4-even-decimal-digit-p
        (mod (floor n 100) 10))
       (amc12a-2020-p4-even-decimal-digit-p
        (mod (floor n 10) 10))
       (amc12a-2020-p4-even-decimal-digit-p
        (mod n 10))
       (equal (mod n 5) 0)))

(defun amc12a-2020-p4-count-qualifying-through (limit)
  (declare (xargs :measure (nfix limit)))
  (if (zp limit)
      0
    (+ (if (amc12a-2020-p4-qualifying-number-p limit) 1 0)
       (amc12a-2020-p4-count-qualifying-through (- limit 1)))))

(defun amc12a-2020-p4-statement ()
  (equal (amc12a-2020-p4-count-qualifying-through 9999)
         100))

(value-triple :itpeval-statement-checked)
:q
