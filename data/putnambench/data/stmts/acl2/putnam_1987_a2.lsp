;; Statement-only formalization of PutnamBench corpus artifact putnam_1987_a2:
;; the 10^1987-th digit in the concatenation of the positive integers lies
;; in the block of 1984-digit integers. This file contains no proof.

(in-package "ACL2")

;; For positive M this is
;;
;;   sum_(d=1)^M 9*d*10^(d-1),
;;
;; the exact number of digits occupied by the positive integers having at
;; most M decimal digits.
(defun putnam-1987-a2-digits-through-width (m)
  (if (posp m)
      (/ (+ 1
            (* (- (* 9 m) 1)
               (expt 10 m)))
         9)
    0))

;; The source recurrence for SEQIND and its SEQSIZE clauses define the same
;; concatenation. Hence f(1987)=1984 is equivalent to saying that position
;; 10^1987 is after every at-most-1983-digit integer and no later than the
;; last digit of the 1984-digit integers.
(defun putnambench-putnam-1987-a2-statement ()
  (let ((position (expt 10 1987)))
    (and
     (< (putnam-1987-a2-digits-through-width 1983)
        position)
     (<= position
         (putnam-1987-a2-digits-through-width 1984)))))

(value-triple :itpeval-statement-checked)
:q
