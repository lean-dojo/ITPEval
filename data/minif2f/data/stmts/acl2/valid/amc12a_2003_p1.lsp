;; Statement-only formalization of miniF2F corpus artifact amc12a_2003_p1:
;; the difference between the first 2003 terms of the natural sequences
;; u(n) = 2*n + 2 and v(n) = 2*n + 1 is 2003. This file contains no proof.
;;
;; The source hypotheses uniquely determine u and v, so the two recursive
;; sums below eliminate those function parameters definitionally. The
;; Isabelle and Metamath sources use an index-shifted presentation; every
;; presentation has exactly 2003 paired terms with termwise difference one.

(in-package "ACL2")

(defun amc12a-2003-p1-u-sum (remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let ((n (- remaining 1)))
      (+ (amc12a-2003-p1-u-sum n)
         (+ (* 2 n) 2)))))

(defun amc12a-2003-p1-v-sum (remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let ((n (- remaining 1)))
      (+ (amc12a-2003-p1-v-sum n)
         (+ (* 2 n) 1)))))

(defun amc12a-2003-p1-natural-subtraction (x y)
  (if (< x y)
      0
    (- x y)))

(defun amc12a-2003-p1-statement ()
  (equal
   (amc12a-2003-p1-natural-subtraction
    (amc12a-2003-p1-u-sum 2003)
    (amc12a-2003-p1-v-sum 2003))
   2003))

(value-triple :itpeval-statement-checked)
:q
