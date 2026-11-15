;; Statement-only formalization of miniF2F corpus artifact amc12b_2002_p7:
;; positive natural numbers a, b, and c are consecutive, their product is
;; eight times their sum, and their sum of squares is 77. This file contains
;; no proof.

(in-package "ACL2")

(defun amc12b-2002-p7-statement (a b c)
  (implies (and (natp a)
                (natp b)
                (natp c)
                (< 0 a)
                (< 0 b)
                (< 0 c)
                (equal b (+ a 1))
                (equal c (+ b 1))
                (equal (* (* a b) c)
                       (* 8 (+ (+ a b) c))))
           (equal (+ (expt a 2)
                     (+ (expt b 2)
                        (expt c 2)))
                  77)))

(value-triple :itpeval-statement-checked)
:q
