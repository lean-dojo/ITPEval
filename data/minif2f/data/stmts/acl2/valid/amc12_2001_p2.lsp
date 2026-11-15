;; Statement-only formalization of miniF2F artifact amc12_2001_p2:
;; natural numbers a, b, and n form a two-digit number n = 10*a + b that
;; also satisfies n = a*b + a + b, under the stated digit bounds, implying
;; b = 9. This file contains no proof.

(in-package "ACL2")

(defun amc12-2001-p2-statement (a b n)
  (implies (and (natp a)
                (natp b)
                (natp n)
                (<= 1 a)
                (<= a 9)
                (<= 0 b)
                (<= b 9)
                (equal n (+ (* 10 a) b))
                (equal n (+ (* a b) (+ a b))))
           (equal b 9)))

(value-triple :itpeval-statement-checked)
:q
