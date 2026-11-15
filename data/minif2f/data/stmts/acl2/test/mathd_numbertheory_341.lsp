;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_341:
;; if natural decimal digits a, b, and c form the last three digits of 5^100,
;; then their sum is 13. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-341-statement (a b c)
  (implies (and (natp a)
                (natp b)
                (natp c)
                (<= a 9)
                (<= b 9)
                (<= c 9)
                (equal (mod (expt 5 100) 1000)
                       (+ (* 100 a) (* 10 b) c)))
           (equal (+ a b c) 13)))

(value-triple :itpeval-statement-checked)
:q
