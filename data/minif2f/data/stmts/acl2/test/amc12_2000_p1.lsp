;; Statement-only formalization of miniF2F artifact amc12_2000_p1: for
;; pairwise-distinct positive natural numbers i, m, and o whose product is
;; 2001, their sum is at most 671. This file contains no proof.

(in-package "ACL2")

(defun amc12-2000-p1-statement (i m o)
  (implies (and (natp i)
                (natp m)
                (natp o)
                (< 0 i)
                (< 0 m)
                (< 0 o)
                (not (equal i m))
                (not (equal m o))
                (not (equal o i))
                (equal (* (* i m) o) 2001))
           (<= (+ (+ i m) o) 671)))

(value-triple :itpeval-statement-checked)
:q
