;; Statement-only formalization of miniF2F corpus artifact imo_1984_p6:
;; positive odd natural numbers a < b < c < d whose endpoint and middle sums
;; are powers of two and satisfy a*d = b*c must have a = 1. This file contains
;; no proof.

(in-package "ACL2")

(defun imo-1984-p6-statement (a b c d k m)
  (implies
   (and (natp a)
        (natp b)
        (natp c)
        (natp d)
        (natp k)
        (natp m)
        (< 0 a)
        (< 0 b)
        (< 0 c)
        (< 0 d)
        (equal (mod a 2) 1)
        (equal (mod b 2) 1)
        (equal (mod c 2) 1)
        (equal (mod d 2) 1)
        (< a b)
        (< b c)
        (< c d)
        (equal (* a d) (* b c))
        (equal (+ a d) (expt 2 k))
        (equal (+ b c) (expt 2 m)))
   (equal a 1)))

(value-triple :itpeval-statement-checked)
:q
