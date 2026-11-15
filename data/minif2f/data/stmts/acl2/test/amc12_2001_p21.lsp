;; Statement-only formalization of miniF2F corpus artifact amc12_2001_p21:
;; four natural numbers whose product is 8 factorial and which satisfy three
;; adjacent bilinear equations have integer difference a - d equal to 10.
;; This file contains no proof.

(in-package "ACL2")

(defun amc12-2001-p21-factorial (n)
  (if (zp n)
      1
    (* n (amc12-2001-p21-factorial (- n 1)))))

(defun amc12-2001-p21-statement (a b c d)
  (implies
   (and (natp a)
        (natp b)
        (natp c)
        (natp d)
        (equal (* (* (* a b) c) d)
               (amc12-2001-p21-factorial 8))
        (equal (+ (+ (* a b) a) b) 524)
        (equal (+ (+ (* b c) b) c) 146)
        (equal (+ (+ (* c d) c) d) 104))
   (equal (- a d) 10)))

(value-triple :itpeval-statement-checked)
:q
