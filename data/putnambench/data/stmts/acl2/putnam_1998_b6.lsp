;; Statement-only formalization of PutnamBench corpus artifact putnam_1998_b6:
;; every integer-coefficient monic cubic has a positive integer input at which
;; its real square root is not an integer. This file contains no proof.

(in-package "ACL2")

(defun putnam-1998-b6-polynomial-value (a b c n)
  (+ (* n n n)
     (* a n n)
     (* b n)
     c))

(defun-sk putnam-1998-b6-integer-square-p (value)
  (exists (root)
    (and
     (integerp root)
     (equal value (* root root)))))

(defun putnam-1998-b6-sqrt-not-integer-p (a b c n)
  (let ((value
         (putnam-1998-b6-polynomial-value a b c n)))
    (and
     (integerp n)
     (< 0 n)
     (not (putnam-1998-b6-integer-square-p value)))))

(defun-sk putnam-1998-b6-witness-exists-p (a b c)
  (exists (n)
    (putnam-1998-b6-sqrt-not-integer-p a b c n)))

(defun putnambench-putnam-1998-b6-statement (a b c)
  (implies
   (and
    (integerp a)
    (integerp b)
    (integerp c))
   (putnam-1998-b6-witness-exists-p a b c)))

(value-triple :itpeval-statement-checked)
:q
