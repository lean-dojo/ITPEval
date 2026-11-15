;; Statement-only formalization of miniF2F artifact imo_2001_p6: positive
;; natural numbers d < c < b < a satisfying the stated natural-arithmetic
;; identity make a*b + c*d nonprime. This file contains no proof.

(in-package "ACL2")

(defun imo-2001-p6-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (imo-2001-p6-no-divisor-from-p n (+ d 1)))
    t))

(defun imo-2001-p6-primep (n)
  (and (natp n)
       (< 1 n)
       (imo-2001-p6-no-divisor-from-p n 2)))

;; On natural inputs, nfix of an integer difference is truncated natural
;; subtraction.
(defun imo-2001-p6-statement (a b c d)
  (implies
   (and (natp a)
        (natp b)
        (natp c)
        (natp d)
        (< 0 a)
        (< 0 b)
        (< 0 c)
        (< 0 d)
        (< d c)
        (< c b)
        (< b a)
        (equal (+ (* a c) (* b d))
               (* (nfix (- (+ b d a) c))
                  (nfix (- (+ b d c) a)))))
   (not (imo-2001-p6-primep
         (+ (* a b) (* c d))))))

(value-triple :itpeval-statement-checked)
:q
