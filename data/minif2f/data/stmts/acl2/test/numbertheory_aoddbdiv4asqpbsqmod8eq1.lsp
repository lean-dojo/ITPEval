;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_aoddbdiv4asqpbsqmod8eq1: for every odd integer a and
;; nonnegative integer b divisible by 4, a^2 + b^2 has remainder 1 modulo 8.
;; This file contains no proof.

(in-package "ACL2")

(defun numbertheory-aoddbdiv4asqpbsqmod8eq1-statement (a b)
  (implies
   (and (integerp a)
        (integerp b)
        (equal (mod a 2) 1)
        (<= 0 b)
        (equal (mod b 4) 0))
   (equal (mod (+ (* a a)
                  (* b b))
               8)
          1)))

(value-triple :itpeval-statement-checked)
:q
