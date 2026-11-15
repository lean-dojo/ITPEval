;; Statement-only formalization of miniF2F corpus artifact
;; amc12b_2002_p11: if a, b, their sum, and the truncated natural difference
;; a - b are prime, then a + b + ((a - b) + (a + b)) is prime. This file
;; contains no proof.

(in-package "ACL2")

(defun amc12b-2002-p11-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (amc12b-2002-p11-no-divisor-from-p n (+ d 1)))
    t))

(defun amc12b-2002-p11-primep (n)
  (and (natp n)
       (< 1 n)
       (amc12b-2002-p11-no-divisor-from-p n 2)))

(defun amc12b-2002-p11-statement (a b)
  (implies
   (and (natp a)
        (natp b)
        (amc12b-2002-p11-primep a)
        (amc12b-2002-p11-primep b)
        (amc12b-2002-p11-primep (+ a b))
        (amc12b-2002-p11-primep (nfix (- a b))))
   (amc12b-2002-p11-primep
    (+ (+ a b)
       (+ (nfix (- a b))
          (+ a b))))))

(value-triple :itpeval-statement-checked)
:q
