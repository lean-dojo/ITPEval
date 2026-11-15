;; Statement-only formalization of miniF2F artifact amc12_2000_p6: for prime
;; natural numbers p and q between 4 and 18 inclusive, p*q - (p+q) is not
;; 194. This file contains no proof.

(in-package "ACL2")

(defun amc12-2000-p6-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (amc12-2000-p6-no-divisor-from-p n (+ d 1)))
    t))

(defun amc12-2000-p6-primep (n)
  (and (natp n)
       (< 1 n)
       (amc12-2000-p6-no-divisor-from-p n 2)))

(defun amc12-2000-p6-statement (p q)
  (implies
   (and (natp p)
        (natp q)
        (amc12-2000-p6-primep p)
        (amc12-2000-p6-primep q)
        (<= 4 p)
        (<= p 18)
        (<= 4 q)
        (<= q 18))
   (not (equal (- (* p q) (+ p q)) 194))))

(value-triple :itpeval-statement-checked)
:q
