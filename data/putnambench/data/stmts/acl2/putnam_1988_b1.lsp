;; Statement-only formalization of PutnamBench corpus artifact putnam_1988_b1:
;; every composite positive integer is xy+xz+yz+1 for positive integers
;; x, y, and z. This file contains no proof.

(in-package "ACL2")

;; If n = x*y+x*z+y*z+1 with x,y,z positive, then each of x,y,z is
;; strictly less than n. Thus the searches through n below are exactly the
;; source's internal existential quantifiers, not a restriction of them.

(defun putnam-1988-b1-positive-z-through-p (n x y z)
  (declare (xargs :measure (nfix z)))
  (if (and (integerp n)
           (posp x)
           (posp y)
           (natp z))
      (or
       (and
        (posp z)
        (equal n
               (+ (* x y)
                  (* x z)
                  (* y z)
                  1)))
       (and
        (not (zp z))
        (putnam-1988-b1-positive-z-through-p
         n x y (- z 1))))
    nil))

(defun putnam-1988-b1-positive-yz-through-p (n x y)
  (declare (xargs :measure (nfix y)))
  (if (and (integerp n)
           (posp x)
           (natp y))
      (or
       (and
        (posp y)
        (putnam-1988-b1-positive-z-through-p n x y n))
       (and
        (not (zp y))
        (putnam-1988-b1-positive-yz-through-p
         n x (- y 1))))
    nil))

(defun putnam-1988-b1-positive-xyz-through-p (n x)
  (declare (xargs :measure (nfix x)))
  (if (and (integerp n)
           (natp x))
      (or
       (and
        (posp x)
        (putnam-1988-b1-positive-yz-through-p n x n))
       (and
        (not (zp x))
        (putnam-1988-b1-positive-xyz-through-p
         n (- x 1))))
    nil))

(defun putnambench-putnam-1988-b1-statement (a b)
  (implies
   (and
    (integerp a)
    (integerp b)
    (<= 2 a)
    (<= 2 b))
   (putnam-1988-b1-positive-xyz-through-p
    (* a b)
    (* a b))))

(value-triple :itpeval-statement-checked)
:q
