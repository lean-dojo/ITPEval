;; Statement-only formalization of PutnamBench corpus artifact putnam_2018_a1:
;; the positive integer solutions of 1/a + 1/b = 3/2018 are exactly the six
;; specified ordered pairs. This file contains no proof.

(in-package "ACL2")

(defun putnam-2018-a1-solution-p (a b)
  (or
   (and (equal a 673)
        (equal b 1358114))
   (and (equal a 674)
        (equal b 340033))
   (and (equal a 1009)
        (equal b 2018))
   (and (equal a 2018)
        (equal b 1009))
   (and (equal a 340033)
        (equal b 674))
   (and (equal a 1358114)
        (equal b 673))))

;; ACL2 universally closes A and B. POSP is exactly the positive-integer
;; domain, and ACL2 division computes the exact rational equation.
(defun putnambench-putnam-2018-a1-statement (a b)
  (iff
   (and
    (posp a)
    (posp b)
    (equal
     (+ (/ 1 a) (/ 1 b))
     (/ 3 2018)))
   (putnam-2018-a1-solution-p a b)))

(value-triple :itpeval-statement-checked)
:q
