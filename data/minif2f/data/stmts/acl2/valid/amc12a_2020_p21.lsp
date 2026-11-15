;; Statement-only formalization of miniF2F corpus artifact amc12a_2020_p21:
;; the set of natural numbers divisible by 5 whose LCM with 5! equals five
;; times their GCD with 10! has cardinality 48. This file contains no proof.

(in-package "ACL2")

(defun amc12a-2020-p21-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (amc12a-2020-p21-factorial (- n 1)))))

(defun amc12a-2020-p21-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((<= a b)
             (amc12a-2020-p21-gcd a (- b a)))
            (t
             (amc12a-2020-p21-gcd (- a b) b)))
    0))

(defun amc12a-2020-p21-lcm (a b)
  (if (and (natp a) (natp b))
      (if (or (equal a 0) (equal b 0))
          0
        (/ (* a b) (amc12a-2020-p21-gcd a b)))
    0))

(defun amc12a-2020-p21-solution-p (n)
  (and (natp n)
       (equal (mod n 5) 0)
       (equal
        (amc12a-2020-p21-lcm
         (amc12a-2020-p21-factorial 5) n)
        (* 5
           (amc12a-2020-p21-gcd
            (amc12a-2020-p21-factorial 10) n)))))

(defun amc12a-2020-p21-count-solutions-through (limit)
  (declare (xargs :measure (nfix limit)))
  (if (zp limit)
      0
    (+ (if (amc12a-2020-p21-solution-p limit) 1 0)
       (amc12a-2020-p21-count-solutions-through (- limit 1)))))

;; Comparing prime exponents in the defining equation shows that every
;; solution divides 2^8 * 3^4 * 5^3 * 7 = 18144000. Stabilization beyond this
;; exact maximum keeps the quantified domain equal to all natural numbers.
(defun amc12a-2020-p21-statement (m)
  (implies
   (and (natp m)
        (<= 18144000 m))
   (equal (amc12a-2020-p21-count-solutions-through m)
          48)))

(value-triple :itpeval-statement-checked)
:q
