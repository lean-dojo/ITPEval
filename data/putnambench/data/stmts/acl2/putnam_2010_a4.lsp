;; Statement-only formalization of PutnamBench corpus artifact putnam_2010_a4:
;; every positive integer n makes
;; 10^(10^(10^n)) + 10^(10^n) + 10^n - 1 nonprime. This file contains no proof.

(in-package "ACL2")

;; For a natural number, checking all candidates from 2 through number-1 is
;; exactly the usual definition of primality.
(defun putnam-2010-a4-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and
       (not (equal (mod number divisor) 0))
       (putnam-2010-a4-no-divisor-from-p
        number (+ divisor 1)))
    t))

(defun putnam-2010-a4-primep (number)
  (and
   (natp number)
   (< 1 number)
   (putnam-2010-a4-no-divisor-from-p number 2)))

(defun putnam-2010-a4-number (n)
  (+ (expt 10 (expt 10 (expt 10 n)))
     (expt 10 (expt 10 n))
     (expt 10 n)
     -1))

(defun putnambench-putnam-2010-a4-statement (n)
  (implies
   (and
    (integerp n)
    (< 0 n))
   (not
    (putnam-2010-a4-primep
     (putnam-2010-a4-number n)))))

(value-triple :itpeval-statement-checked)
:q
