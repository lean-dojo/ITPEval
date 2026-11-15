;; Statement-only formalization of PutnamBench corpus artifact putnam_2009_b1:
;; every positive rational number is a quotient of finite products of
;; factorials of primes, with repetition allowed. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A source family Fin k -> nat is represented by a proper ACL2 list of length
;; k. This is a bijective finite-sequence encoding; NIL represents k = 0 and
;; repeated list entries represent repeated primes. ACL2's rational arithmetic
;; gives the source's exact quotient, while DEFUN-SK keeps both finite families
;; existentially quantified inside the statement.

(defun putnam-2009-b1-no-proper-divisor-p (p d)
  (declare (xargs :measure (nfix d)))
  (if (zp d)
      t
    (and
     (or
      (equal d 1)
      (not (equal (mod p d) 0)))
     (putnam-2009-b1-no-proper-divisor-p p (1- d)))))

(defun putnam-2009-b1-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (putnam-2009-b1-no-proper-divisor-p p (1- p))))

(defun putnam-2009-b1-prime-list-p (values)
  (if (consp values)
      (and
       (putnam-2009-b1-prime-p (car values))
       (putnam-2009-b1-prime-list-p (cdr values)))
    (equal values nil)))

(defun putnam-2009-b1-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (putnam-2009-b1-factorial (1- n)))))

(defun putnam-2009-b1-factorial-product (values)
  (if (consp values)
      (*
       (putnam-2009-b1-factorial (car values))
       (putnam-2009-b1-factorial-product (cdr values)))
    1))

(defun-sk putnam-2009-b1-representation-exists-p (q)
  (exists (numerator-primes denominator-primes)
    (and
     (putnam-2009-b1-prime-list-p numerator-primes)
     (putnam-2009-b1-prime-list-p denominator-primes)
     (equal
      q
      (/
       (putnam-2009-b1-factorial-product numerator-primes)
       (putnam-2009-b1-factorial-product denominator-primes))))))

(defun putnambench-putnam-2009-b1-statement (q)
  (implies
   (and
    (rationalp q)
    (< 0 q))
   (putnam-2009-b1-representation-exists-p q)))

(value-triple :itpeval-statement-checked)
:q
