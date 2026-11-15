;; Statement-only formalization of PutnamBench corpus artifact putnam_2003_b3:
;; the factorial of a natural number equals the product, over i from 1 to n,
;; of the least common multiple of 1 through floor(n/i). This file contains
;; no proof.

(in-package "ACL2")

(defun putnam-2003-b3-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (putnam-2003-b3-factorial (- n 1)))))

(defun putnam-2003-b3-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (cond
   ((zp a) (nfix b))
   ((zp b) (nfix a))
   ((< a b)
    (putnam-2003-b3-gcd a (- b a)))
   (t
    (putnam-2003-b3-gcd (- a b) b))))

(defun putnam-2003-b3-lcm (a b)
  (if (or (zp a) (zp b))
      0
    (floor (* a b)
           (putnam-2003-b3-gcd a b))))

;; This is lcm{1,...,k}, with the empty lcm equal to 1.
(defun putnam-2003-b3-initial-lcm (k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      1
    (putnam-2003-b3-lcm
     k
     (putnam-2003-b3-initial-lcm (- k 1)))))

;; This is the product from i=1 through i=remaining of
;; lcm{1,...,floor(n/i)}.
(defun putnam-2003-b3-lcm-product (n remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      1
    (*
     (putnam-2003-b3-initial-lcm
      (floor n remaining))
     (putnam-2003-b3-lcm-product
      n (- remaining 1)))))

(defun putnambench-putnam-2003-b3-statement (n)
  (implies
   (natp n)
   (equal
    (putnam-2003-b3-factorial n)
    (putnam-2003-b3-lcm-product n n))))

(value-triple :itpeval-statement-checked)
:q
