;; Statement-only formalization of PutnamBench corpus artifact putnam_1980_b6:
;; the reduced denominator of the recursively defined rational G(d,p) is not
;; divisible by the prime p when 1 < d <= p. This file contains no proof.

(in-package "ACL2")

;; E(K,M) is the K-th elementary symmetric sum of 1, 1/2, ..., 1/M.
;; Splitting subsets according to whether they contain M gives its exact
;; recursion below.
(defun putnam-1980-b6-elementary-symmetric (k m)
  (declare (xargs :measure (+ (nfix k) (nfix m))))
  (cond
   ((not (and (natp k) (natp m))) 0)
   ((zp k) 1)
   ((zp m) 0)
   (t
    (+ (putnam-1980-b6-elementary-symmetric k (- m 1))
       (* (/ 1 m)
          (putnam-1980-b6-elementary-symmetric
           (- k 1) (- m 1)))))))

(defun putnam-1980-b6-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (or (not (natp n)) (zp n))
      1
    (* n (putnam-1980-b6-factorial (- n 1)))))

;; The source recurrence uniquely determines every value used in its
;; conclusion. Its solution on 1 <= D <= N is
;;
;;   G(D,N) = D! / N * E(D-1,N-1).
;;
;; Indeed the D=1 case is 1/N. For D>1, substituting the formula for D-1
;; makes the source sum telescope via
;;
;;   E(K,M) - E(K,M-1) = E(K-1,M-1)/M.
;;
;; Conversely induction on D in the source recurrence gives this formula,
;; so eliminating the external G and its recurrence hypothesis is
;; bidirectionally equivalent. Values at other integer pairs are irrelevant
;; and may be extended arbitrarily.
(defun putnam-1980-b6-g (d n)
  (if (and (natp d)
           (natp n)
           (< 0 d)
           (<= d n))
      (* (/ (putnam-1980-b6-factorial d) n)
         (putnam-1980-b6-elementary-symmetric
          (- d 1) (- n 1)))
    0))

(defun putnam-1980-b6-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and
       (not (equal (mod n d) 0))
       (putnam-1980-b6-no-divisor-from-p n (+ d 1)))
    t))

(defun putnam-1980-b6-primep (n)
  (and (natp n)
       (< 1 n)
       (putnam-1980-b6-no-divisor-from-p n 2)))

(defun putnambench-putnam-1980-b6-statement (d p)
  (implies
   (and
    (natp d)
    (natp p)
    (< 1 d)
    (<= d p)
    (putnam-1980-b6-primep p))
   (not
    (equal
     (mod
      (denominator (putnam-1980-b6-g d p))
      p)
     0))))

(value-triple :itpeval-statement-checked)
:q
