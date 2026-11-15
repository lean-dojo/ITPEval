;; Statement-only formalization of miniF2F corpus artifact imo_1967_p3:
;; for positive natural numbers k, m, and n, if k+m+1 is prime and
;; n+1 < k+m+1, then the product of c(i) for 1 <= i <= n divides the
;; product of c(m+i)-c(k), where c(s)=s(s+1). This file contains no proof.
;;
;; The source hypothesis uniquely determines c, so the definition below
;; eliminates that function quantifier without restricting the statement.
;; The shifted factors use integer subtraction exactly as in the source.
;; Since n is positive, the left product is positive, so divisibility of the
;; right product is equivalent to zero remainder.

(in-package "ACL2")

(defun imo-1967-p3-c (s)
  (* s (+ s 1)))

(defun imo-1967-p3-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and (not (equal (mod number divisor) 0))
           (imo-1967-p3-no-divisor-from-p number (+ divisor 1)))
    t))

(defun imo-1967-p3-primep (number)
  (and (natp number)
       (< 1 number)
       (imo-1967-p3-no-divisor-from-p number 2)))

(defun imo-1967-p3-base-product (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (imo-1967-p3-base-product (- n 1))
       (imo-1967-p3-c n))))

(defun imo-1967-p3-shifted-difference-product (k m n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (imo-1967-p3-shifted-difference-product k m (- n 1))
       (- (imo-1967-p3-c (+ m n))
          (imo-1967-p3-c k)))))

(defun imo-1967-p3-statement (k m n)
  (implies
   (and (natp k)
        (natp m)
        (natp n)
        (< 0 k)
        (< 0 m)
        (< 0 n)
        (imo-1967-p3-primep (+ k m 1))
        (< (+ n 1) (+ k m 1)))
   (equal
    (mod (imo-1967-p3-shifted-difference-product k m n)
         (imo-1967-p3-base-product n))
    0)))

(value-triple :itpeval-statement-checked)
:q
