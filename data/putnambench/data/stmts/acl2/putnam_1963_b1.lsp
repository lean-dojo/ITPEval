;; Statement-only formalization of PutnamBench artifact putnam_1963_b1:
;; the integer a for which x^2 - x + a divides x^13 + x + 90.
;; This file contains no proof.

(in-package "ACL2")

;; Modulo x^2 - x + a, the relation x^2 = x - a reduces every power
;; x^n to a unique linear remainder u*x + v. If x^(n-1) has remainder
;; u*x + v, multiplication by x gives (u+v)*x - a*u.
;;
;; Since the divisor is monic, polynomial division over the integers has an
;; integer-coefficient quotient and a unique remainder of degree below two.
;; Thus divisibility in Z[x] is equivalent to both remainder coefficients
;; being zero. The same zero-remainder condition is equivalent to divisibility
;; after embedding the coefficients into any real field, matching all three
;; ground-truth formulations.

(defun putnam-1963-b1-power-remainder (n a)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons 0 1)
    (let* ((previous
            (putnam-1963-b1-power-remainder (- n 1) a))
           (u (car previous))
           (v (cdr previous)))
      (cons (+ u v)
            (- (* a u))))))

(defun putnam-1963-b1-divides-p (a)
  (let* ((power-remainder
          (putnam-1963-b1-power-remainder 13 a))
         (linear-coefficient (+ (car power-remainder) 1))
         (constant-coefficient (+ (cdr power-remainder) 90)))
    (and (equal linear-coefficient 0)
         (equal constant-coefficient 0))))

(defun putnambench-putnam-1963-b1-statement (a)
  (implies
   (integerp a)
   (equal (putnam-1963-b1-divides-p a)
          (equal a 2))))

(value-triple :itpeval-statement-checked)
:q
