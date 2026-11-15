;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_prmdvsneqnsqmodpeq0: for every integer n and natural prime p,
;; p divides n if and only if n squared has remainder zero modulo p. This
;; file contains no proof.

(in-package "ACL2")

(defun numbertheory-prmdvsneqnsqmodpeq0-no-divisor-from-p
    (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and
       (not (equal (mod number divisor) 0))
       (numbertheory-prmdvsneqnsqmodpeq0-no-divisor-from-p
        number
        (+ divisor 1)))
    t))

(defun numbertheory-prmdvsneqnsqmodpeq0-primep (number)
  (and (natp number)
       (< 1 number)
       (numbertheory-prmdvsneqnsqmodpeq0-no-divisor-from-p number 2)))

(defun numbertheory-prmdvsneqnsqmodpeq0-statement (n p)
  (implies
   (and (integerp n)
        (natp p)
        (numbertheory-prmdvsneqnsqmodpeq0-primep p))
   (iff (equal (mod n p) 0)
        (equal (mod (expt n 2) p) 0))))

(value-triple :itpeval-statement-checked)
:q
