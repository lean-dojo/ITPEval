;; Statement-only formalization of thousand-theorems corpus artifact Q1506253,
;; "Euclid's theorem": for every natural number n, there exists a natural
;; prime p with n <= p. This file contains no proof.

(in-package "ACL2")

(defun q1506253-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and
       (not (equal (mod number divisor) 0))
       (q1506253-no-divisor-from-p number (+ divisor 1)))
    t))

(defun q1506253-primep (number)
  (and (natp number)
       (< 1 number)
       (q1506253-no-divisor-from-p number 2)))

(defun-sk q1506253-prime-at-least-exists-p (n)
  (exists (p)
    (and (natp p)
         (<= n p)
         (q1506253-primep p))))

(defun thousand-theorems-q1506253-euclids-theorem-statement (n)
  (implies
   (natp n)
   (q1506253-prime-at-least-exists-p n)))

(value-triple :itpeval-statement-checked)
:q
