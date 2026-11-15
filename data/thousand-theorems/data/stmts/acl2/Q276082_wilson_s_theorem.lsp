;; Statement-only formalization of thousand-theorems corpus artifact Q276082,
;; "Wilson's theorem": for every prime natural number p, (p - 1)! is congruent
;; to -1 modulo p. This file contains no proof.

(in-package "ACL2")

(defun q276082-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and
       (not (equal (mod number divisor) 0))
       (q276082-no-divisor-from-p number (+ divisor 1)))
    t))

(defun q276082-primep (number)
  (and (natp number)
       (< 1 number)
       (q276082-no-divisor-from-p number 2)))

(defun q276082-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (q276082-factorial (- n 1)))))

(defun thousand-theorems-q276082-wilson-s-theorem-statement (p)
  (implies
   (q276082-primep p)
   (equal (mod (q276082-factorial (- p 1)) p)
          (mod -1 p))))

(value-triple :itpeval-statement-checked)
:q
