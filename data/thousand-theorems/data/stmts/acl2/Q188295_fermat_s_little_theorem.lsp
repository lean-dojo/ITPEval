;; Statement-only formalization of thousand-theorems corpus artifact Q188295,
;; "Fermat's little theorem": for a prime p, every nonzero residue a modulo p
;; satisfies a^(p - 1) = 1 in ZMod p. This file contains no proof.

(in-package "ACL2")

(defun q188295-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and
       (not (equal (mod number divisor) 0))
       (q188295-no-divisor-from-p number (+ divisor 1)))
    t))

(defun q188295-primep (number)
  (and (natp number)
       (< 1 number)
       (q188295-no-divisor-from-p number 2)))

(defun thousand-theorems-q188295-fermat-little-theorem-statement (p a)
  (implies
   (and (q188295-primep p)
        (natp a)
        (< a p)
        (not (equal a 0)))
   (equal (mod (expt a (- p 1)) p)
          1)))

(value-triple :itpeval-statement-checked)
:q
