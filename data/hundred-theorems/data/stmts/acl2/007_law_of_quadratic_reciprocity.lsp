;; Statement-only formalization of hundred-theorems artifact
;; 007_law_of_quadratic_reciprocity, "Law of Quadratic Reciprocity": for
;; distinct odd primes p and q, the product of the Legendre symbols (q/p) and
;; (p/q) is (-1)^(((p - 1)/2) * ((q - 1)/2)). This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-007-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (hundred-theorems-007-no-divisor-from-p n (+ d 1)))
    t))

(defun hundred-theorems-007-primep (n)
  (and (natp n)
       (< 1 n)
       (hundred-theorems-007-no-divisor-from-p n 2)))

(defun hundred-theorems-007-quadratic-residue-search-p (a p x)
  (declare (xargs :measure (nfix (- p x))))
  (if (and (natp a)
           (natp p)
           (< 0 p)
           (natp x)
           (< x p))
      (or (equal (mod (* x x) p) (mod a p))
          (hundred-theorems-007-quadratic-residue-search-p
           a p (+ x 1)))
    nil))

(defun hundred-theorems-007-legendre (p a)
  (if (and (natp p)
           (natp a)
           (< 1 p))
      (cond ((equal (mod a p) 0) 0)
            ((hundred-theorems-007-quadratic-residue-search-p a p 0) 1)
            (t -1))
    0))

(defun hundred-theorems-007-statement (p q)
  (implies
   (and (natp p)
        (natp q)
        (hundred-theorems-007-primep p)
        (hundred-theorems-007-primep q)
        (equal (mod p 2) 1)
        (equal (mod q 2) 1)
        (not (equal p q)))
   (equal
    (* (hundred-theorems-007-legendre p q)
       (hundred-theorems-007-legendre q p))
    (expt -1
          (* (floor (- p 1) 2)
             (floor (- q 1) 2))))))

(value-triple :itpeval-statement-checked)
:q
