;; Statement-only formalization of thousand-theorems corpus artifact Q914517,
;; "Fermat's theorem on sums of two squares": every natural prime not
;; congruent to 3 modulo 4 is a sum of two natural-number squares. The
;; existential witnesses are unbounded ACL2 quantifiers. This file contains
;; no proof.

(in-package "ACL2")

(defun q914517-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (q914517-no-divisor-from-p n (+ d 1)))
    t))

(defun q914517-primep (n)
  (and (natp n)
       (< 1 n)
       (q914517-no-divisor-from-p n 2)))

(defun-sk q914517-sum-of-two-squares-p (p)
  (exists (a b)
    (and (natp a)
         (natp b)
         (equal (+ (* a a) (* b b))
                p))))

(defun thousand-theorems-q914517-fermat-s-theorem-on-sums-of-two-squares-statement
    (p)
  (implies
   (and (q914517-primep p)
        (not (equal (mod p 4) 3)))
   (q914517-sum-of-two-squares-p p)))

(value-triple :itpeval-statement-checked)
:q
