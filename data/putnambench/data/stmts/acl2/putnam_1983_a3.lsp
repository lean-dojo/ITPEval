;; Statement-only formalization of PutnamBench corpus artifact putnam_1983_a3:
;; for every odd prime p, the polynomial
;; F(n) = 1 + 2*n + 3*n^2 + ... + (p-1)*n^(p-2) takes incongruent values
;; modulo p at distinct residues. This file contains no proof.

(in-package "ACL2")

(defun putnam-1983-a3-no-divisor-through-p (p candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod p candidate) 0))
     (putnam-1983-a3-no-divisor-through-p
      p (- candidate 1)))))

(defun putnam-1983-a3-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (putnam-1983-a3-no-divisor-through-p
    p (- p 1))))

;; With TERMS = p-1, the descending recursion sums exactly the exponents
;; 0,...,p-2 in the source definition of F.
(defun putnam-1983-a3-polynomial-sum (n terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- terms 1)))
      (+ (* terms (expt n index))
         (putnam-1983-a3-polynomial-sum
          n index)))))

(defun putnam-1983-a3-polynomial (p n)
  (if (natp p)
      (putnam-1983-a3-polynomial-sum
       n (- p 1))
    0))

;; The ground truths use the complete residue systems {0,...,p-1} and
;; {1,...,p}. This predicate uses the former; replacing residue 0 by p leaves
;; every integer-coefficient polynomial value unchanged modulo p.
(defun putnambench-putnam-1983-a3-statement (p a b)
  (implies
   (and
    (putnam-1983-a3-prime-p p)
    (equal (mod p 2) 1)
    (natp a)
    (< a p)
    (natp b)
    (< b p)
    (not (equal a b)))
   (not
    (equal
     (mod (putnam-1983-a3-polynomial p a) p)
     (mod (putnam-1983-a3-polynomial p b) p)))))

(value-triple :itpeval-statement-checked)
:q
