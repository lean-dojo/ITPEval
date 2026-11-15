;; Statement-only formalization of PutnamBench corpus artifact putnam_1974_a3:
;; primes represented by x^2 + 16*y^2 and by 4*x^2 + 4*x*y + 5*y^2 are
;; classified by their residue modulo 8. This file contains no proof.

(in-package "ACL2")

(defun putnam-1974-a3-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and
       (not (equal (mod n d) 0))
       (putnam-1974-a3-no-divisor-from-p n (+ d 1)))
    t))

(defun putnam-1974-a3-primep (n)
  (and
   (natp n)
   (< 1 n)
   (putnam-1974-a3-no-divisor-from-p n 2)))

;; These predicates retain the source's unrestricted integer witnesses.
(defun-sk putnam-1974-a3-sum-two-squares-p (p)
  (exists (m n)
    (and
     (integerp m)
     (integerp n)
     (equal p
            (+ (* m m)
               (* n n))))))

(defun-sk putnam-1974-a3-form-a-representable-p (p)
  (exists (x y)
    (and
     (integerp x)
     (integerp y)
     (equal p
            (+ (* x x)
               (* 16 y y))))))

(defun-sk putnam-1974-a3-form-b-representable-p (p)
  (exists (x y)
    (and
     (integerp x)
     (integerp y)
     (equal p
            (+ (* 4 x x)
               (* 4 x y)
               (* 5 y y))))))

;; This is the supplied sum-of-two-squares theorem, universally quantified
;; over the same natural-number domain as in the source.
(defun-sk putnam-1974-a3-sum-two-squares-assumption-p ()
  (forall (p)
    (implies
     (natp p)
     (implies
      (and
       (putnam-1974-a3-primep p)
       (< 2 p))
      (iff
       (putnam-1974-a3-sum-two-squares-p p)
       (equal (mod p 4) 1))))))

(defun putnam-1974-a3-first-solution-set-p (p)
  (and
   (putnam-1974-a3-primep p)
   (equal (mod p 8) 1)))

(defun putnam-1974-a3-second-solution-set-p (p)
  (and
   (putnam-1974-a3-primep p)
   (equal (mod p 8) 5)))

(defun-sk putnam-1974-a3-classification-p ()
  (forall (p)
    (implies
     (natp p)
     (and
      (iff
       (and
        (putnam-1974-a3-primep p)
        (< 2 p)
        (putnam-1974-a3-form-a-representable-p p))
       (putnam-1974-a3-first-solution-set-p p))
      (iff
       (and
        (putnam-1974-a3-primep p)
        (< 2 p)
        (putnam-1974-a3-form-b-representable-p p))
       (putnam-1974-a3-second-solution-set-p p))))))

(defun putnambench-putnam-1974-a3-statement ()
  (implies
   (putnam-1974-a3-sum-two-squares-assumption-p)
   (putnam-1974-a3-classification-p)))

(value-triple :itpeval-statement-checked)
:q
