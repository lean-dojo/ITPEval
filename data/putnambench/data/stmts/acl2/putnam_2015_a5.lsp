;; Statement-only formalization of PutnamBench corpus artifact putnam_2015_a5:
;; the parity of the count of positive reduced residues below q/4 characterizes
;; odd prime powers with prime congruent to 5 or 7 modulo 8. This file contains
;; no proof.

(in-package "ACL2")

(defun putnam-2015-a5-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((zp a) b)
            ((zp b) a)
            ((< a b)
             (putnam-2015-a5-gcd a (- b a)))
            (t
             (putnam-2015-a5-gcd (- a b) b)))
    0))

;; For natural a and q, a < q/4 is equivalent to 4*a < q. Every qualifying
;; positive a is below q, so this recursion counts the source set exactly.
(defun putnam-2015-a5-coprime-count-through (q a)
  (declare (xargs :measure (nfix a)))
  (if (and (natp q) (natp a))
      (if (zp a)
          0
        (+ (if (and (< (* 4 a) q)
                    (equal (putnam-2015-a5-gcd a q) 1))
               1
             0)
           (putnam-2015-a5-coprime-count-through
            q (- a 1))))
    0))

(defun putnam-2015-a5-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (putnam-2015-a5-no-divisor-from-p n (+ d 1)))
    t))

(defun putnam-2015-a5-primep (n)
  (and (natp n)
       (< 1 n)
       (putnam-2015-a5-no-divisor-from-p n 2)))

(defun putnam-2015-a5-qualifying-prime-p (p)
  (and (putnam-2015-a5-primep p)
       (or (equal (mod p 8) 5)
           (equal (mod p 8) 7))))

(defun putnam-2015-a5-power-witness-through-k-p (q p k)
  (declare (xargs :measure (nfix k)))
  (if (and (natp q) (natp p) (natp k))
      (if (zp k)
          nil
        (or (equal q (expt p k))
            (putnam-2015-a5-power-witness-through-k-p
             q p (- k 1))))
    nil))

;; If q=p^k with p prime and k positive, then p<=q and k<=q. Searching both
;; variables through q is therefore equivalent to the source existential.
(defun putnam-2015-a5-prime-power-through-p (q p)
  (declare (xargs :measure (nfix p)))
  (if (and (natp q) (natp p))
      (if (< p 2)
          nil
        (or (and (putnam-2015-a5-qualifying-prime-p p)
                 (putnam-2015-a5-power-witness-through-k-p
                  q p q))
            (putnam-2015-a5-prime-power-through-p
             q (- p 1))))
    nil))

(defun putnambench-putnam-2015-a5-statement (q nq)
  (implies
   (and (natp q)
        (natp nq)
        (oddp q)
        (< 0 q)
        (equal nq
               (putnam-2015-a5-coprime-count-through q q)))
   (equal (oddp nq)
          (putnam-2015-a5-prime-power-through-p q q))))

(value-triple :itpeval-statement-checked)
:q
