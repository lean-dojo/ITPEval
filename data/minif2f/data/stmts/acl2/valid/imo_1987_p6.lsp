;; Statement-only formalization of miniF2F corpus artifact imo_1987_p6:
;; if k^2+k+p is prime for every natural k up to floor(sqrt(p/3)), then it
;; is prime for every natural k up to p-2. This file contains no proof.
;;
;; The source function f is uniquely fixed by f(k) = k^2+k+p, so substituting
;; this polynomial is bidirectionally equivalent to quantifying over f under
;; that defining hypothesis. For natural p and k, the square-root cutoff is
;; exactly 3*k^2 <= p.

(in-package "ACL2")

(defun imo-1987-p6-polynomial (k p)
  (+ (* k k) k p))

(defun imo-1987-p6-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (imo-1987-p6-no-divisor-from-p n (+ d 1)))
    t))

(defun imo-1987-p6-primep (n)
  (and (natp n)
       (< 1 n)
       (imo-1987-p6-no-divisor-from-p n 2)))

(defun imo-1987-p6-cutoff-primes-through-p (p k)
  (declare (xargs :measure (nfix k)))
  (if (and (natp p)
           (natp k))
      (and
       (implies
        (<= (* 3 k k) p)
        (imo-1987-p6-primep
         (imo-1987-p6-polynomial k p)))
       (or
        (zp k)
        (imo-1987-p6-cutoff-primes-through-p
         p (- k 1))))
    nil))

(defun imo-1987-p6-primes-through-p (p k)
  (declare (xargs :measure (nfix k)))
  (if (and (natp p)
           (natp k))
      (and
       (imo-1987-p6-primep
        (imo-1987-p6-polynomial k p))
       (or
        (zp k)
        (imo-1987-p6-primes-through-p
         p (- k 1))))
    nil))

(defun imo-1987-p6-statement (p)
  (implies
   (and
    (natp p)
    (imo-1987-p6-cutoff-primes-through-p p p))
   (imo-1987-p6-primes-through-p
    p (nfix (- p 2)))))

(value-triple :itpeval-statement-checked)
:q
