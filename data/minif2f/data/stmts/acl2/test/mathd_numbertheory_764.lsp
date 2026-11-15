;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_764: for every prime natural p at least 7, the sum
;; modulo p of 1/(k(k+1)) for k from 1 through p-2 is 2. This file contains
;; no proof.

(in-package "ACL2")

(defun mathd-numbertheory-764-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (mathd-numbertheory-764-no-divisor-from-p n (+ d 1)))
    t))

(defun mathd-numbertheory-764-primep (n)
  (and (natp n)
       (< 1 n)
       (mathd-numbertheory-764-no-divisor-from-p n 2)))

(defun mathd-numbertheory-764-inverse (k p)
  (mod (expt k (nfix (- p 2))) p))

(defun mathd-numbertheory-764-sum (k remaining p)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (* (mathd-numbertheory-764-inverse k p)
          (mathd-numbertheory-764-inverse (+ k 1) p))
       (mathd-numbertheory-764-sum
        (+ k 1)
        (- remaining 1)
        p))))

(defun mathd-numbertheory-764-statement (p)
  (implies
   (and (natp p)
        (mathd-numbertheory-764-primep p)
        (<= 7 p))
   (equal
    (mod (mathd-numbertheory-764-sum
          1
          (nfix (- p 2))
          p)
         p)
    2)))

(value-triple :itpeval-statement-checked)
:q
