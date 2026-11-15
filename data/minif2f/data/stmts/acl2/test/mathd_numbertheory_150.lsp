;; Statement-only formalization of miniF2F artifact mathd_numbertheory_150:
;; every natural n for which 7 + 30*n is nonprime satisfies 6 <= n. This file
;; contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-150-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (mathd-numbertheory-150-no-divisor-from-p n (+ d 1)))
    t))

(defun mathd-numbertheory-150-primep (n)
  (and (natp n)
       (< 1 n)
       (mathd-numbertheory-150-no-divisor-from-p n 2)))

(defun mathd-numbertheory-150-statement (n)
  (implies
   (and (natp n)
        (not (mathd-numbertheory-150-primep
              (+ 7 (* 30 n)))))
   (<= 6 n)))

(value-triple :itpeval-statement-checked)
:q
