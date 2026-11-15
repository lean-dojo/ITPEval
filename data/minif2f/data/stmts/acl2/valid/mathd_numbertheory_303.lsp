;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_303: the natural numbers at least two satisfying
;; 171 congruent to 80 and 468 congruent to 13 modulo n sum to 111.
;; This file contains no proof.
;;
;; The source hypothesis uniquely determines its finite set or duplicate-free
;; list, so summing the solution predicate is definitionally equivalent to
;; quantifying over that container. For n > 171, the first congruence fails
;; because 171 mod n = 171 and 80 mod n = 80. Thus checking through 171
;; preserves the source's full natural-number domain.

(in-package "ACL2")

(defun mathd-numbertheory-303-solution-p (n)
  (and (natp n)
       (<= 2 n)
       (equal (mod 171 n) (mod 80 n))
       (equal (mod 468 n) (mod 13 n))))

(defun mathd-numbertheory-303-sum-solutions-through (limit)
  (declare (xargs :measure (nfix limit)))
  (if (zp limit)
      0
    (+ (if (mathd-numbertheory-303-solution-p limit)
           limit
         0)
       (mathd-numbertheory-303-sum-solutions-through
        (- limit 1)))))

(defun mathd-numbertheory-303-statement ()
  (equal (mathd-numbertheory-303-sum-solutions-through 171)
         111))

(value-triple :itpeval-statement-checked)
:q
