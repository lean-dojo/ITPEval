;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_13:
;; the least and next-least positive natural numbers n satisfying
;; 14*n mod 100 = 46 have rational average 64. This file contains no proof.
;;
;; The source set is definitionally represented by the solution predicate.
;; Recursion below checks every natural below a candidate, exactly encoding
;; the two source IsLeast assumptions. The other ground truths' bounds are
;; equivalent because the solutions are precisely 39 modulo 50.

(in-package "ACL2")

(defun mathd-numbertheory-13-solution-p (n)
  (and (natp n)
       (< 0 n)
       (equal (mod (* 14 n) 100) 46)))

(defun mathd-numbertheory-13-no-solution-below-p (limit)
  (declare (xargs :measure (nfix limit)))
  (if (zp limit)
      t
    (let ((candidate (- limit 1)))
      (and
       (not (mathd-numbertheory-13-solution-p candidate))
       (mathd-numbertheory-13-no-solution-below-p candidate)))))

(defun mathd-numbertheory-13-no-other-solution-below-p
    (limit excluded)
  (declare (xargs :measure (nfix limit)))
  (if (zp limit)
      t
    (let ((candidate (- limit 1)))
      (and
       (or (equal candidate excluded)
           (not (mathd-numbertheory-13-solution-p candidate)))
       (mathd-numbertheory-13-no-other-solution-below-p
        candidate excluded)))))

(defun mathd-numbertheory-13-statement (u v)
  (implies
   (and
    (natp u)
    (natp v)
    (mathd-numbertheory-13-solution-p u)
    (mathd-numbertheory-13-no-solution-below-p u)
    (mathd-numbertheory-13-solution-p v)
    (not (equal v u))
    (mathd-numbertheory-13-no-other-solution-below-p v u))
   (equal (/ (+ u v) 2) 64)))

(value-triple :itpeval-statement-checked)
:q
