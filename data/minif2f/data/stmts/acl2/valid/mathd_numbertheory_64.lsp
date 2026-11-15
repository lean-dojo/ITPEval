;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_64:
;; 39 is the least natural number x such that 30*x has remainder 42 modulo 47.
;; This file contains no proof.
;;
;; The recursive predicate checks every natural below 39, which is equivalent
;; to the source assertion that every natural-number solution is at least 39.

(in-package "ACL2")

(defun mathd-numbertheory-64-solution-p (x)
  (and (natp x)
       (equal (mod (* 30 x) 47) 42)))

(defun mathd-numbertheory-64-no-solution-below-p (limit)
  (declare (xargs :measure (nfix limit)))
  (if (zp limit)
      t
    (let ((candidate (- limit 1)))
      (and
       (not (mathd-numbertheory-64-solution-p candidate))
       (mathd-numbertheory-64-no-solution-below-p candidate)))))

(defun mathd-numbertheory-64-statement ()
  (and
   (mathd-numbertheory-64-solution-p 39)
   (mathd-numbertheory-64-no-solution-below-p 39)))

(value-triple :itpeval-statement-checked)
:q
