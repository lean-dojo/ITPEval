;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_690:
;; 314 is the least positive natural number congruent to 2 modulo 3, 4 modulo
;; 5, 6 modulo 7, and 8 modulo 9. This file contains no proof.
;;
;; The recursive predicate checks every natural below 314, exactly encoding
;; the source assertion that every positive natural satisfying the four
;; congruences is at least 314.

(in-package "ACL2")

(defun mathd-numbertheory-690-solution-p (n)
  (and (natp n)
       (< 0 n)
       (equal (mod n 3) 2)
       (equal (mod n 5) 4)
       (equal (mod n 7) 6)
       (equal (mod n 9) 8)))

(defun mathd-numbertheory-690-no-solution-below-p (limit)
  (declare (xargs :measure (nfix limit)))
  (if (zp limit)
      t
    (let ((candidate (- limit 1)))
      (and
       (not (mathd-numbertheory-690-solution-p candidate))
       (mathd-numbertheory-690-no-solution-below-p candidate)))))

(defun mathd-numbertheory-690-statement ()
  (and
   (mathd-numbertheory-690-solution-p 314)
   (mathd-numbertheory-690-no-solution-below-p 314)))

(value-triple :itpeval-statement-checked)
:q
