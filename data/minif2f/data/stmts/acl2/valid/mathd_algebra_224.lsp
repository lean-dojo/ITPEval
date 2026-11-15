;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_224:
;; the set of natural numbers whose principal real square roots lie strictly
;; between 2 and 7/2 has cardinality eight. This file contains no proof.

(in-package "ACL2")

;; For natural n, 2 < sqrt(n) < 7/2 is equivalent, by nonnegativity and
;; squaring, to 4 < n and 4*n < 49.
(defun mathd-algebra-224-solution-p (n)
  (and (natp n)
       (< 4 n)
       (< (* 4 n) 49)))

(defun mathd-algebra-224-count-solutions-through (limit)
  (declare (xargs :measure (nfix limit)))
  (if (zp limit)
      0
    (+ (if (mathd-algebra-224-solution-p limit) 1 0)
       (mathd-algebra-224-count-solutions-through (- limit 1)))))

;; The inequality 4*n < 49 makes every solution at most 12. Stabilization for
;; every natural cutoff from 13 onward therefore states the cardinality over
;; all natural numbers.
(defun mathd-algebra-224-statement (m)
  (implies
   (and (natp m)
        (<= 13 m))
   (equal (mathd-algebra-224-count-solutions-through m)
          8)))

(value-triple :itpeval-statement-checked)
:q
