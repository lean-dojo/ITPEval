;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_282:
;; a real function defined by floor on rational inputs and squared ceiling on
;; irrational inputs has the stated four-value sum 79. This file contains no
;; proof.
;;
;; The source hypotheses determine the function uniquely. ACL2 is first-order,
;; so the function is represented by the four observations used in the
;; conclusion. Every source function supplies the antecedent below. Conversely,
;; the forced observations extend to the source function defined on every real
;; x by abs(floor(x)) when x is rational and ceiling(x)^2 otherwise, so this is
;; not a finite-table restriction of the source function.
;;
;; The real cube root of 8 is 2, while 9/2 is rational. Also, pi is irrational
;; and 3 < pi < 4, so ceiling(-pi) = -3. Finally, sqrt(50) is irrational and
;; 7 < sqrt(50) < 8; the exact integer square-root computation below therefore
;; returns ceiling(sqrt(50)) = 8. These equivalences reduce the four source
;; hypothesis instances to the exact observation equalities below. Since those
;; equalities force integer values, ACL2's unrestricted observation parameters
;; omit no real-valued source instance.

(in-package "ACL2")

(defun mathd-algebra-282-floor-sqrt-down (n candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (if (<= (* candidate candidate) n)
        candidate
      (mathd-algebra-282-floor-sqrt-down
       n (- candidate 1)))))

(defun mathd-algebra-282-floor-sqrt (n)
  (mathd-algebra-282-floor-sqrt-down n n))

(defun mathd-algebra-282-ceil-sqrt (n)
  (let ((floor-root (mathd-algebra-282-floor-sqrt n)))
    (if (equal (* floor-root floor-root) n)
        floor-root
      (+ floor-root 1))))

(defun mathd-algebra-282-statement
    (f-at-cuberoot-eight
     f-at-negative-pi
     f-at-sqrt-fifty
     f-at-nine-halves)
  (implies
   (and
    (equal f-at-cuberoot-eight
           (abs (floor 2 1)))
    (equal f-at-negative-pi
           (expt -3 2))
    (equal f-at-sqrt-fifty
           (expt (mathd-algebra-282-ceil-sqrt 50) 2))
    (equal f-at-nine-halves
           (abs (floor 9 2))))
   (equal (+ f-at-cuberoot-eight
             f-at-negative-pi
             f-at-sqrt-fifty
             f-at-nine-halves)
          79)))

(value-triple :itpeval-statement-checked)
:q
