;; Statement-only formalization of miniF2F artifact mathd_algebra_215: the
;; finite set of real solutions to (x + 3)^2 = 121 has element sum -6. This
;; file contains no proof.
;;
;; A duplicate-free rational list exactly represents the source finite set.
;; This is not a domain restriction: every real solution is one of the
;; rational roots -14 and 8. Requiring both roots to occur and every list
;; element to satisfy the equation is equivalent to the source membership
;; biconditional, while exclusion of any further roots remains substantive.

(in-package "ACL2")

(defun mathd-algebra-215-solution-listp (s)
  (if (consp s)
      (and (rationalp (car s))
           (equal (expt (+ (car s) 3) 2)
                  121)
           (mathd-algebra-215-solution-listp (cdr s)))
    (equal s nil)))

(defun mathd-algebra-215-sum (s)
  (if (consp s)
      (+ (car s)
         (mathd-algebra-215-sum (cdr s)))
    0))

(defun mathd-algebra-215-statement (s)
  (implies
   (and (mathd-algebra-215-solution-listp s)
        (no-duplicatesp-equal s)
        (member-equal -14 s)
        (member-equal 8 s))
   (equal (mathd-algebra-215-sum s)
          -6)))

(value-triple :itpeval-statement-checked)
:q
