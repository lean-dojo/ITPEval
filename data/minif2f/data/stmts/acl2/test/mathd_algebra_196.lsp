;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_196:
;; the finite set of real solutions to |2 - x| = 3 has element sum 4. This
;; file contains no proof.
;;
;; A duplicate-free rational list represents the finite set. Requiring every
;; listed value to satisfy the equation and requiring both -1 and 5 to occur
;; is bidirectionally equivalent to the source membership characterization:
;; over the reals, |2 - x| = 3 holds exactly when x is -1 or 5. Hence every
;; element of the source set is rational, so this exact representation does
;; not narrow the source real domain.

(in-package "ACL2")

(defun mathd-algebra-196-solution-list-p (values)
  (if (consp values)
      (and (rationalp (car values))
           (equal (abs (- 2 (car values))) 3)
           (mathd-algebra-196-solution-list-p (cdr values)))
    (equal values nil)))

(defun mathd-algebra-196-sum (values)
  (if (consp values)
      (+ (car values)
         (mathd-algebra-196-sum (cdr values)))
    0))

(defun mathd-algebra-196-statement (s)
  (implies
   (and (mathd-algebra-196-solution-list-p s)
        (no-duplicatesp-equal s)
        (member-equal -1 s)
        (member-equal 5 s))
   (equal (mathd-algebra-196-sum s) 4)))

(value-triple :itpeval-statement-checked)
:q
