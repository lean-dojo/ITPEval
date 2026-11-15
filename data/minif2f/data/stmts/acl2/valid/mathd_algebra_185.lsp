;; Statement-only formalization of miniF2F artifact mathd_algebra_185: the
;; finite set of integers x satisfying |x + 4| < 9 has cardinality 17.
;; ACL2 represents the set as a duplicate-free integer list and states its
;; extensional equality with the predicate over every ACL2 object. This file
;; contains no proof.

(in-package "ACL2")

(defun mathd-algebra-185-integer-listp (values)
  (if (consp values)
      (and (integerp (car values))
           (mathd-algebra-185-integer-listp (cdr values)))
    (equal values nil)))

(defun mathd-algebra-185-member-condition-p (x)
  (and (integerp x)
       (< (abs (+ x 4)) 9)))

(defun-sk mathd-algebra-185-complete-set-p (values)
  (forall (x)
    (iff (member-equal x values)
         (mathd-algebra-185-member-condition-p x))))

(defun mathd-algebra-185-statement (s)
  (implies
   (and
    (mathd-algebra-185-integer-listp s)
    (no-duplicatesp-equal s)
    (mathd-algebra-185-complete-set-p s))
   (equal (len s) 17)))

(value-triple :itpeval-statement-checked)
:q
