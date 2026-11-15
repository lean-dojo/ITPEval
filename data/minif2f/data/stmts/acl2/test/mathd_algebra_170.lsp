;; Statement-only formalization of miniF2F artifact mathd_algebra_170: the
;; finite set of integers n satisfying |n - 2| <= 5 + 6/10 has cardinality
;; 11. ACL2 represents the finite set as a duplicate-free integer list and
;; checks both directions of membership on the exhaustive range -3 through 7.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-170-integer-listp (values)
  (if (consp values)
      (and (integerp (car values))
           (mathd-algebra-170-integer-listp (cdr values)))
    (equal values nil)))

(defun mathd-algebra-170-member-condition-p (n)
  (and (integerp n)
       (<= (abs (- n 2))
           (+ 5 (/ 6 10)))))

(defun mathd-algebra-170-all-members-valid-p (values)
  (if (consp values)
      (and (mathd-algebra-170-member-condition-p (car values))
           (mathd-algebra-170-all-members-valid-p (cdr values)))
    (equal values nil)))

(defun mathd-algebra-170-required-members-present-p (candidates values)
  (if (consp candidates)
      (and
       (or (not (mathd-algebra-170-member-condition-p (car candidates)))
           (member-equal (car candidates) values))
       (mathd-algebra-170-required-members-present-p
        (cdr candidates)
        values))
    (equal candidates nil)))

(defun mathd-algebra-170-statement (s)
  (implies
   (and
    (mathd-algebra-170-integer-listp s)
    (no-duplicatesp-equal s)
    (mathd-algebra-170-all-members-valid-p s)
    (mathd-algebra-170-required-members-present-p
     (list -3 -2 -1 0 1 2 3 4 5 6 7)
     s))
   (equal (len s) 11)))

(value-triple :itpeval-statement-checked)
:q
