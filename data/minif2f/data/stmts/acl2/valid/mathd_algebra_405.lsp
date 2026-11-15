;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_405:
;; the finite set of positive natural numbers whose square plus four times
;; the number plus four is less than 20 has cardinality 2. ACL2 represents
;; that set extensionally as a duplicate-free list. This file contains no
;; proof.

(in-package "ACL2")

(defun mathd-algebra-405-solution-p (x)
  (and (natp x)
       (< 0 x)
       (< (+ (expt x 2)
             (* 4 x)
             4)
          20)))

(defun-sk mathd-algebra-405-complete-set-p (solutions)
  (forall (x)
    (iff (member-equal x solutions)
         (mathd-algebra-405-solution-p x))))

(defun mathd-algebra-405-statement (solutions)
  (implies
   (and (true-listp solutions)
        (no-duplicatesp-equal solutions)
        (mathd-algebra-405-complete-set-p solutions))
   (equal (len solutions) 2)))

(value-triple :itpeval-statement-checked)
:q
