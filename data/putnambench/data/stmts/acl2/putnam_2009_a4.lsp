;; Statement-only formalization of PutnamBench corpus artifact putnam_2009_a4:
;; a proper set of rational numbers containing zero and closed under integer
;; shifts and the map x |-> 1/(x(x-1)). This file contains no proof.

(in-package "ACL2")

;; The source answer is False, so its biconditional is equivalent to the
;; existence of a proper set satisfying the three hypotheses. A tame unary
;; function object represents the characteristic function of that set.

(defun putnam-2009-a4-member-p (set x)
  (if (apply$ set (list x)) t nil))

(defun-sk putnam-2009-a4-closed-p (set)
  (forall (x)
    (implies
     (and
      (rationalp x)
      (putnam-2009-a4-member-p set x))
     (and
      (putnam-2009-a4-member-p set (+ x 1))
      (putnam-2009-a4-member-p set (- x 1))
      (implies
       (and
        (not (equal x 0))
        (not (equal x 1)))
       (putnam-2009-a4-member-p
        set
        (/ 1 (* x (- x 1)))))))))

(defun-sk putnam-2009-a4-proper-p (set)
  (exists (omitted)
    (and
     (rationalp omitted)
     (not (putnam-2009-a4-member-p set omitted)))))

(defun-sk putnam-2009-a4-counterexample-exists-p ()
  (exists (set)
    (and
     (tamep-functionp set)
     (putnam-2009-a4-member-p set 0)
     (putnam-2009-a4-closed-p set)
     (putnam-2009-a4-proper-p set))))

(defun putnambench-putnam-2009-a4-statement ()
  (putnam-2009-a4-counterexample-exists-p))

(value-triple :itpeval-statement-checked)
:q
