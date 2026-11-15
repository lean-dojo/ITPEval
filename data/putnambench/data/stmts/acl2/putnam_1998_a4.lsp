;; Statement-only formalization of PutnamBench corpus artifact putnam_1998_a4:
;; the decimal concatenation recurrence beginning with 0 and 1 is divisible
;; by 11 exactly at positive indices congruent to 1 modulo 6. This file
;; contains no proof.

(in-package "ACL2")

;; The source hypotheses uniquely determine A at every positive index, so this
;; recursive definition is equivalent to quantifying over A with those
;; hypotheses. The unconstrained source value A(0) never affects the statement.
(defun putnam-1998-a4-digits (n)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (natp n)) nil)
   ((equal n 1) (list 0))
   ((equal n 2) (list 1))
   ((< 2 n)
    (append
     (putnam-1998-a4-digits (- n 1))
     (putnam-1998-a4-digits (- n 2))))
   (t nil)))

(defun putnam-1998-a4-from-digits-aux (digits accumulator)
  (if (consp digits)
      (putnam-1998-a4-from-digits-aux
       (cdr digits)
       (+ (* 10 accumulator) (car digits)))
    accumulator))

(defun putnam-1998-a4-from-digits (digits)
  (putnam-1998-a4-from-digits-aux digits 0))

(defun putnambench-putnam-1998-a4-statement (n)
  (implies
   (natp n)
   (iff
    (and
     (<= 1 n)
     (equal
      (mod
       (putnam-1998-a4-from-digits
        (putnam-1998-a4-digits n))
       11)
      0))
    (equal (mod n 6) 1))))

(value-triple :itpeval-statement-checked)
:q
