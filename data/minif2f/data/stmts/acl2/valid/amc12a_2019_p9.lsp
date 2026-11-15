;; Statement-only formalization of miniF2F corpus artifact amc12a_2019_p9:
;; the rational sequence with a(1)=1, a(2)=3/7, and the stated nonlinear
;; recurrence has reduced numerator plus denominator 8078 at index 2019.
;; This file contains no proof.
;;
;; Applying the source recurrence at n=0 shows that a(0)=-3: a zero
;; denominator would make the quotient zero, while otherwise cross
;; multiplication in the rationals gives the unique value -3. The two values
;; a(0)=-3 and a(1)=1 then determine every later term by the recurrence, and
;; the term at index 2 is 3/7. Thus every source sequence agrees with the
;; recursive sequence below, and this sequence satisfies all source
;; hypotheses, making the closed predicate bidirectionally equivalent to the
;; universally quantified source implication. ACL2's numerator and
;; denominator return the canonical reduced rational components.

(in-package "ACL2")

(defun amc12a-2019-p9-sequence-aux (steps earlier later)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      later
    (amc12a-2019-p9-sequence-aux
     (- steps 1)
     later
     (/ (* earlier later)
        (- (* 2 earlier) later)))))

(defun amc12a-2019-p9-sequence (n)
  (cond ((not (natp n)) 0)
        ((equal n 0) -3)
        (t (amc12a-2019-p9-sequence-aux
            (- n 1) -3 1))))

(defun amc12a-2019-p9-statement ()
  (let ((term (amc12a-2019-p9-sequence 2019)))
    (equal (+ (denominator term)
              (numerator term))
           8078)))

(value-triple :itpeval-statement-checked)
:q
