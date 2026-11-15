;; Statement-only formalization of miniF2F corpus artifact aimeII_2020_p6:
;; for the rational sequence with t(1)=20, t(2)=21, and
;; t(n)=(5*t(n-1)+1)/(25*t(n-2)) for every n>=3, the reduced numerator
;; and denominator of t(2020) sum to 626. This file contains no proof.

(in-package "ACL2")

;; The source quantifies over every rational-valued function satisfying the
;; two initial values and recurrence. Those equations determine every term
;; from index 1 onward uniquely; t(0) is unconstrained and never used. The
;; transition below constructs that unique positive-index sequence, while
;; choosing the irrelevant value t(0)=0. Thus every source sequence agrees
;; with this definition at index 2020, and this definition extends to a source
;; sequence, making the closed predicate bidirectionally equivalent.
(defun aimeii-2020-p6-sequence-aux (steps earlier later)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      later
    (aimeii-2020-p6-sequence-aux
     (- steps 1)
     later
     (/ (+ (* 5 later) 1)
        (* 25 earlier)))))

(defun aimeii-2020-p6-sequence (n)
  (cond ((not (natp n)) 0)
        ((equal n 0) 0)
        ((equal n 1) 20)
        (t (aimeii-2020-p6-sequence-aux
            (- n 2) 20 21))))

(defun aimeii-2020-p6-statement ()
  (let ((term (aimeii-2020-p6-sequence 2020)))
    (equal (+ (denominator term)
              (numerator term))
           626)))

(value-triple :itpeval-statement-checked)
:q
