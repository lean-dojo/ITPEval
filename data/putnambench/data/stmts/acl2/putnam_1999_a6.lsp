;; Statement-only formalization of PutnamBench corpus artifact putnam_1999_a6:
;; every term of a specified nonlinear real recurrence is an integer multiple
;; of its positive index. This file contains no proof.

(in-package "ACL2")

;; The hypotheses uniquely determine all positive-index terms from 1, 2, 24.
;; Since these values are rational and the recurrence uses only field
;; operations, every determined real value is the image of the exact rational
;; computed below. ACL2 division by zero is total with reciprocal zero, as in
;; the source fields, so this substitution is bidirectionally equivalent even
;; without a separate nonzero-denominator hypothesis.
(defun putnam-1999-a6-next (x y z)
  (/ (- (* 6 (* (* z z) x))
        (* 8 (* z (* y y))))
     (* y x)))

;; With X = a_i, Y = a_(i+1), and Z = a_(i+2), one step shifts the window
;; and computes a_(i+3). Starting with i = 1 makes STEPS = n-1 return a_n.
(defun putnam-1999-a6-sequence-from (steps x y z)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      x
    (putnam-1999-a6-sequence-from
     (- steps 1)
     y
     z
     (putnam-1999-a6-next x y z))))

(defun putnam-1999-a6-sequence (n)
  (if (posp n)
      (putnam-1999-a6-sequence-from (- n 1) 1 2 24)
    0))

;; For positive integer N, INTEGERP(a_N / N) holds exactly when there exists
;; an integer K with a_N = K*N; the existential witness remains internal.
(defun putnambench-putnam-1999-a6-statement (n)
  (implies
   (posp n)
   (integerp
    (/ (putnam-1999-a6-sequence n) n))))

(value-triple :itpeval-statement-checked)
:q
