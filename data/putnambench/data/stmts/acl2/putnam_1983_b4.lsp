;; Statement-only formalization of PutnamBench corpus artifact putnam_1983_b4:
;; every positive-integer sequence obtained by repeatedly adding the floor of
;; the square root of its current term contains a perfect square. This file
;; contains no proof.

(in-package "ACL2")

;; This returns floor(sqrt(N)) for natural N.
(defun putnam-1983-b4-floor-sqrt-down (n candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (if (<= (* candidate candidate) n)
        candidate
      (putnam-1983-b4-floor-sqrt-down
       n (- candidate 1)))))

(defun putnam-1983-b4-floor-sqrt (n)
  (if (natp n)
      (putnam-1983-b4-floor-sqrt-down n n)
    0))

;; The source recurrence uniquely determines the sequence from its positive
;; initial value, so this recursive function eliminates the arbitrary source
;; sequence and step function bidirectionally.
(defun putnam-1983-b4-sequence-value (m index)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      m
    (let ((previous
           (putnam-1983-b4-sequence-value
            m (- index 1))))
      (+ previous
         (putnam-1983-b4-floor-sqrt previous)))))

;; For a natural value, equality with the square of its floor square root is
;; equivalent to the source existential integer or natural square witness.
(defun putnam-1983-b4-perfect-square-p (value)
  (and
   (natp value)
   (let ((root
          (putnam-1983-b4-floor-sqrt value)))
     (equal (* root root) value))))

(defun-sk putnam-1983-b4-has-square-p (m)
  (exists (index)
    (and
     (natp index)
     (putnam-1983-b4-perfect-square-p
      (putnam-1983-b4-sequence-value m index)))))

(defun putnambench-putnam-1983-b4-statement (m)
  (implies
   (posp m)
   (putnam-1983-b4-has-square-p m)))

(value-triple :itpeval-statement-checked)
:q
