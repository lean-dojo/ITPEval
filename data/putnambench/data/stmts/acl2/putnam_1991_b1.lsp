;; Statement-only formalization of PutnamBench corpus artifact putnam_1991_b1:
;; the positive initial values whose square-remainder recurrence is eventually
;; constant are exactly the perfect squares. This file contains no proof.

(in-package "ACL2")

;; This is floor(sqrt(N)) for natural N, hence the greatest natural M with
;; M^2 <= N.
(defun putnam-1991-b1-floor-sqrt-down (n candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (if (<= (* candidate candidate) n)
        candidate
      (putnam-1991-b1-floor-sqrt-down
       n (- candidate 1)))))

(defun putnam-1991-b1-floor-sqrt (n)
  (if (natp n)
      (putnam-1991-b1-floor-sqrt-down n n)
    0))

(defun putnam-1991-b1-square-remainder (n)
  (if (natp n)
      (let ((root (putnam-1991-b1-floor-sqrt n)))
        (- n (* root root)))
    0))

;; The source assumptions uniquely determine the sequence from A, so this
;; recursion eliminates the arbitrary source functions m, S, and a
;; bidirectionally.
(defun putnam-1991-b1-sequence-value (a index)
  (declare (xargs :measure (nfix index)))
  (if (or (not (natp a))
          (not (natp index)))
      0
    (if (zp index)
        a
      (let ((previous
             (putnam-1991-b1-sequence-value
              a (- index 1))))
        (+ previous
           (putnam-1991-b1-square-remainder previous))))))

;; For a positive natural value, this is equivalent to the source solution-set
;; condition that the value is the square of a positive integer.
(defun putnam-1991-b1-perfect-square-p (value)
  (and
   (natp value)
   (let ((root (putnam-1991-b1-floor-sqrt value)))
     (equal (* root root) value))))

(defun putnam-1991-b1-fixed-step-p (a index)
  (equal
   (putnam-1991-b1-sequence-value a (+ index 1))
   (putnam-1991-b1-sequence-value a index)))

;; Because the recurrence is deterministic, it is eventually constant iff
;; some consecutive pair is equal. The first implication is the universal
;; form of "(exists K, fixed-step(A,K)) implies square(A)"; K is not an
;; external existential witness. The reverse implication uses the canonical
;; internal witness K=0, since a square has zero square remainder.
(defun putnambench-putnam-1991-b1-statement (a k)
  (implies
   (and (posp a)
        (natp k))
   (and
    (implies
     (putnam-1991-b1-fixed-step-p a k)
     (putnam-1991-b1-perfect-square-p a))
    (implies
     (putnam-1991-b1-perfect-square-p a)
     (putnam-1991-b1-fixed-step-p a 0)))))

(value-triple :itpeval-statement-checked)
:q
