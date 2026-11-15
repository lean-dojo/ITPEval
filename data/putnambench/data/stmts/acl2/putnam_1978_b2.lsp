;; Statement-only formalization of PutnamBench corpus artifact putnam_1978_b2:
;; the positive double series with summand 1/(i*j*(i+j+2)) converges to
;; 7/4. This file contains no proof.

(in-package "ACL2")

;; Exact rational sum over j = 1,...,UPPER for a fixed positive I.
(defun putnam-1978-b2-inner-sum (i upper)
  (declare (xargs :measure (nfix upper)))
  (if (zp upper)
      0
    (+ (/ 1
          (* i upper (+ i upper 2)))
       (putnam-1978-b2-inner-sum i (- upper 1)))))

;; Exact rational sum over the square 1 <= i,j <= N.
(defun putnam-1978-b2-square-sum-aux (remaining upper)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (putnam-1978-b2-inner-sum remaining upper)
       (putnam-1978-b2-square-sum-aux
        (- remaining 1) upper))))

(defun putnam-1978-b2-square-sum (n)
  (if (natp n)
      (putnam-1978-b2-square-sum-aux n n)
    0))

;; For positive terms, convergence of these square partial sums is equivalent
;; to the iterated positive double sum in the Lean and Isabelle statements and
;; is exactly the sequence of square sums used by the Rocq statement.
;; Positive rational tolerances are cofinal among positive real tolerances,
;; while every displayed partial sum remains its exact rational value.
(defun-sk putnam-1978-b2-tail-p (epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (<
      (abs
       (- (putnam-1978-b2-square-sum n)
          (/ 7 4)))
      epsilon))))

(defun-sk putnam-1978-b2-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1978-b2-tail-p epsilon cutoff))))

(defun putnambench-putnam-1978-b2-statement (epsilon)
  (implies
   (and
    (rationalp epsilon)
    (< 0 epsilon))
   (putnam-1978-b2-cutoff-exists-p epsilon)))

(value-triple :itpeval-statement-checked)
:q
