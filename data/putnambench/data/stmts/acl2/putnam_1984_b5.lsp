;; Statement-only formalization of PutnamBench corpus artifact putnam_1984_b5:
;; the alternating sum of mth powers weighted by binary one-count parity is
;; (-1)^m times 2^(m*(m-1)/2) times m!. This file contains no proof.

(in-package "ACL2")

;; The fuel starts at n. Repeated division by two reaches zero in at most n
;; steps, so on natural inputs this is exactly the source recurrence for d.
(defun putnam-1984-b5-binary-one-count-aux (n fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp n)
          (zp fuel))
      0
    (if (< n 2)
        n
      (+ (mod n 2)
         (putnam-1984-b5-binary-one-count-aux
          (floor n 2)
          (- fuel 1))))))

(defun putnam-1984-b5-binary-one-count (n)
  (putnam-1984-b5-binary-one-count-aux
   (nfix n)
   (nfix n)))

;; Sum the terms with indices k = 0,...,term-count-1.
(defun putnam-1984-b5-alternating-power-sum (m term-count)
  (declare (xargs :measure (nfix term-count)))
  (if (zp term-count)
      0
    (let ((k (- term-count 1)))
      (+ (putnam-1984-b5-alternating-power-sum
          m k)
         (* (expt -1
                   (putnam-1984-b5-binary-one-count k))
            (expt k m))))))

(defun putnam-1984-b5-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1984-b5-factorial (- n 1)))))

;; These are the evaluations of the source solution
;; (2, X*(X-1)/2, X) at m.
(defun putnam-1984-b5-solution-base ()
  2)

(defun putnam-1984-b5-solution-exponent (m)
  (floor (* m (- m 1)) 2))

(defun putnam-1984-b5-solution-factorial-argument (m)
  m)

(defun putnambench-putnam-1984-b5-statement (m)
  (implies
   (posp m)
   (equal
    (putnam-1984-b5-alternating-power-sum
     m (expt 2 m))
    (* (expt -1 m)
       (expt (putnam-1984-b5-solution-base)
             (putnam-1984-b5-solution-exponent m))
       (putnam-1984-b5-factorial
        (putnam-1984-b5-solution-factorial-argument m))))))

(value-triple :itpeval-statement-checked)
:q
