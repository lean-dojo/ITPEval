;; Statement-only formalization of PutnamBench corpus artifact putnam_2020_b1:
;; the binary digit-sum parity weighted cubic sum from 1 through 2020 has
;; residue 1990 modulo 2020. This file contains no proof.

(in-package "ACL2")

;; Repeated division by two reads exactly the binary digits of a natural
;; number. The fuel starts at n, which is more than enough iterations to
;; reach zero, and makes the terminating recursion explicit to ACL2.
(defun putnam-2020-b1-binary-one-count-aux (n fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp n)
          (zp fuel))
      0
    (+ (mod n 2)
       (putnam-2020-b1-binary-one-count-aux
        (floor n 2)
        (- fuel 1)))))

(defun putnam-2020-b1-binary-one-count (n)
  (putnam-2020-b1-binary-one-count-aux
   (nfix n)
   (nfix n)))

;; This is the inclusive source sum from k = 1 through UPPER.
(defun putnam-2020-b1-alternating-cubic-sum (upper)
  (declare (xargs :measure (nfix upper)))
  (if (zp upper)
      0
    (+ (putnam-2020-b1-alternating-cubic-sum
        (- upper 1))
       (* (expt -1
                 (putnam-2020-b1-binary-one-count upper))
          (expt upper 3)))))

;; The source hypotheses uniquely define both d and S, so substituting those
;; definitions here is logically equivalent to their quantified presentation.
(defun putnambench-putnam-2020-b1-statement ()
  (equal
   (mod (putnam-2020-b1-alternating-cubic-sum 2020)
        2020)
   1990))

(value-triple :itpeval-statement-checked)
:q
