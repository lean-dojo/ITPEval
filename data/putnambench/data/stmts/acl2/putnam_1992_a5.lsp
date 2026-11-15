;; Statement-only formalization of PutnamBench corpus artifact putnam_1992_a5:
;; the parity-of-binary-one-count sequence contains no three consecutive equal
;; blocks of the same positive length. This file contains no proof.

(in-package "ACL2")

;; Repeated division by two reads every binary digit of a natural number. The
;; fuel starts at n, so it cannot expire before the quotient reaches zero.
(defun putnam-1992-a5-binary-one-count-aux (n fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp n)
          (zp fuel))
      0
    (+ (mod n 2)
       (putnam-1992-a5-binary-one-count-aux
        (floor n 2)
        (- fuel 1)))))

(defun putnam-1992-a5-sequence-value (n)
  (mod
   (putnam-1992-a5-binary-one-count-aux
    (nfix n)
    (nfix n))
   2))

;; This checks the source equality for exactly j = 0,...,m-1.
(defun putnam-1992-a5-three-equal-blocks-p (k m remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let* ((j (- remaining 1))
           (first
            (putnam-1992-a5-sequence-value (+ k j)))
           (second
            (putnam-1992-a5-sequence-value (+ k m j)))
           (third
            (putnam-1992-a5-sequence-value
             (+ k (* 2 m) j))))
      (and
       (equal first second)
       (equal second third)
       (putnam-1992-a5-three-equal-blocks-p
        k m j)))))

;; ACL2 implicitly universally closes the formal parameters. Thus this is
;; exactly the classical equivalence
;;   not (exists positive k,m, all j<m satisfy P)
;; iff
;;   for all k,m, positive(k,m) implies not (all j<m satisfy P).
(defun putnambench-putnam-1992-a5-statement (k m)
  (implies
   (and
    (posp k)
    (posp m))
   (not
    (putnam-1992-a5-three-equal-blocks-p
     k m m))))

(value-triple :itpeval-statement-checked)
:q
