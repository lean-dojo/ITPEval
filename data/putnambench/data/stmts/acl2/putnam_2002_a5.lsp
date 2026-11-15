;; Statement-only formalization of PutnamBench corpus artifact putnam_2002_a5:
;; every positive rational occurs as a consecutive-term ratio in any rational
;; sequence satisfying the stated Stern recurrence. This file contains no
;; proof.

(in-package "ACL2")

;; DEFSTUB supplies the arbitrary source sequence a : N -> Q.  The predicates
;; below state its codomain and recurrence explicitly; no particular sequence
;; or witness is built into the formalization.
(defstub putnam-2002-a5-a (n) t)

(defun-sk putnam-2002-a5-rational-valued-p ()
  (forall
   (n)
   (implies
    (natp n)
    (rationalp (putnam-2002-a5-a n)))))

(defun-sk putnam-2002-a5-recurrence-p ()
  (forall
   (n)
   (implies
    (natp n)
    (and
     (equal
      (putnam-2002-a5-a (+ (* 2 n) 1))
      (putnam-2002-a5-a n))
     (equal
      (putnam-2002-a5-a (+ (* 2 n) 2))
      (+ (putnam-2002-a5-a n)
         (putnam-2002-a5-a (+ n 1))))))))

(defun putnam-2002-a5-valid-sequence-p ()
  (and
   (putnam-2002-a5-rational-valued-p)
   (equal (putnam-2002-a5-a 0) 1)
   (putnam-2002-a5-recurrence-p)))

;; ACL2 division is totalized, as it is for rationals in the source provers.
;; Since q is positive, an index with a zero denominator cannot satisfy the
;; displayed equality and therefore needs no separate side condition.
(defun-sk putnam-2002-a5-witness-exists-p (q)
  (exists
   (n)
   (and
    (natp n)
    (<= 1 n)
    (equal
     q
     (/ (putnam-2002-a5-a (- n 1))
        (putnam-2002-a5-a n))))))

(defun putnambench-putnam-2002-a5-statement (q)
  (implies
   (and
    (putnam-2002-a5-valid-sequence-p)
    (rationalp q)
    (< 0 q))
   (putnam-2002-a5-witness-exists-p q)))

(value-triple :itpeval-statement-checked)

:q
