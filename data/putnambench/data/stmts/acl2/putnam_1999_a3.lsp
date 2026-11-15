;; Statement-only formalization of PutnamBench corpus artifact putnam_1999_a3:
;; coefficients of 1/(1-2x-x^2) have two consecutive squares summing to
;; another coefficient. This file contains no proof.

(in-package "ACL2")

;; ACL2 has no first-class function quantifiers. A defstub is the standard
;; ACL2 representation of the source's externally supplied, otherwise
;; arbitrary coefficient sequence.

(defstub putnam-1999-a3-a (n) t)

;; Comparing coefficients in
;;
;;   (1 - 2*x - x^2) * sum(a_n*x^n) = 1
;;
;; gives a_0 = 1, a_1 = 2, and a_(k+2) = 2*a_(k+1) + a_k.
;; Conversely, this recurrence gives the source generating function in a
;; neighborhood of zero. The recurrence is therefore an exact algebraic
;; normalization of the analytic premise, but remains an explicit hypothesis
;; on the arbitrary sequence rather than a definition of one chosen sequence.

(defun putnam-1999-a3-initial-coefficients-p ()
  (and
   (equal (putnam-1999-a3-a 0) 1)
   (equal (putnam-1999-a3-a 1) 2)))

(defun-sk putnam-1999-a3-recurrence-p ()
  (forall
   (k)
   (implies
    (natp k)
    (equal
     (putnam-1999-a3-a (+ k 2))
     (+
      (* 2 (putnam-1999-a3-a (+ k 1)))
      (putnam-1999-a3-a k))))))

;; Keep the source's existential m internal. In particular, no witness search
;; or closed-form coefficient construction is built into the proposition.

(defun-sk putnam-1999-a3-conclusion-p (n)
  (exists
   (m)
   (and
    (natp m)
    (equal
     (+
      (* (putnam-1999-a3-a n)
         (putnam-1999-a3-a n))
      (* (putnam-1999-a3-a (+ n 1))
         (putnam-1999-a3-a (+ n 1))))
     (putnam-1999-a3-a m)))))

(defun putnambench-putnam-1999-a3-statement (n)
  (implies
   (and
    (natp n)
    (putnam-1999-a3-initial-coefficients-p)
    (putnam-1999-a3-recurrence-p))
   (putnam-1999-a3-conclusion-p n)))

(value-triple :itpeval-statement-checked)
:q
