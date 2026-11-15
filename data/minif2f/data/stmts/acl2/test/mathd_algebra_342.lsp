;; Statement-only formalization of miniF2F corpus artifact
;; mathd_algebra_342: two finite sums of a real arithmetic progression imply
;; that its initial term is 42/5. This file contains no proof.
;;
;; ACL2 exact rational arithmetic is bidirectionally equivalent here. The
;; hypotheses expand to 5*a + 10*d = 70 and 10*a + 45*d = 210, which force
;; d = 14/5 and a = 42/5. Thus every real solution is rational, while every
;; rational solution embeds into the reals with the same sums and conclusion.

(in-package "ACL2")

(defun mathd-algebra-342-progression-sum-below (a d n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (let ((k (- n 1)))
      (+ (mathd-algebra-342-progression-sum-below a d k)
         (+ a (* k d))))))

(defun mathd-algebra-342-statement (a d)
  (implies
   (and (rationalp a)
        (rationalp d)
        (equal (mathd-algebra-342-progression-sum-below a d 5) 70)
        (equal (mathd-algebra-342-progression-sum-below a d 10) 210))
   (equal a (/ 42 5))))

(value-triple :itpeval-statement-checked)
:q
