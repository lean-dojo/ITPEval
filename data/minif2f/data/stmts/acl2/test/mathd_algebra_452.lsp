;; Statement-only formalization of miniF2F corpus artifact
;; mathd_algebra_452: a real arithmetic progression with first-index value
;; 2/3 and ninth-index value 4/5 has fifth-index value 11/15. This file
;; contains no proof.
;;
;; A sequence has the source constant-first-difference property exactly when
;; it has the form a(n) = a0 + n*d. Conversely, every such affine sequence
;; satisfies that recurrence, so the parameters below are a bidirectionally
;; equivalent representation of the source function and its universal
;; recurrence hypothesis. The endpoint equations force d = 1/60 and
;; a0 = 13/20; hence every satisfying real sequence has rational parameters,
;; and ACL2 exact rational arithmetic omits no source case.

(in-package "ACL2")

(defun mathd-algebra-452-term (a0 d n)
  (+ a0 (* n d)))

(defun mathd-algebra-452-statement (a0 d)
  (implies
   (and (rationalp a0)
        (rationalp d)
        (equal (mathd-algebra-452-term a0 d 1)
               (/ 2 3))
        (equal (mathd-algebra-452-term a0 d 9)
               (/ 4 5)))
   (equal (mathd-algebra-452-term a0 d 5)
          (/ 11 15))))

(value-triple :itpeval-statement-checked)
:q
