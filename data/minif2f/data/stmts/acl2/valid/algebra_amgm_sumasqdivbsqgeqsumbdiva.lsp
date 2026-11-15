;; Statement-only formalization of miniF2F corpus artifact
;; algebra_amgm_sumasqdivbsqgeqsumbdiva: for positive real a, b, and c,
;; a^2/b^2 + b^2/c^2 + c^2/a^2 is at least b/a + c/b + a/c.
;; This file contains no proof.
;;
;; The exact-rational statement below is bidirectionally equivalent to the
;; real statement. One direction is restriction to positive rationals. For
;; the other, if the real inequality failed, its continuous difference on
;; the positive domain would remain negative at a nearby positive rational
;; triple, contradicting the rational statement.

(in-package "ACL2")

(defun algebra-amgm-sumasqdivbsqgeqsumbdiva-statement (a b c)
  (implies
   (and (rationalp a)
        (rationalp b)
        (rationalp c)
        (< 0 a)
        (< 0 b)
        (< 0 c))
   (<= (+ (+ (/ b a)
             (/ c b))
          (/ a c))
       (+ (+ (/ (expt a 2) (expt b 2))
             (/ (expt b 2) (expt c 2)))
          (/ (expt c 2) (expt a 2))))))

(value-triple :itpeval-statement-checked)
:q
