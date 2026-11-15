;; Statement-only formalization of PutnamBench corpus artifact putnam_1974_b3:
;; a real number alpha satisfying cos(pi*alpha) = 1/3 is irrational.
;; This file contains no proof.

(in-package "ACL2")

;; The source statement is equivalent to the nonexistence of a rational
;; alpha with cos(pi*alpha)=1/3.  If alpha=p/q with q>0, the Chebyshev identity
;; gives T_q(1/3)=cos(p*pi), hence T_q(1/3) is 1 or -1.  Conversely, if
;; T_q(1/3) is 1 or -1, then q*arccos(1/3) is an integral multiple of pi,
;; producing a rational alpha with the source cosine value.  Thus it is
;; equivalent to require T_q(1/3) != +/-1 for every positive integer q.
;;
;; The integer S_q=3^q*T_q(1/3) satisfies
;; S_0=S_1=1 and S_q=2*S_(q-1)-9*S_(q-2), so comparison with +/-3^q
;; represents that condition exactly without adding a real cosine primitive.

(defun putnam-1974-b3-scaled-chebyshev (q)
  (declare (xargs :measure (nfix q)))
  (cond
   ((zp q) 1)
   ((equal q 1) 1)
   (t
    (-
     (* 2
        (putnam-1974-b3-scaled-chebyshev (- q 1)))
     (* 9
        (putnam-1974-b3-scaled-chebyshev (- q 2)))))))

(defun putnambench-putnam-1974-b3-statement (q)
  (implies
   (posp q)
   (let ((scaled-cosine
          (putnam-1974-b3-scaled-chebyshev q))
         (scale (expt 3 q)))
     (and
      (not (equal scaled-cosine scale))
      (not (equal scaled-cosine (- scale)))))))

(value-triple :itpeval-statement-checked)
:q
