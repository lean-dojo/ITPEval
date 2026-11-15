;; Statement-only formalization of PutnamBench corpus artifact putnam_1992_a3:
;; for each positive natural m, the positive natural solutions (n,x,y) of
;; (x^2+y^2)^m = (x*y)^n with n coprime to m are classified exactly.
;; This file contains no proof.

(in-package "ACL2")

(defun putnam-1992-a3-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond
       ((equal a 0) b)
       ((equal b 0) a)
       ((< a b)
        (putnam-1992-a3-gcd a (- b a)))
       (t
        (putnam-1992-a3-gcd (- a b) b)))
    0))

(defun putnam-1992-a3-source-condition-p (m n x y)
  (and
   (posp n)
   (posp x)
   (posp y)
   (equal (putnam-1992-a3-gcd n m) 1)
   (equal
    (expt (+ (expt x 2)
             (expt y 2))
          m)
    (expt (* x y) n))))

;; In the source existential, m = 2*r uniquely determines the natural
;; witness r. Under the natural-domain hypothesis, r = floor(m/2), so this
;; definition is bidirectionally equivalent without exposing that witness as
;; an additional statement parameter.
(defun putnam-1992-a3-solution-p (m n x y)
  (let ((r (floor m 2)))
    (and
     (equal m (* 2 r))
     (equal x (expt 2 r))
     (equal y (expt 2 r))
     (equal n (+ (* 2 r) 1)))))

(defun putnambench-putnam-1992-a3-statement (m n x y)
  (implies
   (and
    (natp m)
    (natp n)
    (natp x)
    (natp y)
    (< 0 m))
   (iff
    (putnam-1992-a3-solution-p m n x y)
    (putnam-1992-a3-source-condition-p m n x y))))

(value-triple :itpeval-statement-checked)
:q
