;; Statement-only formalization of PutnamBench corpus artifact putnam_1971_a5:
;; positive integer solitaire point values a > b have exactly 35 unattainable
;; accumulated scores, including 58, exactly when (a,b) = (11,8).
;; This file contains no proof.

(in-package "ACL2")

;; For positive X and Y, a representation S = M*X + N*Y has M <= S.
;; Searching M downward from S is therefore exactly the source existential
;; quantification over natural M and N; divisibility of the nonnegative
;; remainder by Y supplies N internally.
(defun putnam-1971-a5-attainable-through-m-p (s x y m)
  (declare (xargs :measure (nfix m)))
  (if (zp m)
      (equal (mod s y) 0)
    (or
     (and
      (<= (* m x) s)
      (equal (mod (- s (* m x)) y) 0))
     (putnam-1971-a5-attainable-through-m-p
      s x y (- m 1)))))

(defun putnam-1971-a5-attainable-p (s x y)
  (and
   (natp s)
   (putnam-1971-a5-attainable-through-m-p s x y s)))

(defun putnam-1971-a5-unattainable-count-below (bound x y)
  (declare (xargs :measure (nfix bound)))
  (if (zp bound)
      0
    (let ((score (- bound 1)))
      (+
       (if (putnam-1971-a5-attainable-p score x y) 0 1)
       (putnam-1971-a5-unattainable-count-below
        score x y)))))

(defun putnam-1971-a5-gcd (x y)
  (declare (xargs :measure (+ (nfix x) (nfix y))))
  (if (and (natp x) (natp y))
      (cond
       ((equal x 0) y)
       ((equal y 0) x)
       ((< x y)
        (putnam-1971-a5-gcd x (- y x)))
       (t
        (putnam-1971-a5-gcd (- x y) y)))
    0))

;; For positive X and Y, the set of unattainable natural scores is finite
;; exactly when gcd(X,Y)=1. In that case every unattainable score is below
;; X*Y. Since ACL2, Isabelle card, and Lean ncard all give zero rather than 35
;; for an infinite set, this finite count is bidirectionally equivalent to the
;; source cardinality condition.
(defun putnam-1971-a5-source-condition-p (x y)
  (and
   (equal (putnam-1971-a5-gcd x y) 1)
   (equal
    (putnam-1971-a5-unattainable-count-below (* x y) x y)
    35)
   (not (putnam-1971-a5-attainable-p 58 x y))))

;; The universally specified source predicate PAB is inlined using its
;; defining biconditional. The source's designated solution is (11,8).
(defun putnambench-putnam-1971-a5-statement (a b)
  (implies
   (and
    (integerp a)
    (integerp b)
    (< 0 a)
    (< 0 b)
    (< b a))
   (equal
    (putnam-1971-a5-source-condition-p a b)
    (and (equal a 11)
         (equal b 8)))))

(value-triple :itpeval-statement-checked)
:q
