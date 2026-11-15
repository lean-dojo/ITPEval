;; Statement-only formalization of PutnamBench artifact putnam_1966_b2:
;; among any ten consecutive positive integers, at least one is relatively
;; prime to each of the other nine. This file contains no proof.

(in-package "ACL2")

(defun putnam-1966-b2-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (putnam-1966-b2-gcd a (- b a)))
            (t
             (putnam-1966-b2-gcd (- a b) b)))
    0))

(defun putnam-1966-b2-coprime-p (a b)
  (equal (putnam-1966-b2-gcd a b) 1))

;; For OFFSET in 0,...,9, this is exactly the assertion that n+OFFSET is
;; coprime to every distinct member of {n,n+1,...,n+9}.
(defun putnam-1966-b2-candidate-p (n offset)
  (let ((k (+ n offset)))
    (and
     (or (equal offset 0)
         (putnam-1966-b2-coprime-p (+ n 0) k))
     (or (equal offset 1)
         (putnam-1966-b2-coprime-p (+ n 1) k))
     (or (equal offset 2)
         (putnam-1966-b2-coprime-p (+ n 2) k))
     (or (equal offset 3)
         (putnam-1966-b2-coprime-p (+ n 3) k))
     (or (equal offset 4)
         (putnam-1966-b2-coprime-p (+ n 4) k))
     (or (equal offset 5)
         (putnam-1966-b2-coprime-p (+ n 5) k))
     (or (equal offset 6)
         (putnam-1966-b2-coprime-p (+ n 6) k))
     (or (equal offset 7)
         (putnam-1966-b2-coprime-p (+ n 7) k))
     (or (equal offset 8)
         (putnam-1966-b2-coprime-p (+ n 8) k))
     (or (equal offset 9)
         (putnam-1966-b2-coprime-p (+ n 9) k)))))

;; The source set-valued function is eliminated by substituting its defining
;; ten-element set. The finite disjunction is its existential quantifier.
(defun putnambench-putnam-1966-b2-statement (n)
  (implies
   (and (integerp n)
        (< 0 n))
   (or
    (putnam-1966-b2-candidate-p n 0)
    (putnam-1966-b2-candidate-p n 1)
    (putnam-1966-b2-candidate-p n 2)
    (putnam-1966-b2-candidate-p n 3)
    (putnam-1966-b2-candidate-p n 4)
    (putnam-1966-b2-candidate-p n 5)
    (putnam-1966-b2-candidate-p n 6)
    (putnam-1966-b2-candidate-p n 7)
    (putnam-1966-b2-candidate-p n 8)
    (putnam-1966-b2-candidate-p n 9))))

(value-triple :itpeval-statement-checked)
:q
