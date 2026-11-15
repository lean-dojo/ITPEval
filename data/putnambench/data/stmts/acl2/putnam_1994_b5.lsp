;; Statement-only formalization of PutnamBench corpus artifact putnam_1994_b5:
;; for every positive integer n, some real alpha makes the first n iterates
;; of x |-> floor(alpha*x), starting at n^2, agree with the corresponding
;; floors of alpha^k*n^2 and equal n^2-k. This file contains no proof.

(in-package "ACL2")

;; The source hypothesis uniquely defines f_alpha(x) as floor(alpha*x), so the
;; floor map below eliminates that function parameter definitionally.
(defun putnam-1994-b5-iterate-floor-map (alpha x steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      x
    (putnam-1994-b5-iterate-floor-map
     alpha
     (floor (* alpha x) 1)
     (- steps 1))))

(defun putnam-1994-b5-conditions-through-p (n alpha k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      t
    (let ((n-square (* n n)))
      (and
       (equal
        (putnam-1994-b5-iterate-floor-map
         alpha n-square k)
        (- n-square k))
       (equal
        (floor (* (expt alpha k) n-square) 1)
        (- n-square k))
       (putnam-1994-b5-conditions-through-p
        n alpha (- k 1))))))

;; Standard ACL2 represents the witness as a rational real. This does not
;; narrow this particular source existential: with N=n^2, the rational
;; alpha=1-1/N is a witness for every positive n. Its j-th iterate step has
;; value floor((1-1/N)*(N-j))=N-j-1 for 0<=j<n, and for 1<=k<=n the standard
;; binomial bounds put N*(1-1/N)^k in [N-k,N-k+1). Conversely every rational
;; witness is a source real witness. The existential remains internal rather
;; than being replaced by a bounded search or an external parameter.
(defun putnam-1994-b5-candidate-p (n alpha)
  (and
   (rationalp alpha)
   (putnam-1994-b5-conditions-through-p n alpha n)))

(defun-sk putnam-1994-b5-witness-exists-p (n)
  (exists (alpha)
    (putnam-1994-b5-candidate-p n alpha)))

(defun putnambench-putnam-1994-b5-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (putnam-1994-b5-witness-exists-p n)))

(value-triple :itpeval-statement-checked)
:q
