;; Statement-only formalization of PutnamBench corpus artifact putnam_2013_a2:
;; the least possible final terms of increasing integer lists that make
;; n times the list product a square distinguish positive nonsquare integers.
;; This file contains no proof.

(in-package "ACL2")

;; S, P, T, and f are eliminated using their source definitions. For fixed
;; positive N and endpoint R, every admissible increasing list ending in R is
;; uniquely R preceded by a subset of the finite interval N+1,...,R-1.
;; PUTNAM-2013-A2-ENDPOINT-P exhausts exactly those subsets; R itself remains
;; unbounded. The final predicate is therefore the relational form of
;; injectivity of the unique least endpoint.

(defun putnam-2013-a2-floor-sqrt-down (x candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (if (<= (* candidate candidate) x)
        candidate
      (putnam-2013-a2-floor-sqrt-down
       x (- candidate 1)))))

(defun putnam-2013-a2-perfect-square-p (x)
  (if (and (integerp x)
           (<= 0 x))
      (let ((root
             (putnam-2013-a2-floor-sqrt-down x x)))
        (equal (* root root) x))
    nil))

(defun putnam-2013-a2-positive-nonsquare-p (n)
  (and (integerp n)
       (< 0 n)
       (not (putnam-2013-a2-perfect-square-p n))))

(defun putnam-2013-a2-subset-square-exists-p
    (n current endpoint partial-product steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (putnam-2013-a2-perfect-square-p
       (* n endpoint partial-product))
    (or
     (putnam-2013-a2-subset-square-exists-p
      n
      (+ current 1)
      endpoint
      (* partial-product current)
      (- steps 1))
     (putnam-2013-a2-subset-square-exists-p
      n
      (+ current 1)
      endpoint
      partial-product
      (- steps 1)))))

(defun putnam-2013-a2-endpoint-p (n endpoint)
  (and
   (integerp n)
   (integerp endpoint)
   (< n endpoint)
   (putnam-2013-a2-subset-square-exists-p
    n
    (+ n 1)
    endpoint
    1
    (- (- endpoint n) 1))))

(defun putnam-2013-a2-no-smaller-endpoint-p
    (n candidate steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      t
    (and
     (not (putnam-2013-a2-endpoint-p n candidate))
     (putnam-2013-a2-no-smaller-endpoint-p
      n
      (+ candidate 1)
      (- steps 1)))))

(defun putnam-2013-a2-minimum-endpoint-p (n endpoint)
  (and
   (putnam-2013-a2-endpoint-p n endpoint)
   (putnam-2013-a2-no-smaller-endpoint-p
    n
    (+ n 1)
    (- (- endpoint n) 1))))

(defun putnambench-putnam-2013-a2-statement
    (left right common-endpoint)
  (implies
   (and
    (putnam-2013-a2-positive-nonsquare-p left)
    (putnam-2013-a2-positive-nonsquare-p right)
    (putnam-2013-a2-minimum-endpoint-p
     left common-endpoint)
    (putnam-2013-a2-minimum-endpoint-p
     right common-endpoint))
   (equal left right)))

(value-triple :itpeval-statement-checked)
:q
