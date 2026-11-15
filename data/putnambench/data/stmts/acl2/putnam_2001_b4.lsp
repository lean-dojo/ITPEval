;; Statement-only formalization of PutnamBench corpus artifact putnam_2001_b4:
;; emptiness of the intersection of all positive iterated images of the
;; rational map f(x) = x - 1/x on Q minus {-1,0,1}. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defun putnam-2001-b4-in-s-p (x)
  (and
   (rationalp x)
   (not (equal x -1))
   (not (equal x 0))
   (not (equal x 1))))

(defun putnam-2001-b4-f (x)
  (- x (/ x)))

(defun putnam-2001-b4-iterate (n x)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      x
    (putnam-2001-b4-iterate
     (- n 1)
     (putnam-2001-b4-f x))))

;; Membership of X in the nth image of S is expressed with an internal
;; preimage witness Y in S.

(defun-sk putnam-2001-b4-in-image-p (x n)
  (exists (y)
    (and
     (putnam-2001-b4-in-s-p y)
     (equal
      (putnam-2001-b4-iterate n y)
      x))))

;; X lies in every positive iterated image.

(defun-sk putnam-2001-b4-in-all-positive-images-p (x)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= 1 n))
     (putnam-2001-b4-in-image-p x n))))

;; Since f maps S to S, the intersection is nonempty exactly when some
;; element of S lies in every positive iterated image.

(defun-sk putnam-2001-b4-intersection-nonempty-p ()
  (exists (x)
    (and
     (putnam-2001-b4-in-s-p x)
     (putnam-2001-b4-in-all-positive-images-p x))))

(defun putnambench-putnam-2001-b4-statement ()
  (not (putnam-2001-b4-intersection-nonempty-p)))

(value-triple :itpeval-statement-checked)
:q
