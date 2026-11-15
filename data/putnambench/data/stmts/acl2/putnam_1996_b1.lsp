;; Statement-only formalization of PutnamBench corpus artifact putnam_1996_b1:
;; the number of minimal selfish subsets of {1,...,n}, for positive natural
;; n, is the nth Fibonacci number. This file contains no proof.

(in-package "ACL2")

;; The list (1 ... n) is a duplicate-free enumeration of the source interval.
;; Its recursively generated powerset contains each extensional subset exactly
;; once. Thus list length is set cardinality, and the searches below range over
;; all source subsets and all proper subsets without externalizing witnesses.

(defun putnam-1996-b1-one-through (n)
  (declare (xargs :measure (nfix n)))
  (if (or (not (natp n))
          (zp n))
      nil
    (append
     (putnam-1996-b1-one-through (- n 1))
     (list n))))

(defun putnam-1996-b1-adjoin-to-each (element sets)
  (if (endp sets)
      nil
    (cons
     (cons element (car sets))
     (putnam-1996-b1-adjoin-to-each
      element (cdr sets)))))

(defun putnam-1996-b1-powerset (carrier)
  (if (endp carrier)
      (list nil)
    (let ((tail-powerset
           (putnam-1996-b1-powerset (cdr carrier))))
      (append
       tail-powerset
       (putnam-1996-b1-adjoin-to-each
        (car carrier) tail-powerset)))))

(defun putnam-1996-b1-subsetp-equal (left right)
  (if (endp left)
      t
    (and
     (member-equal (car left) right)
     (putnam-1996-b1-subsetp-equal
      (cdr left) right))))

(defun putnam-1996-b1-proper-subset-p (left right)
  (and
   (putnam-1996-b1-subsetp-equal left right)
   (not
    (putnam-1996-b1-subsetp-equal right left))))

(defun putnam-1996-b1-selfish-p (subset)
  (member-equal (len subset) subset))

(defun putnam-1996-b1-no-proper-selfish-subset-p
    (candidates subset)
  (if (endp candidates)
      t
    (and
     (implies
      (putnam-1996-b1-proper-subset-p
       (car candidates) subset)
      (not
       (putnam-1996-b1-selfish-p
        (car candidates))))
     (putnam-1996-b1-no-proper-selfish-subset-p
      (cdr candidates) subset))))

(defun putnam-1996-b1-minimal-selfish-p (subset)
  (and
   (putnam-1996-b1-selfish-p subset)
   (putnam-1996-b1-no-proper-selfish-subset-p
    (putnam-1996-b1-powerset subset)
    subset)))

(defun putnam-1996-b1-count-minimal-selfish (subsets)
  (if (endp subsets)
      0
    (+
     (if (putnam-1996-b1-minimal-selfish-p
          (car subsets))
         1
       0)
     (putnam-1996-b1-count-minimal-selfish
      (cdr subsets)))))

;; This is the source solution recurrence: F(0)=0, F(1)=1, and
;; F(n+2)=F(n)+F(n+1).
(defun putnam-1996-b1-fibonacci (n)
  (declare (xargs :measure (nfix n)))
  (if (or (not (natp n))
          (zp n))
      0
    (if (equal n 1)
        1
      (+
       (putnam-1996-b1-fibonacci (- n 1))
       (putnam-1996-b1-fibonacci (- n 2))))))

(defun putnambench-putnam-1996-b1-statement (n)
  (implies
   (and
    (natp n)
    (<= 1 n))
   (equal
    (putnam-1996-b1-count-minimal-selfish
     (putnam-1996-b1-powerset
      (putnam-1996-b1-one-through n)))
    (putnam-1996-b1-fibonacci n))))

(value-triple :itpeval-statement-checked)
:q
