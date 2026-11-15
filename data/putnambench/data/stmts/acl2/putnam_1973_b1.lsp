;; Statement-only formalization of PutnamBench corpus artifact putnam_1973_b1:
;; if deleting any one of 2*n+1 indexed integers leaves values partitionable
;; into two n-element parts with equal sums, then all the integers are equal.
;; This file contains no proof.

(in-package "ACL2")

;; List order represents the source index set, so repeated integer values remain
;; distinct indexed entries. The recursive search chooses every n-position
;; subsequence of a deletion; its complement is the other n-position part.

(defun putnam-1973-b1-integer-list-p (values)
  (if (consp values)
      (and
       (integerp (car values))
       (putnam-1973-b1-integer-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1973-b1-sum-list (values)
  (if (consp values)
      (+ (car values)
         (putnam-1973-b1-sum-list (cdr values)))
    0))

(defun putnam-1973-b1-balanced-choice-exists-p
    (remaining needed chosen-sum total-sum)
  (declare (xargs :measure (len remaining)))
  (cond
   ((zp needed)
    (equal (* 2 chosen-sum) total-sum))
   ((endp remaining) nil)
   (t
    (or
     (putnam-1973-b1-balanced-choice-exists-p
      (cdr remaining)
      (- needed 1)
      (+ chosen-sum (car remaining))
      total-sum)
     (putnam-1973-b1-balanced-choice-exists-p
      (cdr remaining)
      needed
      chosen-sum
      total-sum)))))

(defun putnam-1973-b1-balanced-after-removal-p
    (values n)
  (putnam-1973-b1-balanced-choice-exists-p
   values n 0 (putnam-1973-b1-sum-list values)))

(defun putnam-1973-b1-every-removal-balanced-p
    (prefix-reversed remaining n)
  (declare (xargs :measure (len remaining)))
  (if (consp remaining)
      (and
       (putnam-1973-b1-balanced-after-removal-p
        (revappend prefix-reversed (cdr remaining))
        n)
       (putnam-1973-b1-every-removal-balanced-p
        (cons (car remaining) prefix-reversed)
        (cdr remaining)
        n))
    t))

(defun putnam-1973-b1-all-equal-to-p
    (value remaining)
  (if (consp remaining)
      (and
       (equal value (car remaining))
       (putnam-1973-b1-all-equal-to-p
        value (cdr remaining)))
    (equal remaining nil)))

(defun putnam-1973-b1-all-equal-p (values)
  (if (consp values)
      (putnam-1973-b1-all-equal-to-p
       (car values) (cdr values))
    (equal values nil)))

(defun putnambench-putnam-1973-b1-statement
    (n values)
  (implies
   (and
    (natp n)
    (true-listp values)
    (putnam-1973-b1-integer-list-p values)
    (equal (len values) (+ (* 2 n) 1))
    (putnam-1973-b1-every-removal-balanced-p
     nil values n))
   (putnam-1973-b1-all-equal-p values)))

(value-triple :itpeval-statement-checked)
:q
