;; Statement-only formalization of PutnamBench corpus artifact putnam_2003_a1:
;; for every positive integer n, exactly n finite nondecreasing sequences of
;; positive integers sum to n and have last term at most one greater than the
;; first term. This file contains no proof.

(in-package "ACL2")

;; A source function with witness k is determined by its nonzero prefix of
;; length k, since every later value is zero. Conversely, every nonempty list
;; counted below extends uniquely by zeros to such a function. Positivity and
;; sum n force both the prefix length and every entry to be at most n, so the
;; finite enumeration through n is exactly the source cardinality.

(defun putnam-2003-a1-positive-integer-list-p (values)
  (if (consp values)
      (and
       (posp (car values))
       (putnam-2003-a1-positive-integer-list-p
        (cdr values)))
    (equal values nil)))

(defun putnam-2003-a1-sum (values)
  (if (consp values)
      (+ (car values)
         (putnam-2003-a1-sum (cdr values)))
    0))

(defun putnam-2003-a1-nondecreasing-p (values)
  (if (and (consp values)
           (consp (cdr values)))
      (and
       (<= (car values) (cadr values))
       (putnam-2003-a1-nondecreasing-p
        (cdr values)))
    t))

(defun putnam-2003-a1-valid-sequence-p (values n)
  (and
   (consp values)
   (putnam-2003-a1-positive-integer-list-p values)
   (equal (putnam-2003-a1-sum values) n)
   (putnam-2003-a1-nondecreasing-p values)
   (<= (car (last values))
       (+ (car values) 1))))

(defun putnam-2003-a1-prepend-to-each (value sequences)
  (if (consp sequences)
      (cons
       (cons value (car sequences))
       (putnam-2003-a1-prepend-to-each
        value (cdr sequences)))
    nil))

(defun putnam-2003-a1-prepend-values-through
    (value sequences)
  (declare (xargs :measure (nfix value)))
  (if (zp value)
      nil
    (append
     (putnam-2003-a1-prepend-to-each
      value sequences)
     (putnam-2003-a1-prepend-values-through
      (- value 1) sequences))))

(defun putnam-2003-a1-positive-lists-exact
    (length bound)
  (declare (xargs :measure (nfix length)))
  (if (zp length)
      (list nil)
    (putnam-2003-a1-prepend-values-through
     bound
     (putnam-2003-a1-positive-lists-exact
      (- length 1) bound))))

(defun putnam-2003-a1-positive-lists-through
    (maximum-length bound)
  (declare (xargs :measure (nfix maximum-length)))
  (if (zp maximum-length)
      nil
    (append
     (putnam-2003-a1-positive-lists-exact
      maximum-length bound)
     (putnam-2003-a1-positive-lists-through
      (- maximum-length 1) bound))))

(defun putnam-2003-a1-count-valid
    (sequences n)
  (if (consp sequences)
      (+ (if (putnam-2003-a1-valid-sequence-p
              (car sequences) n)
             1
           0)
         (putnam-2003-a1-count-valid
          (cdr sequences) n))
    0))

(defun putnam-2003-a1-sequence-count (n)
  (if (natp n)
      (putnam-2003-a1-count-valid
       (putnam-2003-a1-positive-lists-through n n)
       n)
    0))

(defun putnambench-putnam-2003-a1-statement (n)
  (implies
   (posp n)
   (equal
    (putnam-2003-a1-sequence-count n)
    n)))

(value-triple :itpeval-statement-checked)
:q
