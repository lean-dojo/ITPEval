;; Statement-only formalization of PutnamBench corpus artifact putnam_1993_a4:
;; for 19 positive integers bounded by 93 and 93 positive integers bounded by
;; 19, a nonempty subset of the first family has the same sum as a subset of
;; the second family. This file contains no proof.

(in-package "ACL2")

;; Exact-length lists are in bijection with functions on the finite source
;; index types Fin 19 and Fin 93. Boolean lists of the matching lengths are
;; their characteristic functions, hence are in bijection with all subsets.

(defun putnam-1993-a4-positive-bounded-list-p
    (values remaining bound)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (equal values nil)
    (and
     (consp values)
     (integerp (car values))
     (< 0 (car values))
     (<= (car values) bound)
     (putnam-1993-a4-positive-bounded-list-p
      (cdr values) (- remaining 1) bound))))

(defun putnam-1993-a4-boolean-list-p
    (selectors remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (equal selectors nil)
    (and
     (consp selectors)
     (or (equal (car selectors) nil)
         (equal (car selectors) t))
     (putnam-1993-a4-boolean-list-p
      (cdr selectors) (- remaining 1)))))

(defun putnam-1993-a4-nonempty-selection-p (selectors)
  (if (endp selectors)
      nil
    (or
     (equal (car selectors) t)
     (putnam-1993-a4-nonempty-selection-p
      (cdr selectors)))))

(defun putnam-1993-a4-subset-sum (values selectors)
  (if (endp values)
      0
    (+
     (if (equal (car selectors) t)
         (car values)
       0)
     (putnam-1993-a4-subset-sum
      (cdr values) (cdr selectors)))))

(defun-sk putnambench-putnam-1993-a4-statement (x y)
  (exists (is js)
    (implies
     (and
      (putnam-1993-a4-positive-bounded-list-p x 19 93)
      (putnam-1993-a4-positive-bounded-list-p y 93 19))
     (and
      (putnam-1993-a4-boolean-list-p is 19)
      (putnam-1993-a4-boolean-list-p js 93)
      (putnam-1993-a4-nonempty-selection-p is)
      (equal
       (putnam-1993-a4-subset-sum x is)
       (putnam-1993-a4-subset-sum y js))))))

(value-triple :itpeval-statement-checked)
:q
