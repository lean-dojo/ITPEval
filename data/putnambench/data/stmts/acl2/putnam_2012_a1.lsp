;; Statement-only formalization of PutnamBench corpus artifact putnam_2012_a1:
;; among twelve real numbers in the open interval (1,12), three distinct
;; entries are the side lengths of an acute triangle. This file contains no proof.

(in-package "ACL2")

;; Standard ACL2 represents exact rationals rather than arbitrary reals. For
;; this closed statement, the rational formulation below is bidirectionally
;; equivalent to the source real formulation. If a real counterexample is
;; sorted as x_1 <= ... <= x_12, then it satisfies
;; x_(k-2)^2 + x_(k-1)^2 <= x_k^2 for k = 3,...,12. Multiplying x_k by
;; t^k for a sufficiently small rational t > 1 makes all these inequalities
;; strict while keeping every entry in (1,12). A sufficiently close rational
;; perturbation then preserves the strict ordering, recurrence inequalities,
;; and interval bounds, yielding a rational counterexample. Conversely, every
;; rational counterexample is already a real counterexample.

(defun putnam-2012-a1-entry-list-p (values)
  (if (consp values)
      (and
       (rationalp (car values))
       (< 1 (car values))
       (< (car values) 12)
       (putnam-2012-a1-entry-list-p (cdr values)))
    (equal values nil)))

(defun putnam-2012-a1-square (value)
  (* value value))

(defun putnam-2012-a1-acute-witness-p (values i j k)
  (and
   (natp i)
   (natp j)
   (natp k)
   (< i 12)
   (< j 12)
   (< k 12)
   (not (equal i j))
   (not (equal i k))
   (not (equal j k))
   (<= (nth i values) (nth k values))
   (<= (nth j values) (nth k values))
   (<
    (putnam-2012-a1-square (nth k values))
    (+
     (putnam-2012-a1-square (nth i values))
     (putnam-2012-a1-square (nth j values))))))

(defun putnam-2012-a1-search-k (values i j k)
  (declare (xargs :measure (nfix k)))
  (if (natp k)
      (or
       (putnam-2012-a1-acute-witness-p values i j k)
       (and
        (not (zp k))
        (putnam-2012-a1-search-k values i j (- k 1))))
    nil))

(defun putnam-2012-a1-search-j (values i j)
  (declare (xargs :measure (nfix j)))
  (if (natp j)
      (or
       (putnam-2012-a1-search-k values i j 11)
       (and
        (not (zp j))
        (putnam-2012-a1-search-j values i (- j 1))))
    nil))

(defun putnam-2012-a1-search-i (values i)
  (declare (xargs :measure (nfix i)))
  (if (natp i)
      (or
       (putnam-2012-a1-search-j values i 11)
       (and
        (not (zp i))
        (putnam-2012-a1-search-i values (- i 1))))
    nil))

(defun putnambench-putnam-2012-a1-statement (values)
  (implies
   (and
    (true-listp values)
    (equal (len values) 12)
    (putnam-2012-a1-entry-list-p values))
   (putnam-2012-a1-search-i values 11)))

(value-triple :itpeval-statement-checked)
:q
