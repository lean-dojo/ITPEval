;; Statement-only formalization of PutnamBench corpus artifact putnam_1969_b5:
;; for a strictly increasing sequence of positive integers whose reciprocal
;; series converges, its counting function K(N) satisfies K(N)/N -> 0. The
;; published problem has an integer sequence; checking natural thresholds is
;; equivalent to checking all real thresholds because K is a step function.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub putnam-1969-b5-a (n) t)
(defstub putnam-1969-b5-k (threshold) t)

(defun-sk putnam-1969-b5-positive-sequence-p ()
  (forall (n)
    (implies
     (natp n)
     (posp (putnam-1969-b5-a n)))))

(defun-sk putnam-1969-b5-strictly-increasing-p ()
  (forall (i j)
    (implies
     (and (natp i) (natp j) (< i j))
     (< (putnam-1969-b5-a i)
        (putnam-1969-b5-a j)))))

(defun putnam-1969-b5-reciprocal-partial-sum (count)
  (declare (xargs :measure (nfix count)))
  (if (and (natp count) (< 0 count))
      (+ (putnam-1969-b5-reciprocal-partial-sum (- count 1))
         (/ (putnam-1969-b5-a (- count 1))))
    0))

(defun-sk putnam-1969-b5-series-tail-p (epsilon cutoff)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (natp cutoff)
      (<= cutoff m)
      (<= cutoff n))
     (<
      (abs
       (-
        (putnam-1969-b5-reciprocal-partial-sum m)
        (putnam-1969-b5-reciprocal-partial-sum n)))
      epsilon))))

(defun-sk putnam-1969-b5-series-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1969-b5-series-tail-p epsilon cutoff))))

(defun-sk putnam-1969-b5-reciprocal-series-converges-p ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (putnam-1969-b5-series-cutoff-exists-p epsilon))))

(defun putnam-1969-b5-index-list-p (threshold indices)
  (if (consp indices)
      (and
       (natp (car indices))
       (<= (putnam-1969-b5-a (car indices)) threshold)
       (putnam-1969-b5-index-list-p threshold (cdr indices)))
    (equal indices nil)))

(defun-sk putnam-1969-b5-all-indices-listed-p (threshold indices)
  (forall (index)
    (implies
     (and
      (natp index)
      (<= (putnam-1969-b5-a index) threshold))
     (member-equal index indices))))

(defun putnam-1969-b5-count-witness-p (threshold indices)
  (and
   (natp threshold)
   (true-listp indices)
   (no-duplicatesp-equal indices)
   (putnam-1969-b5-index-list-p threshold indices)
   (putnam-1969-b5-all-indices-listed-p threshold indices)
   (equal (len indices) (putnam-1969-b5-k threshold))))

(defun-sk putnam-1969-b5-count-witness-exists-p (threshold)
  (exists (indices)
    (putnam-1969-b5-count-witness-p threshold indices)))

(defun-sk putnam-1969-b5-counting-function-p ()
  (forall (threshold)
    (implies
     (natp threshold)
     (putnam-1969-b5-count-witness-exists-p threshold))))

(defun-sk putnam-1969-b5-density-tail-p (epsilon cutoff)
  (forall (threshold)
    (implies
     (and
      (posp threshold)
      (natp cutoff)
      (<= cutoff threshold))
     (<
      (abs (/ (putnam-1969-b5-k threshold) threshold))
      epsilon))))

(defun-sk putnam-1969-b5-density-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1969-b5-density-tail-p epsilon cutoff))))

(defun-sk putnam-1969-b5-density-tends-to-zero-p ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (putnam-1969-b5-density-cutoff-exists-p epsilon))))

(defun putnambench-putnam-1969-b5-statement ()
  (implies
   (and
    (putnam-1969-b5-positive-sequence-p)
    (putnam-1969-b5-strictly-increasing-p)
    (putnam-1969-b5-reciprocal-series-converges-p)
    (putnam-1969-b5-counting-function-p))
   (putnam-1969-b5-density-tends-to-zero-p)))

(value-triple :itpeval-statement-checked)
:q
