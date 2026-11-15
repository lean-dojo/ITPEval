;; Statement-only formalization of PutnamBench corpus artifact putnam_1964_b1:
;; for a positive integer sequence with convergent reciprocal series, the
;; number B(N) of terms at most N satisfies B(N)/N -> 0. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub putnam-1964-b1-a (n) t)
(defstub putnam-1964-b1-b (n) t)

(defun-sk putnam-1964-b1-positive-sequence-p ()
  (forall (n)
    (implies
     (natp n)
     (posp (putnam-1964-b1-a n)))))

(defun putnam-1964-b1-reciprocal-partial-sum (count)
  (declare (xargs :measure (nfix count)))
  (if (and (natp count) (< 0 count))
      (+ (putnam-1964-b1-reciprocal-partial-sum (- count 1))
         (/ (putnam-1964-b1-a (- count 1))))
    0))

(defun-sk putnam-1964-b1-series-tail-p (epsilon cutoff)
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
        (putnam-1964-b1-reciprocal-partial-sum m)
        (putnam-1964-b1-reciprocal-partial-sum n)))
      epsilon))))

(defun-sk putnam-1964-b1-series-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1964-b1-series-tail-p epsilon cutoff))))

(defun-sk putnam-1964-b1-reciprocal-series-converges-p ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (putnam-1964-b1-series-cutoff-exists-p epsilon))))

;; A duplicate-free finite list enumerates exactly the indices K with A(K)
;; at most N. This is an exact first-order cardinality encoding.

(defun putnam-1964-b1-index-list-p (threshold indices)
  (if (consp indices)
      (and
       (natp (car indices))
       (<= (putnam-1964-b1-a (car indices)) threshold)
       (putnam-1964-b1-index-list-p threshold (cdr indices)))
    (equal indices nil)))

(defun-sk putnam-1964-b1-all-indices-listed-p (threshold indices)
  (forall (k)
    (implies
     (and
      (natp k)
      (<= (putnam-1964-b1-a k) threshold))
     (member-equal k indices))))

(defun putnam-1964-b1-count-witness-p (threshold indices)
  (and
   (natp threshold)
   (true-listp indices)
   (no-duplicatesp-equal indices)
   (putnam-1964-b1-index-list-p threshold indices)
   (putnam-1964-b1-all-indices-listed-p threshold indices)
   (equal (len indices) (putnam-1964-b1-b threshold))))

(defun-sk putnam-1964-b1-count-witness-exists-p (threshold)
  (exists (indices)
    (putnam-1964-b1-count-witness-p threshold indices)))

(defun-sk putnam-1964-b1-counts-terms-p ()
  (forall (threshold)
    (implies
     (natp threshold)
     (putnam-1964-b1-count-witness-exists-p threshold))))

(defun-sk putnam-1964-b1-limit-tail-p (epsilon cutoff)
  (forall (n)
    (implies
     (and
      (posp n)
      (natp cutoff)
      (<= cutoff n))
     (<
      (abs (/ (putnam-1964-b1-b n) n))
      epsilon))))

(defun-sk putnam-1964-b1-limit-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1964-b1-limit-tail-p epsilon cutoff))))

(defun-sk putnam-1964-b1-density-tends-to-zero-p ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (putnam-1964-b1-limit-cutoff-exists-p epsilon))))

(defun putnambench-putnam-1964-b1-statement ()
  (implies
   (and
    (putnam-1964-b1-positive-sequence-p)
    (putnam-1964-b1-reciprocal-series-converges-p)
    (putnam-1964-b1-counts-terms-p))
   (putnam-1964-b1-density-tends-to-zero-p)))

(value-triple :itpeval-statement-checked)
:q
