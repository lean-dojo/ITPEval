;; Statement-only formalization of PutnamBench artifact putnam_1968_a3:
;; existence of a Gray-code ordering of all subsets of an arbitrary finite
;; set, beginning with the empty set. This file contains no proof.

(in-package "ACL2")

;; A finite set of cardinality N is identified with its positions
;; 0,...,N-1. Its subsets are exactly the N-bit naturals below 2^N. A list
;; of all subsets is encoded by the base-2^N digits of SEQUENCE-CODE. This
;; representation is invariant under a bijection of finite carriers, so it
;; preserves arbitrary finite sets rather than selecting a particular one.

(defun putnam-1968-a3-sequence-entry
    (sequence-code index radix)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (mod sequence-code radix)
    (putnam-1968-a3-sequence-entry
     (floor sequence-code radix)
     (- index 1)
     radix)))

(defun putnam-1968-a3-occurrence-count
    (subset-code sequence-code positions radix)
  (declare (xargs :measure (nfix positions)))
  (if (zp positions)
      0
    (let ((index (- positions 1)))
      (+
       (if (equal
            (putnam-1968-a3-sequence-entry
             sequence-code index radix)
            subset-code)
           1
         0)
       (putnam-1968-a3-occurrence-count
        subset-code sequence-code index radix)))))

(defun putnam-1968-a3-every-subset-once-p
    (subset-count sequence-code positions radix)
  (declare (xargs :measure (nfix subset-count)))
  (if (zp subset-count)
      t
    (let ((subset-code (- subset-count 1)))
      (and
       (equal
        (putnam-1968-a3-occurrence-count
         subset-code sequence-code positions radix)
        1)
       (putnam-1968-a3-every-subset-once-p
        subset-code sequence-code positions radix)))))

(defun putnam-1968-a3-bit-difference-count
    (left right bits)
  (declare (xargs :measure (nfix bits)))
  (if (zp bits)
      0
    (+
     (if (equal (mod left 2) (mod right 2))
         0
       1)
     (putnam-1968-a3-bit-difference-count
      (floor left 2)
      (floor right 2)
      (- bits 1)))))

(defun putnam-1968-a3-adjacent-p
    (sequence-code adjacency-count radix bits)
  (declare (xargs :measure (nfix adjacency-count)))
  (if (zp adjacency-count)
      t
    (let ((index (- adjacency-count 1)))
      (and
       (equal
        (putnam-1968-a3-bit-difference-count
         (putnam-1968-a3-sequence-entry
          sequence-code index radix)
         (putnam-1968-a3-sequence-entry
          sequence-code (+ index 1) radix)
         bits)
        1)
       (putnam-1968-a3-adjacent-p
        sequence-code index radix bits)))))

(defun putnam-1968-a3-valid-sequence-code-p
    (sequence-code radix bits)
  (and
   (equal
    (putnam-1968-a3-sequence-entry
     sequence-code 0 radix)
    0)
   (putnam-1968-a3-every-subset-once-p
    radix sequence-code radix radix)
   (putnam-1968-a3-adjacent-p
    sequence-code (- radix 1) radix bits)))

;; This exhaustive finite search is the source statement's internal
;; existential quantifier over lists. It ranges over every list of length
;; 2^N whose entries are subsets of the N-element carrier.
(defun putnam-1968-a3-sequence-exists-p
    (candidate-count radix bits)
  (declare (xargs :measure (nfix candidate-count)))
  (if (zp candidate-count)
      nil
    (let ((sequence-code (- candidate-count 1)))
      (or
       (putnam-1968-a3-valid-sequence-code-p
        sequence-code radix bits)
       (putnam-1968-a3-sequence-exists-p
        sequence-code radix bits)))))

(defun putnambench-putnam-1968-a3-statement (n)
  (implies
   (natp n)
   (let ((radix (expt 2 n)))
     (putnam-1968-a3-sequence-exists-p
      (expt radix radix)
      radix
      n))))

(value-triple :itpeval-statement-checked)
:q
