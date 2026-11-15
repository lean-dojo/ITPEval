;; Statement-only formalization of PutnamBench corpus artifact putnam_2003_a5:
;; the published bijection between Dyck n-paths with no even-length return and
;; Dyck (n-1)-paths, expressed by equality of their finite cardinalities.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A path of length L whose values lie in {-1,1} is represented bijectively by
;; an L-bit natural number. Thus the searches below enumerate exactly the
;; finite-function objects that can satisfy the source Dyck-path definitions.

(defun putnam-2003-a5-step (code index)
  (if (equal
       (mod (floor code (expt 2 index)) 2)
       1)
      1
    -1))

(defun putnam-2003-a5-prefix-sum (code count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (putnam-2003-a5-prefix-sum code (- count 1))
       (putnam-2003-a5-step code (- count 1)))))

(defun putnam-2003-a5-dyck-prefixes-p
    (code remaining index height)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (equal height 0)
    (let ((next-height
           (+ height
              (putnam-2003-a5-step code index))))
      (and
       (<= 0 next-height)
       (putnam-2003-a5-dyck-prefixes-p
        code
        (- remaining 1)
        (+ index 1)
        next-height)))))

(defun putnam-2003-a5-dyck-path-p (code length)
  (and
   (natp code)
   (natp length)
   (< code (expt 2 length))
   (putnam-2003-a5-dyck-prefixes-p
    code length 0 0)))

(defun putnam-2003-a5-all-downsteps-p
    (code index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and
     (equal (putnam-2003-a5-step code index) -1)
     (putnam-2003-a5-all-downsteps-p
      code
      (+ index 1)
      (- count 1)))))

(defun putnam-2003-a5-even-return-at-index-p
    (code index down-count)
  (declare (xargs :measure (nfix down-count)))
  (if (zp down-count)
      nil
    (or
     (and
      (equal (putnam-2003-a5-step code index) 1)
      (putnam-2003-a5-all-downsteps-p
       code
       (+ index 1)
       down-count)
      (equal (mod down-count 2) 0)
      (equal
       (putnam-2003-a5-prefix-sum
        code
        (+ index down-count 1))
       0))
     (putnam-2003-a5-even-return-at-index-p
      code index (- down-count 1)))))

(defun putnam-2003-a5-has-even-return-p
    (code index-count length)
  (declare (xargs :measure (nfix index-count)))
  (if (zp index-count)
      nil
    (let* ((index (- index-count 1))
           (available-downsteps (- (- length index) 1)))
      (or
       (putnam-2003-a5-even-return-at-index-p
        code index available-downsteps)
       (putnam-2003-a5-has-even-return-p
        code (- index-count 1) length)))))

(defun putnam-2003-a5-no-even-return-p
    (code length)
  (not
   (putnam-2003-a5-has-even-return-p
    code length length)))

(defun putnam-2003-a5-count-dyck-paths
    (candidate-count length)
  (declare (xargs :measure (nfix candidate-count)))
  (if (zp candidate-count)
      0
    (let ((code (- candidate-count 1)))
      (+
       (if (putnam-2003-a5-dyck-path-p code length)
           1
         0)
       (putnam-2003-a5-count-dyck-paths
        code length)))))

(defun putnam-2003-a5-count-no-even-return-dyck-paths
    (candidate-count length)
  (declare (xargs :measure (nfix candidate-count)))
  (if (zp candidate-count)
      0
    (let ((code (- candidate-count 1)))
      (+
       (if (and
            (putnam-2003-a5-dyck-path-p code length)
            (putnam-2003-a5-no-even-return-p
             code length))
           1
         0)
       (putnam-2003-a5-count-no-even-return-dyck-paths
        code length)))))

;; For finite sets A and B, the published one-to-one correspondence is
;; equivalent in both directions to |A| = |B|. The exact counts below therefore
;; preserve the bijection claim for every positive n without externalizing a
;; function witness.

;; The Lean source tests every k in (i,j] for p(k)=-1. This is the intended
;; no-even-return condition described by the problem statement.

(defun putnambench-putnam-2003-a5-statement (n)
  (implies
   (and (natp n) (< 0 n))
   (let* ((source-length (* 2 n))
          (target-length (* 2 (- n 1)))
          (source-count
           (putnam-2003-a5-count-no-even-return-dyck-paths
            (expt 2 source-length)
            source-length))
          (target-count
           (putnam-2003-a5-count-dyck-paths
            (expt 2 target-length)
            target-length)))
     (equal source-count target-count))))

(value-triple :itpeval-statement-checked)
:q
