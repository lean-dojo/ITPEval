;; Statement-only formalization of PutnamBench corpus artifact putnam_1996_b5:
;; the number of length-n two-symbol strings whose every contiguous substring
;; has symbol imbalance between -2 and 2. This file contains no proof.

(in-package "ACL2")

;; A length-n string is encoded by its unique mask in [0,2^n), with bit i
;; representing the symbol at position i. Mapping a set bit to 1 and a clear
;; bit to -1 is a bijection with both source encodings (integer units or
;; Booleans), and interval sums are exactly the source imbalance function.

(defun putnam-1996-b5-symbol-value (code index)
  (if (equal
       (mod (floor code (expt 2 (nfix index))) 2)
       1)
      1
    -1))

(defun putnam-1996-b5-interval-delta
    (code start remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (putnam-1996-b5-symbol-value code start)
     (putnam-1996-b5-interval-delta
      code
      (+ 1 (nfix start))
      (- remaining 1)))))

;; For a fixed start, check all nonempty intervals beginning there. The
;; initial remaining value is n-start, so the tested lengths are precisely
;; 1,...,n-start.
(defun putnam-1996-b5-balanced-lengths-p
    (code start remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let ((delta
           (putnam-1996-b5-interval-delta
            code start remaining)))
      (and
       (<= -2 delta)
       (<= delta 2)
       (putnam-1996-b5-balanced-lengths-p
        code start (- remaining 1))))))

;; Check every start in 0,...,n-1.
(defun putnam-1996-b5-balanced-starts-p
    (code n remaining-starts)
  (declare (xargs :measure (nfix remaining-starts)))
  (if (zp remaining-starts)
      t
    (let ((start (- remaining-starts 1)))
      (and
       (putnam-1996-b5-balanced-lengths-p
        code start (- n start))
       (putnam-1996-b5-balanced-starts-p
        code n start)))))

(defun putnam-1996-b5-balanced-code-p (code n)
  (and
   (natp n)
   (natp code)
   (< code (expt 2 n))
   (putnam-1996-b5-balanced-starts-p code n n)))

;; Count all masks below code-count; at 2^n this is the cardinality of the
;; complete source space of length-n strings satisfying balanced.
(defun putnam-1996-b5-balanced-count
    (n code-count)
  (declare (xargs :measure (nfix code-count)))
  (if (zp code-count)
      0
    (let ((code (- code-count 1)))
      (+
       (if (putnam-1996-b5-balanced-code-p code n)
           1
         0)
       (putnam-1996-b5-balanced-count n code)))))

(defun putnam-1996-b5-solution (n)
  (-
   (+
    (expt 2 (floor (+ n 2) 2))
    (expt 2 (floor (+ n 1) 2)))
   2))

(defun putnambench-putnam-1996-b5-statement (n)
  (implies
   (natp n)
   (equal
    (putnam-1996-b5-balanced-count n (expt 2 n))
    (putnam-1996-b5-solution n))))

(value-triple :itpeval-statement-checked)
:q
