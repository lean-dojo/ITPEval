;; Statement-only formalization of PutnamBench corpus artifact putnam_1997_a5:
;; the number of ordered 10-tuples of positive integers whose reciprocals sum
;; to one is odd. This file contains no proof.

(in-package "ACL2")

(defun putnam-1997-a5-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (natp n)
      (if (zp n)
          1
        (* n
           (putnam-1997-a5-factorial (- n 1))))
    1))

;; Every ordered solution has a unique nondecreasing rearrangement. If K
;; entries remain and their reciprocal sum is R, the next denominator A in a
;; nondecreasing tuple satisfies R <= K/A, hence A <= floor(K/R). The search
;; therefore enumerates every sorted solution exactly once without imposing
;; an external finite cutoff. SYMMETRY-DIVISOR is the product of factorials
;; of the multiplicities seen so far, so each leaf contributes exactly the
;; number 10!/SYMMETRY-DIVISOR of distinct ordered rearrangements.
(defun putnam-1997-a5-count-sorted-range
    (remaining slots previous candidate maximum
               run-length symmetry-divisor)
  (declare
   (xargs
    :measure
    (make-ord
     1
     (+ 1 (nfix slots))
     (nfix (+ 1 (- maximum candidate))))
    :well-founded-relation o<))
  (if (and (rationalp remaining)
           (natp slots)
           (natp previous)
           (posp candidate)
           (natp maximum)
           (natp run-length)
           (posp symmetry-divisor))
      (if (zp slots)
          (if (equal remaining 0)
              (/ (putnam-1997-a5-factorial 10)
                 symmetry-divisor)
            0)
        (if (or (<= remaining 0)
                (> candidate maximum))
            0
          (let* ((next-remaining
                  (- remaining (/ candidate)))
                 (next-slots (- slots 1))
                 (same-denominator
                  (equal candidate previous))
                 (next-run-length
                  (if same-denominator
                      (+ run-length 1)
                    1))
                 (next-symmetry-divisor
                  (if same-denominator
                      (* symmetry-divisor
                         (+ run-length 1))
                    symmetry-divisor))
                 (next-maximum
                  (if (and (posp next-slots)
                           (< 0 next-remaining))
                      (floor next-slots next-remaining)
                    0)))
            (+
             (putnam-1997-a5-count-sorted-range
              next-remaining
              next-slots
              candidate
              candidate
              next-maximum
              next-run-length
              next-symmetry-divisor)
             (putnam-1997-a5-count-sorted-range
              remaining
              slots
              previous
              (+ candidate 1)
              maximum
              run-length
              symmetry-divisor)))))
    0))

(defun putnam-1997-a5-ordered-solution-count ()
  (putnam-1997-a5-count-sorted-range
   1 10 0 1 10 0 1))

(defun putnambench-putnam-1997-a5-statement ()
  (equal
   (mod (putnam-1997-a5-ordered-solution-count) 2)
   1))

(value-triple :itpeval-statement-checked)
:q
