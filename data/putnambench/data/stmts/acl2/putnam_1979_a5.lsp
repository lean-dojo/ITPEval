;; Statement-only formalization of PutnamBench corpus artifact putnam_1979_a5:
;; two distinct real roots of x^3 - 10*x^2 + 29*x - 25 have unboundedly many
;; common values in their floor-multiple sequences. This file contains no proof.

(in-package "ACL2")

;; The cubic has exactly one root in each of (1,2), (2,3), and (5,6).
;; It has no rational root, so the sign tests below compare each of these
;; three real algebraic roots exactly with an arbitrary rational number.
(defun putnam-1979-a5-polynomial (x)
  (+ (* x x x)
     (- (* 10 x x))
     (* 29 x)
     -25))

(defun putnam-1979-a5-root-index-p (root-index)
  (and (natp root-index)
       (< root-index 3)))

(defun putnam-1979-a5-root-less-than-rational-p (root-index q)
  (and
   (putnam-1979-a5-root-index-p root-index)
   (rationalp q)
   (cond
    ((equal root-index 0)
     (or (<= 2 q)
         (and (< 1 q)
              (< q 2)
              (< 0 (putnam-1979-a5-polynomial q)))))
    ((equal root-index 1)
     (or (<= 3 q)
         (and (< 2 q)
              (< q 3)
              (< (putnam-1979-a5-polynomial q) 0))))
    (t
     (or (<= 6 q)
         (and (< 5 q)
              (< q 6)
              (< 0 (putnam-1979-a5-polynomial q))))))))

(defun putnam-1979-a5-rational-less-than-root-p (q root-index)
  (and
   (rationalp q)
   (putnam-1979-a5-root-index-p root-index)
   (not
    (putnam-1979-a5-root-less-than-rational-p root-index q))))

;; ROOT-INDEX denotes one of the three real roots. Since every root is
;; irrational, the two strict rational comparisons are exactly
;; m <= k*root < m+1.
(defun putnam-1979-a5-floor-multiple-p (root-index k m)
  (and
   (putnam-1979-a5-root-index-p root-index)
   (natp k)
   (integerp m)
   (if (zp k)
       (equal m 0)
     (and
      (putnam-1979-a5-rational-less-than-root-p
       (/ m k)
       root-index)
      (putnam-1979-a5-root-less-than-rational-p
       root-index
       (/ (+ m 1) k))))))

;; The witnesses below mirror the source quantifier order exactly. One
;; distinct pair of roots is selected once, and that same pair must share a
;; positive floor value above every natural threshold.

(defun-sk putnam-1979-a5-later-common-value-p
    (left-root right-root threshold)
  (exists (m left-index right-index)
    (and
     (natp m)
     (< threshold m)
     (natp left-index)
     (natp right-index)
     (putnam-1979-a5-floor-multiple-p
      left-root left-index m)
     (putnam-1979-a5-floor-multiple-p
      right-root right-index m))))

(defun-sk putnam-1979-a5-unbounded-common-values-p
    (left-root right-root)
  (forall (threshold)
    (implies
     (natp threshold)
     (putnam-1979-a5-later-common-value-p
      left-root right-root threshold))))

(defun-sk putnambench-putnam-1979-a5-statement ()
  (exists (left-root right-root)
    (and
     (putnam-1979-a5-root-index-p left-root)
     (putnam-1979-a5-root-index-p right-root)
     (not (equal left-root right-root))
     (putnam-1979-a5-unbounded-common-values-p
      left-root right-root))))

(value-triple :itpeval-statement-checked)
:q
