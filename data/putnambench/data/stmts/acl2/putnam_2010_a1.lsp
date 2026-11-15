;; Statement-only formalization of PutnamBench corpus artifact putnam_2010_a1:
;; the greatest number of boxes into which 1 through n can be placed with
;; equal box sums is ceiling(n/2). This file contains no proof.

(in-package "ACL2")

;; For positive K, each code below K^N has exactly N base-K digits (allowing
;; leading zeroes). Reading those digits as box labels gives a bijection with
;; all functions from {1,...,N} to the K boxes. Thus the exhaustive search
;; below is exactly the source's internal existential over BOXES.

(defun putnam-2010-a1-box-sum
    (code remaining k box)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (if (equal (mod code k) box)
           remaining
         0)
       (putnam-2010-a1-box-sum
        (floor code k)
        (- remaining 1)
        k
        box))))

(defun putnam-2010-a1-all-box-sums-equal-p
    (code n k remaining-boxes reference-sum)
  (declare (xargs :measure (nfix remaining-boxes)))
  (if (zp remaining-boxes)
      t
    (let ((box (- remaining-boxes 1)))
      (and
       (equal
        (putnam-2010-a1-box-sum code n k box)
        reference-sum)
       (putnam-2010-a1-all-box-sums-equal-p
        code n k box reference-sum)))))

(defun putnam-2010-a1-valid-boxing-code-p (code n k)
  (and
   (natp code)
   (posp k)
   (< code (expt k n))
   (putnam-2010-a1-all-box-sums-equal-p
    code
    n
    k
    k
    (putnam-2010-a1-box-sum code n k 0))))

(defun putnam-2010-a1-boxing-code-exists-p
    (candidate-count n k)
  (declare (xargs :measure (nfix candidate-count)))
  (if (zp candidate-count)
      nil
    (let ((code (- candidate-count 1)))
      (or
       (putnam-2010-a1-valid-boxing-code-p code n k)
       (putnam-2010-a1-boxing-code-exists-p
        code n k)))))

(defun putnam-2010-a1-equal-sum-boxing-exists-p (n k)
  (and
   (natp n)
   (posp k)
   (putnam-2010-a1-boxing-code-exists-p
    (expt k n) n k)))

;; When N is positive, equal sums make every box nonempty: an empty box would
;; have sum zero, forcing every box sum and hence the total 1+...+N to be zero.
;; Therefore every valid K is at most N. Searching downward from N consequently
;; returns exactly the greatest K from the source predicate.
(defun putnam-2010-a1-greatest-box-count-through
    (n candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (if (putnam-2010-a1-equal-sum-boxing-exists-p
         n candidate)
        candidate
      (putnam-2010-a1-greatest-box-count-through
       n (- candidate 1)))))

(defun putnam-2010-a1-solution (n)
  (floor (+ n 1) 2))

(defun putnambench-putnam-2010-a1-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (equal
    (putnam-2010-a1-greatest-box-count-through n n)
    (putnam-2010-a1-solution n))))

(value-triple :itpeval-statement-checked)
:q
