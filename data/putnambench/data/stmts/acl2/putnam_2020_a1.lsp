;; Statement-only formalization of PutnamBench corpus artifact putnam_2020_a1:
;; the number of positive multiples of 2020 having at most 2020 decimal
;; digits and consisting of a nonempty block of ones followed by zeros is
;; 508536. This file contains no proof.

(in-package "ACL2")

;; For ONES >= 1 and ZEROS >= 0, the represented number is the decimal
;; repunit with ONES digits, followed by ZEROS zero digits. Every positive
;; integer of the source form has exactly one such pair, and its number of
;; decimal digits is ONES + ZEROS. Thus counting the pairs with sum at most
;; 2020 is bijectively equivalent to taking the cardinality of the source set.

(defun putnam-2020-a1-repunit (ones)
  (declare (xargs :measure (nfix ones)))
  (if (zp ones)
      0
    (+ 1
       (* 10
          (putnam-2020-a1-repunit
           (- (nfix ones) 1))))))

(defun putnam-2020-a1-number (ones zeros)
  (* (putnam-2020-a1-repunit ones)
     (expt 10 (nfix zeros))))

(defun putnam-2020-a1-divisible-p (ones zeros)
  (equal
   (mod (putnam-2020-a1-number ones zeros) 2020)
   0))

;; Count all zero-block lengths from 0 through ZEROS for a fixed positive
;; one-block length. This is the source's existential digit description
;; internalized as an exact finite enumeration.
(defun putnam-2020-a1-count-zero-blocks (ones zeros)
  (declare (xargs :measure (nfix zeros)))
  (if (zp zeros)
      (if (putnam-2020-a1-divisible-p ones 0) 1 0)
    (+ (if (putnam-2020-a1-divisible-p
            ones (nfix zeros))
           1
         0)
       (putnam-2020-a1-count-zero-blocks
        ones (- (nfix zeros) 1)))))

;; Count the pairs (ONES,ZEROS) with 1 <= ONES <= MAX-DIGITS and
;; 0 <= ZEROS <= MAX-DIGITS-ONES.
(defun putnam-2020-a1-count-through-ones (ones max-digits)
  (declare (xargs :measure (nfix ones)))
  (if (zp ones)
      0
    (+ (putnam-2020-a1-count-zero-blocks
        (nfix ones)
        (- (nfix max-digits) (nfix ones)))
       (putnam-2020-a1-count-through-ones
        (- (nfix ones) 1)
        max-digits))))

(defun putnambench-putnam-2020-a1-statement ()
  (equal
   (putnam-2020-a1-count-through-ones 2020 2020)
   508536))

(value-triple :itpeval-statement-checked)
:q
