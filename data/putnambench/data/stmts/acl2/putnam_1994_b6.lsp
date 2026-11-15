;; Statement-only formalization of PutnamBench corpus artifact putnam_1994_b6:
;; for the sequence n(a) = 101*a - 100*2^a on indices 0 through 99,
;; congruent pairwise sums modulo 10100 determine the same unordered pair.
;; This file contains no proof.

(in-package "ACL2")

;; The source function n is uniquely fixed by its defining hypothesis, so it
;; is eliminated here by direct substitution of that definition.
(defun putnam-1994-b6-sequence-term (a)
  (- (* 101 a)
     (* 100 (expt 2 a))))

(defun putnambench-putnam-1994-b6-statement (a b c d)
  (implies
   (and (natp a)
        (natp b)
        (natp c)
        (natp d)
        (<= a 99)
        (<= b 99)
        (<= c 99)
        (<= d 99)
        (equal
         (mod (+ (putnam-1994-b6-sequence-term a)
                 (putnam-1994-b6-sequence-term b))
              10100)
         (mod (+ (putnam-1994-b6-sequence-term c)
                 (putnam-1994-b6-sequence-term d))
              10100)))
   (or (and (equal a c)
            (equal b d))
       (and (equal a d)
            (equal b c)))))

(value-triple :itpeval-statement-checked)
:q
