;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sumrange_Simple_queryqtvc: the simple linear range-sum query
;; verification condition, including initialization, loop-invariant
;; preservation, and the final half-open integer-array sum. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite integer lists represent Why3 arrays of mathematical integers.

(defun sumrange-simple-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (sumrange-simple-integer-list-p (cdr xs)))))

;; Int.toNat sends negative indices to zero, and the exported total list lookup
;; returns the integer default zero outside the list.

(defun sumrange-simple-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun sumrange-simple-nth-int (index xs)
  (let ((value
         (nth
          (sumrange-simple-int-to-nat index)
          xs)))
    (if (integerp value)
        value
      0)))

;; On every source-valid interval this is the source recursive definition of
;; ArraySum.sum, summing exactly the entries with LOWER <= index < UPPER.

(defun sumrange-simple-range-sum (xs lower upper)
  (declare
   (xargs :measure
          (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (sumrange-simple-nth-int lower xs)
     (sumrange-simple-range-sum
      xs (+ lower 1) upper))))

;; Preserve the source's innermost universal quantifier over every integer K.

(defun-sk sumrange-simple-all-indices-p (a i o1 s)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (and
        (<= i k)
        (<= k o1))
       (equal
        s
        (sumrange-simple-range-sum a i k)))
      (and
       (and
        (<= 0 k)
        (< k (len a)))
       (equal
        (+
         s
         (sumrange-simple-nth-int k a))
        (sumrange-simple-range-sum
         a i (+ k 1))))))))

;; For each integer accumulator S, retain both the universally quantified loop
;; step and the loop-exit implication in their original scope.

(defun-sk sumrange-simple-all-accumulators-p (a i j o1)
  (forall (s)
    (implies
     (integerp s)
     (and
      (sumrange-simple-all-indices-p
       a i o1 s)
      (implies
       (equal
        s
        (sumrange-simple-range-sum
         a i (+ o1 1)))
       (equal
        s
        (sumrange-simple-range-sum
         a i j)))))))

;; The outer quantifier ranges over exactly the source integer indices and
;; integer arrays. Both generated branches for the loop range remain explicit.

(defun-sk
  ntp4vc-pearl-sumrange-simple-queryqtvc-statement
  ()
  (forall (i j a)
    (implies
     (and
      (integerp i)
      (integerp j)
      (sumrange-simple-integer-list-p a))
     (implies
      (and
       (<= 0 i)
       (<= i j)
       (<= j (len a)))
      (let ((o1 (- j 1)))
        (and
         (implies
          (<= i (+ o1 1))
          (and
           (equal
            0
            (sumrange-simple-range-sum
             a i i))
           (sumrange-simple-all-accumulators-p
            a i j o1)))
         (implies
          (< (+ o1 1) i)
          (equal
           0
           (sumrange-simple-range-sum
            a i j)))))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
