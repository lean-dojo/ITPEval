;; Statement-only formalization of VERINA corpus artifact verina_advanced_58,
;; "nthUglyNumber": the deterministic three-index sequence program returns the
;; nth natural number whose only prime factors are 2, 3, and 5. This file
;; contains no proof.

(in-package "ACL2")

;; The Nat input domain is explicit in the final correctness predicate.

(defun verina-advanced-58-nth-ugly-number-precond (n)
  (< 0 n))

(defun verina-advanced-58-nat-min (left right)
  (if (< left right)
      left
    right))

;; Lean's List.get! on List Nat returns zero when the index is out of bounds.

(defun verina-advanced-58-nth-default-zero (seq index)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (if (consp seq)
          (car seq)
        0)
    (if (consp seq)
        (verina-advanced-58-nth-default-zero
         (cdr seq)
         (- index 1))
      0)))

;; The four-entry list represents the source quadruple
;; (next, c2', c3', c5') without changing any component.

(defun verina-advanced-58-next-ugly (seq c2 c3 c5)
  (let* ((i2
          (* (verina-advanced-58-nth-default-zero seq c2)
             2))
         (i3
          (* (verina-advanced-58-nth-default-zero seq c3)
             3))
         (i5
          (* (verina-advanced-58-nth-default-zero seq c5)
             5))
         (next
          (verina-advanced-58-nat-min
           i2
           (verina-advanced-58-nat-min i3 i5)))
         (c2-next
          (if (equal next i2) (+ c2 1) c2))
         (c3-next
          (if (equal next i3) (+ c3 1) c3))
         (c5-next
          (if (equal next i5) (+ c5 1) c5)))
    (list next c2-next c3-next c5-next)))

;; This is the source local loop. Each transition appends NEXT and advances
;; every index whose multiple equals NEXT.

(defun verina-advanced-58-loop (i seq c2 c3 c5)
  (declare (xargs :measure (nfix i)))
  (if (zp i)
      seq
    (let* ((state
            (verina-advanced-58-next-ugly
             seq c2 c3 c5))
           (next (car state))
           (c2-next (cadr state))
           (c3-next (caddr state))
           (c5-next (cadddr state)))
      (verina-advanced-58-loop
       (- i 1)
       (append seq (list next))
       c2-next
       c3-next
       c5-next))))

;; The proof-valued precondition argument is computationally erased. NFIX
;; implements Lean's truncated Nat subtraction before both loop iteration and
;; final List.get! indexing.

(defun verina-advanced-58-nth-ugly-number (n)
  (let* ((index (nfix (- n 1)))
         (seq
          (verina-advanced-58-loop
           index
           (list 1)
           0
           0
           0)))
    (verina-advanced-58-nth-default-zero seq index)))

;; On a recursive branch, p > 1 and n is positive and divisible by p, so
;; floor(n/p) is strictly smaller than n. Fuel initialized to n therefore
;; cannot expire and gives exactly the source well-founded recursion.

(defun verina-advanced-58-divide-out-aux (n p fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (and
       (natp n)
       (natp p)
       (< 1 p)
       (< 0 n)
       (equal (mod n p) 0))
      (if (zp fuel)
          n
        (verina-advanced-58-divide-out-aux
         (floor n p)
         p
         (- fuel 1)))
    n))

(defun verina-advanced-58-divide-out (n p)
  (verina-advanced-58-divide-out-aux
   n
   p
   (nfix n)))

(defun verina-advanced-58-is-ugly (x)
  (if (equal x 0)
      nil
    (let* ((n1
            (verina-advanced-58-divide-out x 2))
           (n2
            (verina-advanced-58-divide-out n1 3))
           (n3
            (verina-advanced-58-divide-out n2 5)))
      (equal n3 1))))

;; CURRENT through CURRENT + REMAINING - 1 is a List.range segment. Counting
;; entries accepted by IS-UGLY is therefore the length of the source filter.

(defun verina-advanced-58-count-ugly-from
    (current remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if (verina-advanced-58-is-ugly current)
         1
       0)
     (verina-advanced-58-count-ugly-from
      (+ current 1)
      (- remaining 1)))))

(defun verina-advanced-58-count-ugly-below (result)
  (verina-advanced-58-count-ugly-from
   0
   (nfix result)))

(defun verina-advanced-58-nth-ugly-number-postcond
    (n result)
  (and
   (natp n)
   (natp result)
   (verina-advanced-58-is-ugly result)
   (equal
    (verina-advanced-58-count-ugly-below result)
    (nfix (- n 1)))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the Nat binder and positive-index precondition, and
;; its conclusion applies the complete postcondition to the exact executable
;; result.

(defun
    verina-advanced-58-nth-ugly-number-spec-satisfied-statement
    (n)
  (implies
   (and
    (natp n)
    (verina-advanced-58-nth-ugly-number-precond n))
   (verina-advanced-58-nth-ugly-number-postcond
    n
    (verina-advanced-58-nth-ugly-number n))))

(value-triple :itpeval-statement-checked)
:q
