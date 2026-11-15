;; Statement-only formalization of PutnamBench corpus artifact putnam_2009_b3:
;; the positive integers where the second difference of the number of
;; mediocre subsets of {1,...,n} is one are exactly 2^k-1 for k at least one.
;; This file contains no proof.

(in-package "ACL2")

;; The list (1 ... n) is a duplicate-free enumeration of the source interval.
;; Its powerset therefore contains every extensional subset exactly once.

(defun putnam-2009-b3-one-through (n)
  (declare (xargs :measure (nfix n)))
  (if (or (not (natp n))
          (zp n))
      nil
    (append
     (putnam-2009-b3-one-through (- n 1))
     (list n))))

(defun putnam-2009-b3-adjoin-to-each (element sets)
  (if (endp sets)
      nil
    (cons
     (cons element (car sets))
     (putnam-2009-b3-adjoin-to-each
      element (cdr sets)))))

(defun putnam-2009-b3-powerset (carrier)
  (if (endp carrier)
      (list nil)
    (let ((tail-powerset
           (putnam-2009-b3-powerset (cdr carrier))))
      (append
       tail-powerset
       (putnam-2009-b3-adjoin-to-each
        (car carrier) tail-powerset)))))

;; FIRST and every element of REMAINING belong to SUBSET. When their sum is
;; even, ACL2's exact rational division by two is the integer average from the
;; source statement.
(defun putnam-2009-b3-closed-with-first-p
    (first remaining subset)
  (if (endp remaining)
      t
    (and
     (implies
      (equal (mod (+ first (car remaining)) 2) 0)
      (member-equal
       (/ (+ first (car remaining)) 2)
       subset))
     (putnam-2009-b3-closed-with-first-p
      first (cdr remaining) subset))))

(defun putnam-2009-b3-mediocre-elements-p
    (remaining subset)
  (if (endp remaining)
      t
    (and
     (putnam-2009-b3-closed-with-first-p
      (car remaining) subset subset)
     (putnam-2009-b3-mediocre-elements-p
      (cdr remaining) subset))))

(defun putnam-2009-b3-mediocre-p (subset)
  (putnam-2009-b3-mediocre-elements-p subset subset))

(defun putnam-2009-b3-count-mediocre-subsets (subsets)
  (if (endp subsets)
      0
    (+
     (if (putnam-2009-b3-mediocre-p (car subsets))
         1
       0)
     (putnam-2009-b3-count-mediocre-subsets
      (cdr subsets)))))

(defun putnam-2009-b3-a (n)
  (if (natp n)
      (putnam-2009-b3-count-mediocre-subsets
       (putnam-2009-b3-powerset
        (putnam-2009-b3-one-through n)))
    0))

;; For positive n, any k>=1 satisfying n=2^k-1 also satisfies k<=n.
;; This finite search is therefore exactly the source existential quantifier.
(defun putnam-2009-b3-solution-through-k-p (n k)
  (declare (xargs :measure (nfix k)))
  (if (or (not (integerp n))
          (not (natp k))
          (zp k))
      nil
    (or
     (equal n (- (expt 2 k) 1))
     (putnam-2009-b3-solution-through-k-p
      n (- k 1)))))

(defun putnam-2009-b3-solution-member-p (n)
  (and
   (integerp n)
   (< 0 n)
   (putnam-2009-b3-solution-through-k-p n n)))

;; The ACL2 argument N supplies the universal integer quantifier needed for
;; extensional equality of the two sets in the source theorem.
(defun putnambench-putnam-2009-b3-statement (n)
  (implies
   (integerp n)
   (iff
    (and
     (< 0 n)
     (equal
      (+
       (-
        (putnam-2009-b3-a (+ n 2))
        (* 2 (putnam-2009-b3-a (+ n 1))))
       (putnam-2009-b3-a n))
      1))
    (putnam-2009-b3-solution-member-p n))))

(value-triple :itpeval-statement-checked)
:q
