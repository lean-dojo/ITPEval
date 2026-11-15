;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2017_odd_even_sort_rearranging_Top_my_swapqtvc: swapping
;; an earlier larger entry with a later smaller entry in an integer array
;; preserves the exchange relation and strictly decreases its entropy sum.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite lists of ACL2 integers represent the source's finite arrays
;; of mathematical integers without restricting either integer domain.

(defun odd-even-swap-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (odd-even-swap-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Int.toNat maps every negative integer to zero.  The source lookup is total
;; and returns the inhabited integer default zero outside the finite list.

(defun odd-even-swap-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun odd-even-swap-nth-int (xs index)
  (let ((natural-index
         (odd-even-swap-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      0)))

;; Source List.set changes an in-range position and leaves the list unchanged
;; when the natural index is out of range.

(defun odd-even-swap-list-set (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (odd-even-swap-list-set
        (cdr xs)
        (- index 1)
        value)))))

;; This is the source ArraySwap exchange relation.  Both replacement values
;; are read from OLD, so NEW is exactly OLD with FIRST and SECOND exchanged.

(defun odd-even-swap-array-exchange-p
    (old new first second)
  (equal
   new
   (odd-even-swap-list-set
    (odd-even-swap-list-set
     old
     (odd-even-swap-int-to-nat first)
     (odd-even-swap-nth-int old second))
    (odd-even-swap-int-to-nat second)
    (odd-even-swap-nth-int old first))))

;; Traversing with INDEX computes exactly
;; sum_{INDEX <= k < INDEX + len(XS)} k * (M - XS[k]).

(defun odd-even-swap-entropy-from (xs m index)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      0
    (+
     (* index (- m (car xs)))
     (odd-even-swap-entropy-from
      (cdr xs) m (+ index 1)))))

(defun odd-even-swap-entropy (xs m)
  (odd-even-swap-entropy-from xs m 0))

;; Preserve the source universal quantifier over every same-length integer
;; array satisfying the exchange relation, including the repeated exchange
;; conjunct in the generated verification condition.

(defun-sk odd-even-swap-all-exchange-results-p
    (old first second m)
  (forall (new)
    (implies
     (odd-even-swap-integer-list-p new)
     (implies
      (equal (len new) (len old))
      (implies
       (odd-even-swap-array-exchange-p
        old new first second)
       (and
        (odd-even-swap-array-exchange-p
         old new first second)
        (<
         (odd-even-swap-entropy new m)
         (odd-even-swap-entropy old m))))))))

;; This predicate is the complete unproved verification condition.

(defun
  ntp4vc-pearl-verifythis-2017-odd-even-sort-rearranging-top-my-swapqtvc-statement
  (array later earlier m)
  (implies
   (and
    (odd-even-swap-integer-list-p array)
    (integerp later)
    (integerp earlier)
    (integerp m)
    (<
     (odd-even-swap-nth-int array later)
     (odd-even-swap-nth-int array earlier))
    (<= 0 earlier)
    (< earlier later)
    (< later (len array)))
   (and
    (<= 0 earlier)
    (< earlier (len array))
    (<= 0 later)
    (< later (len array))
    (odd-even-swap-all-exchange-results-p
     array earlier later m))))

(value-triple :itpeval-statement-checked)
:q
