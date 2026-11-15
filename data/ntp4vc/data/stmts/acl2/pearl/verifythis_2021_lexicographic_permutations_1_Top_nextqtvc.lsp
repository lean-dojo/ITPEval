;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2021_lexicographic_permutations_1_Top_nextqtvc:
;; the complete verification condition for computing the immediate next
;; lexicographic permutation of an integer sequence. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Why3 finite sequences of mathematical integers are represented exactly by
;; proper ACL2 lists whose entries are unbounded ACL2 integers.

(defun lp-next-int-list-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (integerp (car s))
       (lp-next-int-list-p (cdr s)))
    (equal s nil)))

;; Why3/Lean exported indexing first maps an integer through Int.toNat and then
;; uses the inhabited integer default zero outside the finite sequence.

(defun lp-next-read-nat (index s)
  (declare (xargs :measure (nfix index)))
  (if (and
       (natp index)
       (< 0 index)
       (consp s))
      (lp-next-read-nat (- index 1) (cdr s))
    (if (consp s) (car s) 0)))

(defun lp-next-read (s index)
  (lp-next-read-nat (nfix index) s))

;; The source array-to-sequence operation is extensionally the identity under
;; this bijective list representation.

(defun lp-next-to-seq (a)
  a)

(defun lp-next-count (value s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (+ (if (equal value (car s)) 1 0)
         (lp-next-count value (cdr s)))
    0))

(defun-sk lp-next-same-counts-p (left right)
  (forall (value)
    (implies
     (integerp value)
     (equal
      (lp-next-count value left)
      (lp-next-count value right)))))

(defun lp-next-permutation-p (left right)
  (and
   (lp-next-int-list-p left)
   (lp-next-int-list-p right)
   (equal (len left) (len right))
   (lp-next-same-counts-p left right)))

(defun-sk lp-next-prefix-equal-before-p (left right bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index bound))
      (equal
       (lp-next-read left index)
       (lp-next-read right index))))))

(defun-sk lp-next-lex-less-p (left right)
  (exists (index)
    (and
     (integerp index)
     (equal (len left) (len right))
     (< 0 (len right))
     (<= 0 index)
     (< index (len left))
     (lp-next-prefix-equal-before-p left right index)
     (<
      (lp-next-read left index)
      (lp-next-read right index)))))

(defun-sk lp-next-descending-order-p (s lo hi)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index))
     (implies
      (and
       (<= lo left-index)
       (<= left-index right-index)
       (< right-index hi))
      (<=
       (lp-next-read s right-index)
       (lp-next-read s left-index))))))

(defun lp-next-descending-p (s lo hi)
  (and
   (lp-next-int-list-p s)
   (integerp lo)
   (integerp hi)
   (<= 0 lo)
   (<= lo hi)
   (<= hi (len s))
   (lp-next-descending-order-p s lo hi)))

(defun-sk lp-next-equal-before-p (left right bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index bound))
      (equal
       (lp-next-read left index)
       (lp-next-read right index))))))

(defun-sk lp-next-at-most-after-p (a lower n value)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (< lower index)
       (< index n))
      (<= (lp-next-read a index) value)))))

(defun-sk lp-next-unchanged-except-p (new old first second)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len new))
       (not (equal index first))
       (not (equal index second)))
      (equal
       (lp-next-read new index)
       (lp-next-read old index))))))

(defun lp-next-swap-relation-p (new old first second)
  (and
   (lp-next-int-list-p new)
   (equal (len new) (len old))
   (equal
    (lp-next-read new first)
    (lp-next-read old second))
   (equal
    (lp-next-read new second)
    (lp-next-read old first))
   (lp-next-unchanged-except-p new old first second)
   (lp-next-permutation-p
    (lp-next-to-seq new)
    (lp-next-to-seq old))))

(defun-sk lp-next-mirror-same-p (a start n distance)
  (forall (offset)
    (implies
     (integerp offset)
     (implies
      (and
       (< 0 offset)
       (< offset distance))
      (and
       (equal
        (lp-next-read a (+ start offset))
        (lp-next-read a (- n offset)))
       (equal
        (lp-next-read a (- n offset))
        (lp-next-read a (+ start offset))))))))

(defun-sk lp-next-interval-equal-p (left right lo hi)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lo index)
       (<= index hi))
      (equal
       (lp-next-read left index)
       (lp-next-read right index))))))

(defun-sk lp-next-mirror-from-p (new old start n distance)
  (forall (offset)
    (implies
     (integerp offset)
     (implies
      (and
       (< 0 offset)
       (< offset distance))
      (and
       (equal
        (lp-next-read new (+ start offset))
        (lp-next-read old (- n offset)))
       (equal
        (lp-next-read new (- n offset))
        (lp-next-read old (+ start offset))))))))

(defun-sk lp-next-copy-range-p (left right lo hi)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lo index)
       (< index hi))
      (equal
       (lp-next-read left index)
       (lp-next-read right index))))))

(defun-sk lp-next-copy-progress-p (left right lo o6)
  (forall (limit)
    (implies
     (integerp limit)
     (implies
      (and
       (<= lo limit)
       (<= limit o6)
       (lp-next-copy-range-p left right lo limit))
      (and
       (equal
        (lp-next-read left limit)
        (lp-next-read right limit))
       (lp-next-copy-range-p
        left right lo (+ limit 1)))))))

(defun lp-next-copy-loop-condition-p (left right i0 n)
  (let*
      ((o6 (- n 1))
       (o7 (+ i0 1)))
    (and
     (implies
      (<= o7 (+ o6 1))
      (and
       (lp-next-copy-range-p left right (+ i0 1) o7)
       (lp-next-copy-progress-p left right o7 o6)
       (not
        (lp-next-copy-range-p
         left right (+ i0 1) (+ o6 1)))))
     (not (< (+ o6 1) o7)))))

(defun-sk lp-next-to-seq-pointwise-p (a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len (lp-next-to-seq a))))
      (equal
       (lp-next-read (lp-next-to-seq a) index)
       (lp-next-read a index))))))

(defun lp-next-to-seq-spec-p (a)
  (and
   (equal (len (lp-next-to-seq a)) (len a))
   (lp-next-to-seq-pointwise-p a)))

(defun lp-next-is-next-contradiction-p
    (p a a2 i0 x z n)
  (let ((value (lp-next-read p i0)))
    (if (equal value x)
        (lp-next-copy-loop-condition-p
         p (lp-next-to-seq a) i0 n)
      (and
       (equal value z)
       (implies
        (lp-next-to-seq-spec-p a2)
        (lp-next-copy-loop-condition-p
         p (lp-next-to-seq a2) i0 n))))))

(defun-sk lp-next-no-intermediate-proof-p
    (a a0 a2 i0 x z n)
  (forall (p)
    (implies
     (lp-next-int-list-p p)
     (implies
      (and
       (lp-next-permutation-p p a0)
       (lp-next-lex-less-p (lp-next-to-seq a) p)
       (lp-next-lex-less-p p (lp-next-to-seq a2)))
      (lp-next-is-next-contradiction-p
       p a a2 i0 x z n)))))

(defun-sk lp-next-no-between-p (a a0 a2)
  (forall (p)
    (implies
     (lp-next-int-list-p p)
     (not
      (and
       (lp-next-permutation-p p a0)
       (lp-next-lex-less-p (lp-next-to-seq a) p)
       (lp-next-lex-less-p
        p (lp-next-to-seq a2)))))))

(defun-sk lp-next-final-minimality-p (a a0 a2)
  (forall (p)
    (implies
     (lp-next-int-list-p p)
     (implies
      (lp-next-permutation-p p a0)
      (not
       (and
        (lp-next-lex-less-p (lp-next-to-seq a) p)
        (lp-next-lex-less-p
         p (lp-next-to-seq a2))))))))

(defun lp-next-final-conclusion-p (a a0 a2)
  (implies
   (lp-next-no-between-p a a0 a2)
   (and
    (lp-next-permutation-p
     (lp-next-to-seq a2) a0)
    (lp-next-lex-less-p
     (lp-next-to-seq a)
     (lp-next-to-seq a2))
    (lp-next-final-minimality-p a a0 a2))))

(defun lp-next-a3-conclusion-p
    (a a0 a1 a3 i0 i1 j1 z n)
  (and
   (<= 0 (- j1 i1))
   (<
    (- (- j1 1) (+ i1 1))
    (- j1 i1))
   (< i0 (+ i1 1))
   (< i0 (- j1 1))
   (< (- j1 1) n)
   (lp-next-permutation-p
    (lp-next-to-seq a3) a0)
   (lp-next-equal-before-p a3 a i0)
   (equal (lp-next-read a3 i0) z)
   (equal
    (- (+ i1 1) i0)
    (- n (- j1 1)))
   (lp-next-interval-equal-p
    a3 a1 (+ i1 1) (- j1 1))
   (lp-next-mirror-from-p
    a3 a1 i0 n (- (+ i1 1) i0))))

(defun-sk lp-next-all-a3-p
    (a a0 a1 a2 i0 i1 j1 z n)
  (forall (a3)
    (implies
     (lp-next-int-list-p a3)
     (implies
      (lp-next-swap-relation-p a3 a2 i1 j1)
      (lp-next-a3-conclusion-p
       a a0 a1 a3 i0 i1 j1 z n)))))

(defun lp-next-a2-step-p
    (a a0 a1 a2 i0 i1 j1 x z n)
  (if (< i1 j1)
      (and
       (<= 0 i1)
       (< i1 (len a2))
       (<= 0 j1)
       (< j1 (len a2))
       (lp-next-all-a3-p
        a a0 a1 a2 i0 i1 j1 z n))
    (and
     (lp-next-no-intermediate-proof-p
      a a0 a2 i0 x z n)
     (lp-next-final-conclusion-p a a0 a2))))

(defun-sk lp-next-all-a2-p
    (a a0 a1 i0 x z n)
  (forall (j1 i1 a2)
    (implies
     (and
      (integerp j1)
      (integerp i1)
      (lp-next-int-list-p a2))
     (implies
      (and
       (equal (len a2) (len a1))
       (< i0 i1)
       (< i0 j1)
       (< j1 n)
       (lp-next-permutation-p
        (lp-next-to-seq a2) a0)
       (lp-next-equal-before-p a2 a i0)
       (equal (lp-next-read a2 i0) z)
       (equal (- i1 i0) (- n j1))
       (lp-next-interval-equal-p a2 a1 i1 j1)
       (lp-next-mirror-from-p
        a2 a1 i0 n (- i1 i0)))
      (lp-next-a2-step-p
       a a0 a1 a2 i0 i1 j1 x z n)))))

(defun lp-next-a1-conclusion-p
    (a a0 a1 i0 i x z n)
  (and
   (< i0 i)
   (< i0 (- n 1))
   (< (- n 1) n)
   (lp-next-permutation-p
    (lp-next-to-seq a1) a0)
   (lp-next-equal-before-p a1 a i0)
   (equal (lp-next-read a1 i0) z)
   (equal (- i i0) (- n (- n 1)))
   (lp-next-mirror-same-p
    a1 i0 n (- i i0))
   (lp-next-all-a2-p
    a a0 a1 i0 x z n)))

(defun-sk lp-next-all-a1-p
    (a a0 i0 i j x z n)
  (forall (a1)
    (implies
     (lp-next-int-list-p a1)
     (implies
      (lp-next-swap-relation-p
       a1 a (- i 1) j)
      (lp-next-a1-conclusion-p
       a a0 a1 i0 i x z n)))))

(defun lp-next-j-step-p
    (a a0 i0 i j x n)
  (let ((o4 (- i 1)))
    (and
     (<= 0 o4)
     (< o4 (len a))
     (<= 0 j)
     (< j (len a))
     (if (<=
          (lp-next-read a j)
          (lp-next-read a o4))
         (and
          (<= 0 j)
          (< (- j 1) j)
          (<= i (- j 1))
          (< (- j 1) n)
          (lp-next-at-most-after-p
           a (- j 1) n x))
       (let ((z (lp-next-read a j)))
         (and
          (<= 0 j)
          (< j (len a))
          (<= 0 (- i 1))
          (< (- i 1) (len a))
          (<= 0 j)
          (< j (len a))
          (lp-next-all-a1-p
           a a0 i0 i j x z n)))))))

(defun-sk lp-next-all-j-p
    (a a0 i0 i x n)
  (forall (j)
    (implies
     (integerp j)
     (implies
      (and
       (<= i j)
       (< j n)
       (lp-next-at-most-after-p a j n x))
      (lp-next-j-step-p
       a a0 i0 i j x n)))))

(defun lp-next-positive-search-p
    (a a0 i n)
  (let*
      ((i0 (- i 1))
       (x (lp-next-read a i0))
       (o3 (- n 1)))
    (and
     (<= 0 i0)
     (< i0 (len a))
     (<= i o3)
     (< o3 n)
     (lp-next-at-most-after-p a o3 n x)
     (lp-next-all-j-p
      a a0 i0 i x n))))

(defun-sk lp-next-last-permutation-p (a a0)
  (forall (p)
    (implies
     (lp-next-int-list-p p)
     (implies
      (lp-next-permutation-p p a0)
      (not
       (lp-next-lex-less-p
        (lp-next-to-seq a) p))))))

(defun lp-next-false-branch-p (a a0 i n)
  (if (<= i 0)
      (and
       (lp-next-permutation-p
        (lp-next-to-seq a) a0)
       (lp-next-last-permutation-p a a0))
    (lp-next-positive-search-p a a0 i n)))

(defun lp-next-true-branch-p (a i n)
  (and
   (<= 0 i)
   (< (- i 1) i)
   (<= -1 (- i 1))
   (< (- i 1) n)
   (or
    (and
     (equal (- i 1) -1)
     (equal n 0))
    (and
     (<= 0 (- i 1))
     (lp-next-descending-p
      (lp-next-to-seq a)
      (- i 1)
      n)))))

(defun lp-next-i-conclusion-p (a a0 i n)
  (and
   (implies
    (< 0 i)
    (and
     (<= 0 i)
     (< i (len a))
     (<= 0 (- i 1))
     (< (- i 1) (len a))))
   (if (and
        (< 0 i)
        (<=
         (lp-next-read a i)
         (lp-next-read a (- i 1))))
       (lp-next-true-branch-p a i n)
     (lp-next-false-branch-p
      a a0 i n))))

(defun-sk lp-next-all-i-p (a a0 n)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= -1 i)
       (< i n)
       (or
        (and
         (equal i -1)
         (equal n 0))
        (and
         (<= 0 i)
         (lp-next-descending-p
          (lp-next-to-seq a) i n))))
      (lp-next-i-conclusion-p
       a a0 i n)))))

(defun lp-next-vc-conclusion-p (a a0)
  (let*
      ((n (len a))
       (o1 (- n 1)))
    (and
     (<= -1 o1)
     (< o1 n)
     (or
      (and
       (equal o1 -1)
       (equal n 0))
      (and
       (<= 0 o1)
       (lp-next-descending-p
        (lp-next-to-seq a) o1 n)))
     (lp-next-all-i-p a a0 n))))

(defun-sk
    ntp4vc-verifythis-2021-lexicographic-permutations-1-top-nextqtvc-statement
    ()
  (forall (a a0)
    (implies
     (and
      (lp-next-int-list-p a)
      (lp-next-int-list-p a0))
     (implies
      (and
       (equal (len a) (len a0))
       (lp-next-permutation-p
        (lp-next-to-seq a) a0))
      (lp-next-vc-conclusion-p a a0)))))

(value-triple :itpeval-statement-checked)
:q
