;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/euler_sieve_EulerSieveImpl_set_markqtvc: the signed 63-bit
;; verification condition for marking an odd Euler-sieve index and updating
;; its compressed array representation. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Signed 63-bit words are represented by their signed integer values.  This
;; interval representation is bijective, so word equality is integer equality.

(defun es-set-mark-bv63-p (x)
  (and
   (integerp x)
   (<= (- (expt 2 62)) x)
   (< x (expt 2 62))))

(defun es-set-mark-int63-in-bounds-p (x)
  (es-set-mark-bv63-p x))

(defun es-set-mark-int-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (es-set-mark-int-list-p (cdr xs)))))

(defun es-set-mark-bool-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (booleanp (car xs))
     (es-set-mark-bool-list-p (cdr xs)))))

(defun es-set-mark-int-to-nat (x)
  (if (and (integerp x) (< x 0))
      0
    (nfix x)))

;; The source list lookup is total: integer lists default to zero and Boolean
;; lists default to false.

(defun es-set-mark-nth-int (i xs)
  (let ((value (nth (es-set-mark-int-to-nat i) xs)))
    (if (integerp value) value 0)))

(defun es-set-mark-nth-bool (i xs)
  (let ((value (nth (es-set-mark-int-to-nat i) xs)))
    (if (booleanp value) value nil)))

;; Source List.set leaves a list unchanged when its natural index is outside
;; the list.

(defun es-set-mark-list-set (xs index value)
  (if (< (nfix index) (len xs))
      (update-nth (nfix index) value xs)
    xs))

;; The machine quotient truncates toward zero.  Euclidean division and modulo
;; are used in the state invariant.

(defun es-set-mark-tdiv (numerator denominator)
  (if
      (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (let ((quotient
             (floor (abs numerator) (abs denominator))))
        (if
            (or
             (and (< numerator 0) (< 0 denominator))
             (and (< 0 numerator) (< denominator 0)))
            (- quotient)
          quotient))
    0))

(defun es-set-mark-ediv (numerator denominator)
  (if
      (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (floor numerator denominator)
    0))

(defun es-set-mark-emod (numerator denominator)
  (if
      (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (mod numerator denominator)
    0))

;; The array and Euler-sieve state types remain arbitrary nonempty types.
;; DEFSTUB supplies only conservative function interfaces; every typing,
;; invariant, and extensionality law is explicit in the statement context.

(defstub es-set-mark-array-p (x) t)
(defstub es-set-mark-array-elts (x) t)
(defstub es-set-mark-array-size (x) t)

(defstub es-set-mark-state-p (x) t)
(defstub es-set-mark-nexts (x) t)
(defstub es-set-mark-marked (x) t)
(defstub es-set-mark-arr (x) t)
(defstub es-set-mark-max (x) t)
(defstub es-set-mark-max-arr (x) t)

(defun-sk es-set-mark-array-elements-in-bounds-p (a)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len (es-set-mark-array-elts a))))
     (es-set-mark-int63-in-bounds-p
      (es-set-mark-nth-int
       i
       (es-set-mark-array-elts a))))))

(defun es-set-mark-array-invariant-p (a)
  (and
   (integerp (es-set-mark-array-size a))
   (es-set-mark-int-list-p (es-set-mark-array-elts a))
   (<= 0 (es-set-mark-array-size a))
   (equal
    (es-set-mark-array-size a)
    (len (es-set-mark-array-elts a)))
   (<=
    (len (es-set-mark-array-elts a))
    (- (expt 2 62) 1))
   (es-set-mark-array-elements-in-bounds-p a)))

(defun-sk es-set-mark-array-nonempty-p ()
  (exists (a)
    (es-set-mark-array-p a)))

(defun-sk es-set-mark-array-context-p ()
  (forall (a)
    (implies
     (es-set-mark-array-p a)
     (es-set-mark-array-invariant-p a))))

;; EulerSieveSpec.inv_nexts and all_eliminated_marked.

(defun-sk es-set-mark-inv-nexts-p (nexts n)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i n))
     (and
      (< i (es-set-mark-nth-int i nexts))
      (<= (es-set-mark-nth-int i nexts) n)))))

(defun-sk es-set-mark-eliminated-between-p (marked nexts i)
  (forall (j)
    (implies
     (and
      (integerp j)
      (< i j)
      (< j (es-set-mark-nth-int i nexts)))
     (equal (es-set-mark-nth-bool j marked) t))))

(defun-sk es-set-mark-all-eliminated-index-p (marked nexts)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len marked)))
     (es-set-mark-eliminated-between-p marked nexts i))))

(defun es-set-mark-all-eliminated-marked-p (marked nexts)
  (and
   (equal (len marked) (len nexts))
   (es-set-mark-all-eliminated-index-p marked nexts)))

;; Universal indexed clauses of the source state invariant, parameterized by
;; the five state fields so the same exact predicate can describe an updated
;; state in the verification condition.

(defun-sk es-set-mark-invariant-even-p (marked max)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 3 i)
      (<= i max)
      (equal (es-set-mark-emod i 2) 0))
     (equal (es-set-mark-nth-bool i marked) t))))

(defun-sk es-set-mark-invariant-odd-p (nexts max)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 3 i)
      (< i (- max 1))
      (equal (es-set-mark-emod i 2) 1))
     (or
      (equal
       (es-set-mark-emod
        (es-set-mark-nth-int i nexts)
        2)
       1)
      (equal
       (es-set-mark-nth-int i nexts)
       (+ max 1))))))

(defun-sk es-set-mark-invariant-range-p (arr max max-arr)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i max-arr))
     (and
      (<=
       (- (+ max 1))
       (es-set-mark-nth-int
        i
        (es-set-mark-array-elts arr)))
      (<=
       (es-set-mark-nth-int
        i
        (es-set-mark-array-elts arr))
       (+ max 1))))))

(defun-sk es-set-mark-invariant-sign-p (marked arr max-arr)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i max-arr))
     (iff
      (equal
       (es-set-mark-nth-bool
        (+ (* 2 i) 1)
        marked)
       t)
      (<
       (es-set-mark-nth-int
        i
        (es-set-mark-array-elts arr))
       0)))))

(defun-sk es-set-mark-invariant-unmarked-p
    (nexts marked arr max-arr)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i max-arr)
      (not
       (equal
        (es-set-mark-nth-bool
         (+ (* 2 i) 1)
         marked)
        t)))
     (equal
      (es-set-mark-nth-int
       i
       (es-set-mark-array-elts arr))
      (es-set-mark-nth-int
       (+ (* 2 i) 1)
       nexts)))))

(defun-sk es-set-mark-invariant-marked-p
    (nexts marked arr max-arr)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i max-arr)
      (equal
       (es-set-mark-nth-bool
        (+ (* 2 i) 1)
        marked)
       t))
     (equal
      (es-set-mark-nth-int
       i
       (es-set-mark-array-elts arr))
      (-
       (es-set-mark-nth-int
        (+ (* 2 i) 1)
        nexts))))))

(defun-sk es-set-mark-invariant-between-p (arr i)
  (forall (j)
    (implies
     (and
      (integerp j)
      (< i j)
      (<
       j
       (es-set-mark-ediv
        (abs
         (es-set-mark-nth-int
          i
          (es-set-mark-array-elts arr)))
        2)))
     (<
      (es-set-mark-nth-int
       j
       (es-set-mark-array-elts arr))
      0))))

(defun-sk es-set-mark-invariant-jump-p (arr max max-arr)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i max-arr))
     (and
      (<
       i
       (es-set-mark-ediv
        (abs
         (es-set-mark-nth-int
          i
          (es-set-mark-array-elts arr)))
        2))
      (<=
       (es-set-mark-ediv
        (abs
         (es-set-mark-nth-int
          i
          (es-set-mark-array-elts arr)))
        2)
       (+ max-arr 1))
      (<=
       (abs
        (es-set-mark-nth-int
         i
         (es-set-mark-array-elts arr)))
       (+ max 1))
      (es-set-mark-invariant-between-p arr i)))))

(defun es-set-mark-state-invariant-data-p
    (nexts marked arr max max-arr)
  (and
   (< max (- (expt 2 62) 1))
   (<= 3 max)
   (equal (len nexts) (len marked))
   (equal (len marked) (+ max 1))
   (equal
    (es-set-mark-ediv (- max 1) 2)
    max-arr)
   (equal
    (len (es-set-mark-array-elts arr))
    (+ max-arr 1))
   (es-set-mark-inv-nexts-p nexts (len nexts))
   (es-set-mark-all-eliminated-marked-p marked nexts)
   (es-set-mark-invariant-even-p marked max)
   (es-set-mark-invariant-odd-p nexts max)
   (equal
    (es-set-mark-nth-int max nexts)
    (+ max 1))
   (implies
    (equal (es-set-mark-emod (- max 1) 2) 0)
    (equal
     (es-set-mark-nth-int (- max 1) nexts)
     max))
   (implies
    (equal (es-set-mark-emod (- max 1) 2) 1)
    (equal
     (es-set-mark-nth-int (- max 1) nexts)
     (+ max 1)))
   (es-set-mark-invariant-range-p arr max max-arr)
   (es-set-mark-invariant-sign-p marked arr max-arr)
   (es-set-mark-invariant-unmarked-p
    nexts marked arr max-arr)
   (es-set-mark-invariant-marked-p
    nexts marked arr max-arr)
   (es-set-mark-invariant-jump-p arr max max-arr)))

(defun-sk es-set-mark-state-nonempty-p ()
  (exists (self)
    (es-set-mark-state-p self)))

(defun-sk es-set-mark-state-context-p ()
  (forall (self)
    (implies
     (es-set-mark-state-p self)
     (and
      (es-set-mark-int-list-p
       (es-set-mark-nexts self))
      (es-set-mark-bool-list-p
       (es-set-mark-marked self))
      (es-set-mark-array-p
       (es-set-mark-arr self))
      (es-set-mark-bv63-p
       (es-set-mark-max self))
      (es-set-mark-bv63-p
       (es-set-mark-max-arr self))
      (es-set-mark-state-invariant-data-p
       (es-set-mark-nexts self)
       (es-set-mark-marked self)
       (es-set-mark-arr self)
       (es-set-mark-max self)
       (es-set-mark-max-arr self))))))

(defun-sk es-set-mark-state-injective-context-p ()
  (forall (a b)
    (implies
     (and
      (es-set-mark-state-p a)
      (es-set-mark-state-p b)
      (equal
       (es-set-mark-nexts a)
       (es-set-mark-nexts b))
      (equal
       (es-set-mark-marked a)
       (es-set-mark-marked b))
      (equal
       (es-set-mark-arr a)
       (es-set-mark-arr b))
      (equal
       (es-set-mark-max a)
       (es-set-mark-max b))
      (equal
       (es-set-mark-max-arr a)
       (es-set-mark-max-arr b)))
     (equal a b))))

(defun es-set-mark-context-p ()
  (and
   (es-set-mark-array-nonempty-p)
   (es-set-mark-array-context-p)
   (es-set-mark-state-nonempty-p)
   (es-set-mark-state-context-p)
   (es-set-mark-state-injective-context-p)))

;; List.set's extensional postcondition from the source VC.

(defun-sk es-set-mark-other-indices-unchanged-p
    (old updated index)
  (forall (j)
    (implies
     (and
      (integerp j)
      (<= 0 j)
      (< j (len old))
      (not (equal j index)))
     (equal
      (es-set-mark-nth-bool j updated)
      (es-set-mark-nth-bool j old)))))

;; The final universally quantified state.  Its first conjunct is the exact
;; source invariant specialized to the updated marked list and chosen array;
;; the second conjunct is the source field-extensionality implication.

(defun-sk es-set-mark-all-result-states-p
    (t1 updated-arr updated-marked index)
  (forall (t2)
    (implies
     (es-set-mark-state-p t2)
     (and
      (es-set-mark-state-invariant-data-p
       (es-set-mark-nexts t1)
       updated-marked
       updated-arr
       (es-set-mark-max t1)
       (es-set-mark-max-arr t1))
      (implies
       (and
        (equal
         (es-set-mark-max-arr t1)
         (es-set-mark-max-arr t2))
        (equal
         (es-set-mark-max t1)
         (es-set-mark-max t2))
        (equal
         updated-arr
         (es-set-mark-arr t2))
        (equal
         updated-marked
         (es-set-mark-marked t2))
        (equal
         (es-set-mark-nexts t1)
         (es-set-mark-nexts t2)))
       (equal
        (es-set-mark-marked t2)
        (es-set-mark-list-set
         (es-set-mark-marked t1)
         (es-set-mark-int-to-nat index)
         t)))))))

(defun es-set-mark-marking-continuation-p
    (t1 updated-arr index)
  (let*
      ((old (es-set-mark-marked t1))
       (updated
        (es-set-mark-list-set
         old
         (es-set-mark-int-to-nat index)
         t)))
    (and
     (<= 0 index)
     (< index (len old))
     (implies
      (and
       (equal (len updated) (len old))
       (equal (es-set-mark-nth-bool index updated) t)
       (es-set-mark-other-indices-unchanged-p
        old updated index))
      (es-set-mark-all-result-states-p
       t1 updated-arr updated index)))))

;; Positive-array-entry branch: negate the compressed entry, update the
;; abstract array at x, then mark the original odd index.

(defun-sk es-set-mark-all-updated-arrays-p
    (t1 x negated index)
  (forall (updated-arr)
    (implies
     (es-set-mark-array-p updated-arr)
     (implies
      (and
       (equal
        (es-set-mark-array-size updated-arr)
        (es-set-mark-array-size
         (es-set-mark-arr t1)))
       (equal
        (es-set-mark-array-size updated-arr)
        (es-set-mark-array-size
         (es-set-mark-arr t1)))
       (equal
        (es-set-mark-array-elts updated-arr)
        (es-set-mark-list-set
         (es-set-mark-array-elts
          (es-set-mark-arr t1))
         (es-set-mark-int-to-nat x)
         negated)))
      (es-set-mark-marking-continuation-p
       t1 updated-arr index)))))

(defun-sk es-set-mark-all-negated-words-p
    (t1 x entry index)
  (forall (negated)
    (implies
     (and
      (es-set-mark-bv63-p negated)
      (equal negated (- entry)))
     (and
      (<= 0 x)
      (<
       x
       (len
        (es-set-mark-array-elts
         (es-set-mark-arr t1))))
      (es-set-mark-all-updated-arrays-p
       t1 x negated index)))))

(defun es-set-mark-positive-entry-continuation-p
    (t1 x entry index)
  (and
   (es-set-mark-int63-in-bounds-p (- entry))
   (es-set-mark-all-negated-words-p
    t1 x entry index)))

(defun-sk es-set-mark-all-positive-entries-p
    (t1 x index)
  (forall (entry)
    (implies
     (and
      (es-set-mark-bv63-p entry)
      (equal
       entry
       (es-set-mark-nth-int
        x
        (es-set-mark-array-elts
         (es-set-mark-arr t1)))))
     (es-set-mark-positive-entry-continuation-p
      t1 x entry index))))

(defun es-set-mark-entry-branch-p
    (t1 x entry index)
  (if (<= 0 entry)
      (and
       (<= 0 x)
       (<
        x
        (len
         (es-set-mark-array-elts
          (es-set-mark-arr t1))))
       (es-set-mark-all-positive-entries-p
        t1 x index))
    (es-set-mark-marking-continuation-p
     t1 (es-set-mark-arr t1) index)))

(defun-sk es-set-mark-all-entries-p (t1 x index)
  (forall (entry)
    (implies
     (and
      (es-set-mark-bv63-p entry)
      (equal
       entry
       (es-set-mark-nth-int
        x
        (es-set-mark-array-elts
         (es-set-mark-arr t1)))))
     (es-set-mark-entry-branch-p
      t1 x entry index))))

(defun es-set-mark-index-continuation-p (t1 x index)
  (and
   (<= 0 x)
   (<
    x
    (len
     (es-set-mark-array-elts
      (es-set-mark-arr t1))))
   (es-set-mark-all-entries-p t1 x index)))

(defun-sk es-set-mark-all-compressed-indices-p (t1 index)
  (forall (x)
    (implies
     (and
      (es-set-mark-bv63-p x)
      (equal
       x
       (es-set-mark-tdiv index 2)))
     (es-set-mark-index-continuation-p
      t1 x index))))

(defun ntp4vc-pearl-euler-sieve-eulersieveimpl-set-markqtvc-statement
    (index t1)
  (implies
   (and
    (es-set-mark-context-p)
    (es-set-mark-bv63-p index)
    (es-set-mark-state-p t1)
    (<= 0 index)
    (<= index (es-set-mark-max t1))
    (equal (es-set-mark-emod index 2) 1))
   (and
    (not (equal 2 0))
    (es-set-mark-int63-in-bounds-p
     (es-set-mark-tdiv index 2))
    (es-set-mark-all-compressed-indices-p
     t1 index))))

(value-triple :itpeval-statement-checked)
:q
