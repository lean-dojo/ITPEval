;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/hillel_challenge_FulcrumNoOverflow_fulcrumqtvc: the verification
;; condition for signed 32-bit array summation, fulcrum minimization loop
;; invariants, and absence of overflow in the abstract big-integer encoding.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A 32-bit word is represented by its unsigned value.  FNOF-SINT32 is the
;; exact two's-complement signed interpretation used by the source BitVec.

(defun fnof-word32-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 4294967296)))

(defun fnof-sint32 (word)
  (if (< word 2147483648)
      word
    (- word 4294967296)))

(defun fnof-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

;; Conservative interfaces retain the arbitrary source carrier BIG and the
;; opaque ARRAY32 carrier.  Their complete typing and specification laws used
;; by the verification condition are explicit hypotheses below.

(defstub fnof-big-p (object) t)
(defstub fnof-big-q (object) t)
(defstub fnof-big-r (object) t)
(defstub fnof-big-v (object) t)
(defstub fnof-big-zero () t)

(defstub fnof-array32-p (object) t)
(defstub fnof-array32-length (array) t)
(defstub fnof-array32-elt (array index) t)

(defun fnof-big-invariant-p (object)
  (and
   (<= -2147483648
       (fnof-sint32 (fnof-big-q object)))
   (<= (fnof-sint32 (fnof-big-q object))
       2147483647)
   (<= 0
       (fnof-sint32 (fnof-big-r object)))
   (<= (fnof-sint32 (fnof-big-r object))
       2147483647)
   (equal
    (fnof-big-v object)
    (+
     (* (fnof-sint32 (fnof-big-q object))
        2147483648)
     (fnof-sint32 (fnof-big-r object))))))

(defun-sk fnof-big-inhabited-p ()
  (exists (object)
    (fnof-big-p object)))

(defun-sk fnof-big-type-and-invariant-law-p ()
  (forall (object)
    (implies
     (fnof-big-p object)
     (and
      (fnof-word32-p (fnof-big-q object))
      (fnof-word32-p (fnof-big-r object))
      (integerp (fnof-big-v object))
      (fnof-big-invariant-p object)))))

(defun-sk fnof-big-injective-law-p ()
  (forall (left right)
    (implies
     (and
      (fnof-big-p left)
      (fnof-big-p right)
      (equal (fnof-big-q left)
             (fnof-big-q right))
      (equal (fnof-big-r left)
             (fnof-big-r right))
      (equal (fnof-big-v left)
             (fnof-big-v right)))
     (equal left right))))

(defun fnof-big-zero-law-p ()
  (and
   (fnof-big-p (fnof-big-zero))
   (equal (fnof-big-q (fnof-big-zero)) 0)
   (equal (fnof-big-r (fnof-big-zero)) 0)
   (equal (fnof-big-v (fnof-big-zero)) 0)))

(defun-sk fnof-array32-function-laws-p ()
  (forall (array index)
    (and
     (implies
      (fnof-array32-p array)
      (fnof-word32-p
       (fnof-array32-length array)))
     (implies
      (and
       (fnof-array32-p array)
       (integerp index))
      (fnof-word32-p
       (fnof-array32-elt array index))))))

(defun fnof-background-p ()
  (and
   (fnof-big-inhabited-p)
   (fnof-big-type-and-invariant-law-p)
   (fnof-big-injective-law-p)
   (fnof-big-zero-law-p)
   (fnof-array32-function-laws-p)))

;; This primitive recursion is the unique finite half-open interval sum
;; specified by Why3 int.Sum: SUM A L U is zero when U <= L and otherwise is
;; the sum of the signed array elements at L, ..., U-1.

(defun fnof-sum-count (array index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+
     (fnof-sint32
      (fnof-array32-elt array index))
     (fnof-sum-count
      array
      (+ index 1)
      (- count 1)))))

(defun fnof-sum (array lower upper)
  (if (and
       (integerp lower)
       (integerp upper))
      (fnof-sum-count
       array
       lower
       (nfix (- upper lower)))
    0))

(defun fnof-diff (array index)
  (abs
   (-
    (fnof-sum array 0 index)
    (fnof-sum
     array
     index
     (fnof-sint32
      (fnof-array32-length array))))))

(defun fnof-big-no-overflow-p (value)
  (and
   (<= (- (* 2147483648 2147483648))
       value)
   (<= value
       (- (* 2147483648 2147483648) 1))))

(defun-sk fnof-minimal-through-p
    (array best-value upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (<= index upper))
      (<= best-value
          (fnof-diff array index))))))

(defun-sk fnof-global-minimum-p
    (array best-index)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (<=
        index
        (fnof-sint32
         (fnof-array32-length array))))
      (<=
       (fnof-diff array best-index)
       (fnof-diff array index))))))

(defun fnof-updated-invariant-p
    (array next-index left right best-index bestd)
  (and
   (< 55 89)
   (equal
    (fnof-big-v left)
    (fnof-sum array 0 next-index))
   (equal
    (fnof-big-v right)
    (fnof-sum
     array
     next-index
     (fnof-sint32
      (fnof-array32-length array))))
   (<= 0 (fnof-sint32 best-index))
   (<= (fnof-sint32 best-index)
       next-index)
   (equal
    (fnof-big-v bestd)
    (fnof-diff
     array
     (fnof-sint32 best-index)))
   (fnof-minimal-through-p
    array
    (fnof-big-v bestd)
    next-index)))

(defun-sk fnof-better-branch-all-o5-p
    (array word i1 left right d bestd2)
  (forall (o5)
    (implies
     (fnof-word32-p o5)
     (implies
      (equal
       (fnof-sint32 o5)
       (+ (fnof-sint32 word) 1))
      (and
       (fnof-big-invariant-p d)
       (implies
        (and
         (equal (fnof-big-v d)
                (fnof-big-v bestd2))
         (equal (fnof-big-r d)
                (fnof-big-r bestd2))
         (equal (fnof-big-q d)
                (fnof-big-q bestd2)))
        (fnof-updated-invariant-p
         array
         (+ i1 1)
         left
         right
         o5
         bestd2)))))))

(defun-sk fnof-better-branch-all-bestd2-p
    (array word i1 left right d)
  (forall (bestd2)
    (implies
     (fnof-big-p bestd2)
     (and
      (fnof-int32-in-bounds-p
       (+ (fnof-sint32 word) 1))
      (fnof-better-branch-all-o5-p
       array word i1 left right d bestd2)))))

(defun fnof-after-d-p
    (array word i1 left right d bestd1 besti)
  (and
   (<= 0 (fnof-big-v d))
   (<= 0 (fnof-big-v bestd1))
   (if (< (fnof-big-v d)
          (fnof-big-v bestd1))
       (fnof-better-branch-all-bestd2-p
        array word i1 left right d)
     (fnof-updated-invariant-p
      array
      (+ i1 1)
      left
      right
      besti
      bestd1))))

(defun-sk fnof-all-d-p
    (array word i1 left right bestd1 besti)
  (forall (d)
    (implies
     (fnof-big-p d)
     (implies
      (equal
       (fnof-big-v d)
       (abs
        (-
         (fnof-big-v left)
         (fnof-big-v right))))
      (fnof-after-d-p
       array word i1 left right d bestd1 besti)))))

(defun-sk fnof-all-right-updates-p
    (array word i1 left right-before bestd1 besti element)
  (forall (right)
    (implies
     (fnof-big-p right)
     (implies
      (equal
       (fnof-big-v right)
       (-
        (fnof-big-v right-before)
        (fnof-sint32 element)))
      (and
       (fnof-big-no-overflow-p
        (abs
         (-
          (fnof-big-v left)
          (fnof-big-v right))))
       (fnof-all-d-p
        array word i1 left right bestd1 besti))))))

(defun-sk fnof-all-left-updates-p
    (array word i1 left-before right-before bestd1 besti element)
  (forall (left)
    (implies
     (fnof-big-p left)
     (implies
      (equal
       (fnof-big-v left)
       (+
        (fnof-big-v left-before)
        (fnof-sint32 element)))
      (and
       (<= 0 (fnof-sint32 word))
       (< (fnof-sint32 word)
          (fnof-sint32
           (fnof-array32-length array)))
       (fnof-big-no-overflow-p
        (-
         (fnof-big-v right-before)
         (fnof-sint32 element)))
       (fnof-all-right-updates-p
        array word i1 left right-before
        bestd1 besti element))))))

(defun fnof-second-loop-step-p
    (array word left right bestd1 besti)
  (let* ((i1 (fnof-sint32 word))
         (element
          (fnof-array32-elt array i1)))
    (and
     (<= 0 i1)
     (< i1
        (fnof-sint32
         (fnof-array32-length array)))
     (fnof-big-no-overflow-p
      (+
       (fnof-big-v left)
       (fnof-sint32 element)))
     (fnof-all-left-updates-p
      array word i1 left right
      bestd1 besti element))))

(defun fnof-second-loop-invariant-p
    (array word o2 left right bestd1 besti)
  (let ((i1 (fnof-sint32 word)))
    (and
     (<= 0 i1)
     (<= i1 (fnof-sint32 o2))
     (< 55 89)
     (equal
      (fnof-big-v left)
      (fnof-sum array 0 i1))
     (equal
      (fnof-big-v right)
      (fnof-sum
       array
       i1
       (fnof-sint32
        (fnof-array32-length array))))
     (<= 0 (fnof-sint32 besti))
     (<= (fnof-sint32 besti) i1)
     (equal
      (fnof-big-v bestd1)
      (fnof-diff array (fnof-sint32 besti)))
     (fnof-minimal-through-p
      array
      (fnof-big-v bestd1)
      i1))))

(defun-sk fnof-all-second-loop-iterations-p
    (array o2 left right bestd1 besti)
  (forall (word)
    (implies
     (fnof-word32-p word)
     (implies
      (fnof-second-loop-invariant-p
       array word o2 left right bestd1 besti)
      (fnof-second-loop-step-p
       array word left right bestd1 besti)))))

(defun fnof-second-loop-exit-obligation-p
    (array o2 left right bestd1 besti)
  (implies
   (and
    (< 55 89)
    (equal
     (fnof-big-v left)
     (fnof-sum
      array
      0
      (+ (fnof-sint32 o2) 1)))
    (equal
     (fnof-big-v right)
     (fnof-sum
      array
      (+ (fnof-sint32 o2) 1)
      (fnof-sint32
       (fnof-array32-length array))))
    (<= 0 (fnof-sint32 besti))
    (<= (fnof-sint32 besti)
        (+ (fnof-sint32 o2) 1))
    (equal
     (fnof-big-v bestd1)
     (fnof-diff array (fnof-sint32 besti)))
    (fnof-minimal-through-p
     array
     (fnof-big-v bestd1)
     (+ (fnof-sint32 o2) 1)))
   (and
    (<= 0 (fnof-sint32 besti))
    (<=
     (fnof-sint32 besti)
     (fnof-sint32
      (fnof-array32-length array)))
    (fnof-global-minimum-p
     array
     (fnof-sint32 besti)))))

(defun-sk fnof-all-second-loop-states-p
    (array o2)
  (forall (bestd1 besti left right)
    (implies
     (and
      (fnof-big-p bestd1)
      (fnof-word32-p besti)
      (fnof-big-p left)
      (fnof-big-p right))
     (and
      (fnof-all-second-loop-iterations-p
       array o2 left right bestd1 besti)
      (fnof-second-loop-exit-obligation-p
       array o2 left right bestd1 besti)))))

(defun fnof-second-loop-initial-p
    (array initial-right bestd)
  (and
   (< 55 89)
   (equal
    (fnof-big-v (fnof-big-zero))
    (fnof-sum array 0 0))
   (equal
    (fnof-big-v initial-right)
    (fnof-sum
     array
     0
     (fnof-sint32
      (fnof-array32-length array))))
   (<= 0 0)
   (equal
    (fnof-big-v bestd)
    (fnof-diff array 0))
   (fnof-minimal-through-p
    array
    (fnof-big-v bestd)
    0)))

(defun fnof-negative-second-loop-result-p (array)
  (and
   (<= 0 0)
   (<=
    0
    (fnof-sint32
     (fnof-array32-length array)))
   (fnof-global-minimum-p array 0)))

(defun-sk fnof-all-o2-p
    (array initial-right bestd)
  (forall (o2)
    (implies
     (fnof-word32-p o2)
     (implies
      (equal
       (fnof-sint32 o2)
       (-
        (fnof-sint32
         (fnof-array32-length array))
        1))
      (and
       (implies
        (<= 0 (+ (fnof-sint32 o2) 1))
        (and
         (fnof-second-loop-initial-p
          array initial-right bestd)
         (fnof-all-second-loop-states-p
          array o2)))
       (implies
        (< (+ (fnof-sint32 o2) 1) 0)
        (fnof-negative-second-loop-result-p
         array)))))))

(defun fnof-after-first-loop-bestd-p
    (array initial-right bestd)
  (and
   (fnof-int32-in-bounds-p
    (-
     (fnof-sint32
      (fnof-array32-length array))
     1))
   (fnof-all-o2-p array initial-right bestd)))

(defun-sk fnof-all-bestd-p
    (array initial-right)
  (forall (bestd)
    (implies
     (fnof-big-p bestd)
     (implies
      (equal
       (fnof-big-v bestd)
       (abs
        (-
         (fnof-big-v (fnof-big-zero))
         (fnof-big-v initial-right))))
      (fnof-after-first-loop-bestd-p
       array initial-right bestd)))))

(defun fnof-after-first-loop-p
    (array initial-right)
  (and
   (fnof-big-no-overflow-p
    (abs
     (-
      (fnof-big-v (fnof-big-zero))
      (fnof-big-v initial-right))))
   (fnof-all-bestd-p array initial-right)))

(defun-sk fnof-all-first-loop-right-updates-p
    (array word right element)
  (forall (next-right)
    (implies
     (fnof-big-p next-right)
     (implies
      (equal
       (fnof-big-v next-right)
       (+
        (fnof-big-v right)
        (fnof-sint32 element)))
      (and
       (< 55 89)
       (equal
        (fnof-big-v next-right)
        (fnof-sum
         array
         0
         (+ (fnof-sint32 word) 1))))))))

(defun fnof-first-loop-step-p
    (array word right)
  (let* ((i1 (fnof-sint32 word))
         (element
          (fnof-array32-elt array i1)))
    (and
     (<= 0 i1)
     (< i1
        (fnof-sint32
         (fnof-array32-length array)))
     (fnof-big-no-overflow-p
      (+
       (fnof-big-v right)
       (fnof-sint32 element)))
     (fnof-all-first-loop-right-updates-p
      array word right element))))

(defun-sk fnof-all-first-loop-iterations-p
    (array o1 right)
  (forall (word)
    (implies
     (fnof-word32-p word)
     (let ((i1 (fnof-sint32 word)))
       (implies
        (and
         (<= 0 i1)
         (<= i1 (fnof-sint32 o1))
         (< 55 89)
         (equal
          (fnof-big-v right)
          (fnof-sum array 0 i1)))
        (fnof-first-loop-step-p
         array word right))))))

(defun fnof-first-loop-exit-obligation-p
    (array o1 right)
  (implies
   (and
    (< 55 89)
    (equal
     (fnof-big-v right)
     (fnof-sum
      array
      0
      (+ (fnof-sint32 o1) 1))))
   (fnof-after-first-loop-p array right)))

(defun-sk fnof-all-first-loop-states-p
    (array o1)
  (forall (right)
    (implies
     (fnof-big-p right)
     (and
      (fnof-all-first-loop-iterations-p
       array o1 right)
      (fnof-first-loop-exit-obligation-p
       array o1 right)))))

(defun fnof-nonnegative-first-loop-p
    (array o1)
  (and
   (< 55 89)
   (equal
    (fnof-big-v (fnof-big-zero))
    (fnof-sum array 0 0))
   (fnof-all-first-loop-states-p
    array o1)))

(defun-sk fnof-all-o1-p (array)
  (forall (o1)
    (implies
     (fnof-word32-p o1)
     (implies
      (equal
       (fnof-sint32 o1)
       (-
        (fnof-sint32
         (fnof-array32-length array))
        1))
      (and
       (implies
        (<= 0 (+ (fnof-sint32 o1) 1))
        (fnof-nonnegative-first-loop-p
         array o1))
       (implies
        (< (+ (fnof-sint32 o1) 1) 0)
        (fnof-after-first-loop-p
         array
         (fnof-big-zero))))))))

(defun fnof-fulcrum-vc-conclusion-p (array)
  (and
   (fnof-int32-in-bounds-p
    (-
     (fnof-sint32
      (fnof-array32-length array))
     1))
   (fnof-all-o1-p array)))

(defun
  ntp4vc-pearl-hillel-challenge-fulcrumnooverflow-fulcrumqtvc-statement
  (array)
  (implies
   (and
    (fnof-background-p)
    (fnof-array32-p array)
    (<
     (fnof-sint32
      (fnof-array32-length array))
     (fnof-sint32 2147483647)))
   (fnof-fulcrum-vc-conclusion-p array)))

(value-triple :itpeval-statement-checked)
:q
