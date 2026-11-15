;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2024_challenge1_Top_smart_array_copy_0qtvc: the
;; verification condition for smart array copying by shuffled subsegments,
;; including permutation pairs, nested copy-loop invariants, and extensional
;; list-update conditions. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source array elements have one arbitrary inhabited type.  These
;; conservative interfaces represent that fixed type and its chosen default;
;; their required typing facts remain explicit in the statement predicate.

(defstub sac0-elt-p (value) t)
(defstub sac0-default-elt () t)

(defun sac0-elt-list-p (xs)
  (if (consp xs)
      (and
       (sac0-elt-p (car xs))
       (sac0-elt-list-p (cdr xs)))
    (equal xs nil)))

(defun sac0-integer-list-p (xs)
  (if (consp xs)
      (and
       (integerp (car xs))
       (sac0-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Why3 and the exports map a negative integer to natural index zero.

(defun sac0-int-to-nat (value)
  (if (and (integerp value)
           (< value 0))
      0
    (nfix value)))

;; Source list indexing is total through the inhabited element and integer
;; defaults.  In-range accesses agree with ordinary finite-list indexing.

(defun sac0-nth-elt (index xs)
  (let ((tail
         (nthcdr
          (sac0-int-to-nat index)
          xs)))
    (if (consp tail)
        (car tail)
      (sac0-default-elt))))

(defun sac0-nth-int (index xs)
  (let ((tail
         (nthcdr
          (sac0-int-to-nat index)
          xs)))
    (if (consp tail)
        (car tail)
      0)))

;; Unlike ACL2's update-nth, source List.set leaves an out-of-range list
;; unchanged.

(defun sac0-list-set-natural (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (sac0-list-set-natural
        (cdr xs)
        (- index 1)
        value)))))

(defun sac0-list-set-int (xs index value)
  (sac0-list-set-natural
   xs
   (sac0-int-to-nat index)
   value))

;; Permutation and inverse-permutation predicates.

(defun-sk sac0-permutation-range-p (l p)
  (forall i
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i l))
     (let ((p-at-i (sac0-nth-int i p)))
       (and
        (<= 0 p-at-i)
        (< p-at-i l))))))

(defun-sk sac0-permutation-distinct-p (l p)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j)
      (<= 0 i)
      (< i l)
      (<= 0 j)
      (< j l)
      (not (equal i j)))
     (not
      (equal
       (sac0-nth-int i p)
       (sac0-nth-int j p))))))

(defun sac0-permutation-p (l p)
  (and
   (integerp l)
   (sac0-integer-list-p p)
   (<= 0 l)
   (<= l (len p))
   (sac0-permutation-range-p l p)
   (sac0-permutation-distinct-p l p)))

(defun-sk sac0-permutation-inverses-p (l p invp)
  (forall i
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i l))
     (and
      (equal
       (sac0-nth-int
        (sac0-nth-int i invp)
        p)
       i)
      (equal
       (sac0-nth-int
        (sac0-nth-int i p)
        invp)
       i)))))

(defun sac0-permutation-pair-p (l p invp)
  (and
   (sac0-permutation-p l p)
   (sac0-permutation-p l invp)
   (sac0-permutation-inverses-p l p invp)))

;; Array-chunk and copied-chunk predicates.

(defun sac0-valid-chunk-p (array offset length)
  (and
   (sac0-elt-list-p array)
   (integerp offset)
   (integerp length)
   (<= 0 offset)
   (<= offset (+ offset length))
   (<= (+ offset length) (len array))))

(defun-sk sac0-copy-elements-p (src dst offset length)
  (forall i
    (implies
     (and
      (integerp i)
      (<= offset i)
      (< i (+ offset length)))
     (equal
      (sac0-nth-elt i dst)
      (sac0-nth-elt i src)))))

(defun sac0-copy-p (src dst offset length)
  (and
   (sac0-elt-list-p src)
   (sac0-elt-list-p dst)
   (integerp offset)
   (integerp length)
   (sac0-valid-chunk-p src offset length)
   (equal (len src) (len dst))
   (sac0-copy-elements-p src dst offset length)))

(defun-sk sac0-all-shuffled-chunks-p
    (src dst start sigma k upper)
  (forall j-prime
    (implies
     (and
      (integerp j-prime)
      (<= 0 j-prime)
      (< j-prime upper))
     (sac0-copy-p
      src
      dst
      (+ start
         (* (sac0-nth-int j-prime sigma)
            k))
      k))))

;; This is the exported equality between total integer-indexed functions
;; after List.set and Function.update.

(defun-sk sac0-list-set-function-equal-p
    (xs index value)
  (forall argument
    (implies
     (integerp argument)
     (equal
      (sac0-nth-elt
       argument
       (sac0-list-set-int xs index value))
      (if (equal argument index)
          value
        (sac0-nth-elt argument xs))))))

;; Innermost element-copy loop for one shuffled subsegment.

(defun sac0-i-step-conclusion-p
    (src dst3 start startj sigma k s m j i)
  (let* ((source-index (+ startj i))
         (copied-value
          (sac0-nth-elt source-index src))
         (destination-index (+ startj i))
         (updated
          (sac0-list-set-int
           dst3 destination-index copied-value)))
    (and
     (<= 0 source-index)
     (< source-index (len src))
     (<= 0 destination-index)
     (< destination-index (len dst3))
     (implies
      (equal (len updated) (len dst3))
      (implies
       (sac0-list-set-function-equal-p
        dst3 destination-index copied-value)
       (and
        (sac0-copy-p src updated 0 (* s m))
        (sac0-all-shuffled-chunks-p
         src updated start sigma k j)
        (sac0-copy-p
         src updated startj (+ i 1))))))))

(defun-sk sac0-all-i-steps-p
    (src dst3 start startj sigma k s m j o3)
  (forall i
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (<= i o3)
       (sac0-copy-p src dst3 0 (* s m))
       (sac0-all-shuffled-chunks-p
        src dst3 start sigma k j)
       (sac0-copy-p src dst3 startj i))
      (sac0-i-step-conclusion-p
       src dst3 start startj sigma k s m j i)))))

(defun sac0-dst3-body-p
    (src dst3 start startj sigma k s m j o3)
  (and
   (sac0-all-i-steps-p
    src dst3 start startj sigma k s m j o3)
   (implies
    (and
     (sac0-copy-p src dst3 0 (* s m))
     (sac0-all-shuffled-chunks-p
      src dst3 start sigma k j)
     (sac0-copy-p src dst3 startj (+ o3 1)))
    (and
     (sac0-copy-p src dst3 0 (* s m))
     (sac0-all-shuffled-chunks-p
      src dst3 start sigma k (+ j 1))))))

(defun-sk sac0-all-dst3-loops-p
    (src dst2 start startj sigma k s m j o3)
  (forall dst3
    (implies
     (and
      (sac0-elt-list-p dst3)
      (equal (len dst3) (len dst2)))
     (sac0-dst3-body-p
      src dst3 start startj sigma k s m j o3))))

;; Middle loop over shuffled subsegments.

(defun sac0-j-step-conclusion-p
    (src dst2 start sigma k s m j)
  (and
   (<= 0 j)
   (< j (len sigma))
   (let* ((startj
           (+ start
              (* (sac0-nth-int j sigma)
                 k)))
          (o3 (- k 1)))
     (and
      (implies
       (<= 0 (+ o3 1))
       (and
        (and
         (sac0-copy-p src dst2 0 (* s m))
         (sac0-all-shuffled-chunks-p
          src dst2 start sigma k j)
         (sac0-copy-p src dst2 startj 0))
        (sac0-all-dst3-loops-p
         src dst2 start startj sigma k s m j o3)))
      (implies
       (< (+ o3 1) 0)
       (and
        (sac0-copy-p src dst2 0 (* s m))
        (sac0-all-shuffled-chunks-p
         src dst2 start sigma k (+ j 1))))))))

(defun-sk sac0-all-j-steps-p
    (src dst2 start sigma k s m o2)
  (forall j
    (implies
     (integerp j)
     (implies
      (and
       (<= 0 j)
       (<= j o2)
       (sac0-copy-p src dst2 0 (* s m))
       (sac0-all-shuffled-chunks-p
        src dst2 start sigma k j))
      (sac0-j-step-conclusion-p
       src dst2 start sigma k s m j)))))

(defun sac0-dst2-body-p
    (src dst2 start sigma k s m o2)
  (and
   (sac0-all-j-steps-p
    src dst2 start sigma k s m o2)
   (implies
    (and
     (sac0-copy-p src dst2 0 (* s m))
     (sac0-all-shuffled-chunks-p
      src dst2 start sigma k (+ o2 1)))
    (sac0-copy-p
     src dst2 0 (* (+ s 1) m)))))

(defun-sk sac0-all-dst2-loops-p
    (src dst1 start sigma k s m o2)
  (forall dst2
    (implies
     (and
      (sac0-elt-list-p dst2)
      (equal (len dst2) (len dst1)))
     (sac0-dst2-body-p
      src dst2 start sigma k s m o2))))

(defun sac0-sigma-body-p
    (src dst1 start sigma k l s m)
  (let ((o2 (- l 1)))
    (and
     (implies
      (<= 0 (+ o2 1))
      (and
       (and
        (sac0-copy-p src dst1 0 (* s m))
        (sac0-all-shuffled-chunks-p
         src dst1 start sigma k 0))
       (sac0-all-dst2-loops-p
        src dst1 start sigma k s m o2)))
     (implies
      (< (+ o2 1) 0)
      (sac0-copy-p
       src dst1 0 (* (+ s 1) m))))))

(defun-sk sac0-all-permutations-p
    (src dst1 start k l s m)
  (forall (sigma invsigma)
    (implies
     (and
      (sac0-integer-list-p sigma)
      (sac0-integer-list-p invsigma)
      (equal (len sigma) (len invsigma))
      (equal (len invsigma) l)
      (sac0-permutation-pair-p
       l sigma invsigma))
     (sac0-sigma-body-p
      src dst1 start sigma k l s m))))

(defun sac0-s-body-p (src dst1 k l s m)
  (let ((start (* s m)))
    (and
     (< 0 l)
     (sac0-all-permutations-p
      src dst1 start k l s m))))

(defun-sk sac0-all-s-loops-p
    (src dst1 k l m o1)
  (forall s
    (implies
     (integerp s)
     (implies
      (and
       (<= 0 s)
       (<= s o1)
       (sac0-copy-p src dst1 0 (* s m)))
      (sac0-s-body-p
       src dst1 k l s m)))))

;; Final element-copy loop for the remainder.

(defun sac0-remainder-i-step-conclusion-p
    (src dst2 last q m i)
  (let* ((source-index (+ last i))
         (copied-value
          (sac0-nth-elt source-index src))
         (destination-index (+ last i))
         (updated
          (sac0-list-set-int
           dst2 destination-index copied-value)))
    (and
     (<= 0 source-index)
     (< source-index (len src))
     (<= 0 destination-index)
     (< destination-index (len dst2))
     (implies
      (equal (len updated) (len dst2))
      (implies
       (sac0-list-set-function-equal-p
        dst2 destination-index copied-value)
       (and
        (sac0-copy-p src updated 0 (* q m))
        (sac0-copy-p
         src updated last (+ i 1))))))))

(defun-sk sac0-all-remainder-i-steps-p
    (src dst2 last q m o2)
  (forall i
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (<= i o2)
       (sac0-copy-p src dst2 0 (* q m))
       (sac0-copy-p src dst2 last i))
      (sac0-remainder-i-step-conclusion-p
       src dst2 last q m i)))))

(defun sac0-remainder-dst2-body-p
    (src dst2 last q m o2 full-length)
  (and
   (sac0-all-remainder-i-steps-p
    src dst2 last q m o2)
   (implies
    (and
     (sac0-copy-p src dst2 0 (* q m))
     (sac0-copy-p src dst2 last (+ o2 1)))
    (sac0-copy-p src dst2 0 full-length))))

(defun-sk sac0-all-remainder-dst2-loops-p
    (src old last q m o2 full-length)
  (forall dst2
    (implies
     (and
      (sac0-elt-list-p dst2)
      (equal (len dst2) (len old)))
     (sac0-remainder-dst2-body-p
      src dst2 last q m o2 full-length))))

(defun sac0-remainder-body-p
    (src old q m r full-length)
  (let* ((last (* q m))
         (o2 (- r 1)))
    (and
     (implies
      (<= 0 (+ o2 1))
      (and
       (sac0-copy-p src old 0 (* q m))
       (sac0-copy-p src old last 0)
       (sac0-all-remainder-dst2-loops-p
        src old last q m o2 full-length)))
     (implies
      (< (+ o2 1) 0)
      (sac0-copy-p
       src old 0 full-length)))))

;; Outermost segment loop and complete verification condition.

(defun sac0-dst1-body-p
    (src dst1 k l q r m o1 full-length)
  (and
   (sac0-all-s-loops-p
    src dst1 k l m o1)
   (implies
    (sac0-copy-p
     src dst1 0 (* (+ o1 1) m))
    (sac0-remainder-body-p
     src dst1 q m r full-length))))

(defun-sk sac0-all-dst1-loops-p
    (src dst k l q r m o1 full-length)
  (forall dst1
    (implies
     (and
      (sac0-elt-list-p dst1)
      (equal (len dst1) (len dst)))
     (sac0-dst1-body-p
      src dst1 k l q r m o1 full-length))))

(defun sac0-main-conclusion-p
    (src dst k l q r)
  (let* ((m (* k l))
         (o1 (- q 1))
         (full-length (len dst)))
    (and
     (implies
      (<= 0 (+ o1 1))
      (and
       (sac0-copy-p src dst 0 (* 0 m))
       (sac0-all-dst1-loops-p
        src dst k l q r m o1 full-length)))
     (implies
      (< (+ o1 1) 0)
      (sac0-remainder-body-p
       src dst q m r full-length)))))

(defun-sk
  ntp4vc-pearl-verifythis-2024-challenge1-top-smart-array-copy-0-statement
  ()
  (forall (src dst k l q r)
    (implies
     (and
      (sac0-elt-p (sac0-default-elt))
      (sac0-elt-list-p src)
      (sac0-elt-list-p dst)
      (integerp k)
      (integerp l)
      (integerp q)
      (integerp r)
      (equal (len src) (len dst))
      (< 0 (len dst))
      (< 0 k)
      (< 0 l)
      (<= 0 q)
      (<= 0 r)
      (< r (* k l))
      (equal
       (len dst)
       (+ (* (* q k) l) r)))
     (sac0-main-conclusion-p
      src dst k l q r))))

(value-triple :itpeval-statement-checked)
:q
