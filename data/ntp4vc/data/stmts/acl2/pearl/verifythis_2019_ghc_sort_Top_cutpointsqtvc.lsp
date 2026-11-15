;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2019_ghc_sort_Top_cutpointsqtvc: the verification
;; condition for constructing cutpoints that partition a nonempty integer
;; array into ordered monotonic segments. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Why3 array of integers is represented by its finite in-bounds contents.
;; Every read occurring in an active VC branch is guarded by the original
;; bounds conditions. A list_seq record is represented by its integer list
;; field; its ghost seq field is definitionally the reverse of that list,
;; exactly as required by the source type invariant.

(defun ghc-cut-int-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (ghc-cut-int-list-p (cdr xs)))
    (equal xs nil)))

;; Int.toNat maps negative integers to zero. Out-of-range list reads use the
;; inhabited integer default zero, matching the three prover exports.

(defun ghc-cut-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun ghc-cut-nth-zero-nat (index xs)
  (declare (xargs :measure (nfix index)))
  (if (and
       (natp index)
       (consp xs))
      (if (zp index)
          (car xs)
        (ghc-cut-nth-zero-nat
         (- index 1)
         (cdr xs)))
    0))

(defun ghc-cut-nth-zero (index xs)
  (ghc-cut-nth-zero-nat
   (ghc-cut-int-to-nat index)
   xs))

(defun ghc-cut-seq (list-seq)
  (reverse list-seq))

(defun ghc-cut-seq-read (list-seq index)
  (ghc-cut-nth-zero
   index
   (ghc-cut-seq list-seq)))

(defun ghc-cut-last (list-seq)
  (ghc-cut-seq-read
   list-seq
   (- (len (ghc-cut-seq list-seq)) 1)))

;; These predicates preserve the universal integer quantifiers in each
;; monotonic-segment disjunction.

(defun-sk ghc-cut-strict-run-p (s lower upper)
  (forall (z1 z2)
    (implies
     (and
      (integerp z1)
      (integerp z2))
     (implies
      (and
       (<= lower z1)
       (< z1 z2)
       (< z2 upper))
      (< (ghc-cut-nth-zero z1 s)
         (ghc-cut-nth-zero z2 s))))))

(defun-sk ghc-cut-decreasing-run-p (s lower upper)
  (forall (z1 z2)
    (implies
     (and
      (integerp z1)
      (integerp z2))
     (implies
      (and
       (<= lower z1)
       (< z1 z2)
       (< z2 upper))
      (<= (ghc-cut-nth-zero z2 s)
          (ghc-cut-nth-zero z1 s))))))

(defun ghc-cut-run-p (s lower upper)
  (or
   (ghc-cut-strict-run-p s lower upper)
   (ghc-cut-decreasing-run-p s lower upper)))

(defun-sk ghc-cut-all-segments-p (s list-seq)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (<= 0 k)
       (< k (- (len (ghc-cut-seq list-seq)) 1)))
      (let ((ck (ghc-cut-seq-read list-seq k))
            (ck1
             (ghc-cut-seq-read list-seq (+ k 1))))
        (ghc-cut-run-p s ck ck1))))))

(defun-sk ghc-cut-seq-sorted-p (list-seq)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j))
     (implies
      (and
       (<= 0 i)
       (< i j)
       (< j (len (ghc-cut-seq list-seq))))
      (<= (ghc-cut-seq-read list-seq i)
          (ghc-cut-seq-read list-seq j))))))

(defun-sk ghc-cut-list-bounds-p (list-seq upper)
  (forall (z)
    (implies
     (integerp z)
     (implies
      (member-equal z list-seq)
      (and
       (<= 0 z)
       (<= z upper))))))

;; Boolean equality is the source eqb computation. The only Boolean values in
;; the quantified source domain are represented by T and NIL.

(defun ghc-cut-boolean-p (value)
  (or
   (equal value t)
   (equal value nil)))

(defun ghc-cut-eqb (b1 b2)
  (if (equal b1 b2) t nil))

(defun ghc-cut-lt-bool (left right)
  (if (< left right) t nil))

;; This is the loop invariant antecedent for an arbitrary current cutpoint
;; record.

(defun ghc-cut-current-state-p (s n cut)
  (let ((last (ghc-cut-last cut)))
    (and
     (and
      (< 0 (+ last 1))
      (<= (+ last 1) (+ n 1)))
     (< 0 (len (ghc-cut-seq cut)))
     (equal (ghc-cut-seq-read cut 0) 0)
     (ghc-cut-list-bounds-p cut n)
     (ghc-cut-all-segments-p s cut)
     (ghc-cut-seq-sorted-p cut))))

;; This is the complete postcondition required when the final cutpoint has
;; been installed.

(defun ghc-cut-final-state-p (s list-seq)
  (and
   (equal (ghc-cut-seq-read list-seq 0) 0)
   (equal (ghc-cut-last list-seq) (len s))
   (<= 2 (len list-seq))
   (ghc-cut-list-bounds-p list-seq (len s))
   (ghc-cut-all-segments-p s list-seq)
   (ghc-cut-seq-sorted-p list-seq)))

;; When a changed monotonicity comparison is found, every record whose list
;; field is Cons y cut.list must satisfy the source's next outer-loop
;; invariant. The record's sequence field remains reverse(list) by definition.

(defun ghc-cut-next-state-p (s n cut y next)
  (let ((last (ghc-cut-last cut)))
    (and
     (and
      (<= 0 (- n (+ last 1)))
      (< (- n (+ y 1))
         (- n (+ last 1))))
     (and
      (< 0 (+ y 1))
      (<= (+ y 1) (+ n 1)))
     (< 0 (len (ghc-cut-seq next)))
     (equal (ghc-cut-seq-read next 0) 0)
     (equal (ghc-cut-last next) y)
     (ghc-cut-list-bounds-p next n)
     (ghc-cut-all-segments-p s next)
     (ghc-cut-seq-sorted-p next))))

(defun-sk ghc-cut-all-next-records-p (s n cut y)
  (forall (next)
    (implies
     (ghc-cut-int-list-p next)
     (implies
      (equal next (cons y cut))
      (ghc-cut-next-state-p
       s n cut y next)))))

;; This is the inner-loop continuation for a fixed Boolean result.

(defun ghc-cut-o2-antecedent-p (s cut y o2)
  (if (< y (len s))
      (let* ((o3
              (ghc-cut-lt-bool
               (ghc-cut-nth-zero (- y 1) s)
               (ghc-cut-nth-zero y s)))
             (baseline
              (ghc-cut-lt-bool
               (ghc-cut-nth-zero
                (ghc-cut-last cut)
                s)
               (ghc-cut-nth-zero
                (+ (ghc-cut-last cut) 1)
                s))))
        (and
         (equal o2 (ghc-cut-eqb o3 baseline))
         (iff
          (equal o2 t)
          (equal o3 baseline))))
    (equal o2 nil)))

(defun ghc-cut-o2-true-result-p (s n cut y)
  (let ((last (ghc-cut-last cut)))
    (and
     (and
      (<= 0 (- n y))
      (< (- n (+ y 1))
         (- n y)))
     (and
      (<= (+ last 1) (+ y 1))
      (<= (+ y 1) n))
     (ghc-cut-run-p
      s
      last
      (+ y 1)))))

(defun ghc-cut-o2-result-p (s n cut y o2)
  (if (equal o2 t)
      (ghc-cut-o2-true-result-p
       s n cut y)
    (ghc-cut-all-next-records-p
     s n cut y)))

(defun-sk ghc-cut-all-o2-p (s n cut y)
  (forall (o2)
    (implies
     (ghc-cut-boolean-p o2)
     (implies
      (ghc-cut-o2-antecedent-p
       s cut y o2)
      (ghc-cut-o2-result-p
       s n cut y o2)))))

;; The y quantifier remains inside the branch where last(cut)+1<n.

(defun ghc-cut-y-result-p (s n cut y)
  (and
   (implies
    (< y n)
    (and
     (and
      (<= 0 y)
      (< y (len s)))
     (let ((previous (- y 1)))
       (and
        (<= 0 previous)
        (< previous (len s))))))
   (ghc-cut-all-o2-p s n cut y)))

(defun-sk ghc-cut-all-y-p (s n cut)
  (forall (y)
    (implies
     (integerp y)
     (implies
      (and
       (and
        (<= (+ (ghc-cut-last cut) 1) y)
        (<= y n))
       (ghc-cut-run-p
        s
        (ghc-cut-last cut)
        y))
      (ghc-cut-y-result-p
       s n cut y)))))

(defun ghc-cut-continue-inner-p (s n cut)
  (let ((last (ghc-cut-last cut)))
    (and
     (and
      (and
       (<= 0 (+ last 1))
       (< (+ last 1) (len s)))
      (and
       (<= 0 last)
       (< last (len s))))
     (and
      (and
       (<= (+ last 1) (+ last 1))
       (<= (+ last 1) n))
      (ghc-cut-run-p
       s last (+ last 1)))
     (ghc-cut-all-y-p s n cut))))

;; If the outer loop stopped one point before n, every list_seq record
;; obtained by Cons n cut.list must satisfy the final postcondition.

(defun-sk ghc-cut-all-final-extensions-p (s n cut)
  (forall (next)
    (implies
     (ghc-cut-int-list-p next)
     (implies
      (equal next (cons n cut))
      (ghc-cut-final-state-p s next)))))

(defun ghc-cut-current-conclusion-p (s n cut)
  (let ((last (ghc-cut-last cut)))
    (if (< (+ last 1) n)
        (ghc-cut-continue-inner-p s n cut)
      (if (< last n)
          (ghc-cut-all-final-extensions-p
           s n cut)
        (ghc-cut-final-state-p s cut)))))

(defun-sk ghc-cut-all-current-records-p (s n)
  (forall (cut)
    (implies
     (ghc-cut-int-list-p cut)
     (implies
      (ghc-cut-current-state-p s n cut)
      (ghc-cut-current-conclusion-p
       s n cut)))))

;; This is the initial state after extend 0 nil, followed by the complete
;; universally quantified outer-loop continuation.

(defun ghc-cut-initial-conclusion-p (s n initial)
  (and
   (equal 1 (+ 0 1))
   (and
    (< 0 1)
    (<= 1 (+ n 1)))
   (< 0 (len (ghc-cut-seq initial)))
   (equal (ghc-cut-seq-read initial 0) 0)
   (equal (ghc-cut-last initial) 0)
   (ghc-cut-list-bounds-p initial n)
   (ghc-cut-all-segments-p s initial)
   (ghc-cut-seq-sorted-p initial)
   (ghc-cut-all-current-records-p s n)))

(defun-sk ghc-cut-all-initial-records-p (s n)
  (forall (initial)
    (implies
     (ghc-cut-int-list-p initial)
     (implies
      (equal initial (cons 0 nil))
      (ghc-cut-initial-conclusion-p
       s n initial)))))

;; This closed predicate is the complete unproved cutpoints verification
;; condition, including the source nonempty-array assumption.

(defun-sk
    ntp4vc-pearl-verifythis-2019-ghc-sort-top-cutpointsqtvc-statement
    ()
  (forall (s)
    (implies
     (ghc-cut-int-list-p s)
     (implies
      (< 0 (len s))
      (let ((n (len s)))
        (ghc-cut-all-initial-records-p
         s n))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
