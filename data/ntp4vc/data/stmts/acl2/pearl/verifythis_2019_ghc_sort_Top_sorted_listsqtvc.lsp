;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2019_ghc_sort_Top_sorted_listsqtvc: the verification
;; condition for recursively turning monotonic integer-array segments between
;; cutpoints into nondecreasing lists while preserving all multiplicities.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite ACL2 integer lists represent Why3 integer lists and arrays
;; without bounding their lengths or element values. A list_seq record is
;; represented by its list field; its seq field is definitionally its reverse,
;; exactly as required by the source record invariant.

(defun sls-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (sls-integer-list-p (cdr xs)))
    (equal xs nil)))

(defun sls-integer-list-list-p (xss)
  (declare (xargs :measure (acl2-count xss)))
  (if (consp xss)
      (and
       (sls-integer-list-p (car xss))
       (sls-integer-list-list-p (cdr xss)))
    (equal xss nil)))

;; Int.toNat sends negative integers to zero. Out-of-range list lookup returns
;; the inhabited integer default zero, matching all three supplied exports.

(defun sls-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun sls-nth-zero-nat (index xs)
  (declare (xargs :measure (nfix index)))
  (if (and
       (natp index)
       (consp xs))
      (if (zp index)
          (car xs)
        (sls-nth-zero-nat
         (- index 1)
         (cdr xs)))
    0))

(defun sls-nth-zero (xs index)
  (sls-nth-zero-nat
   (sls-int-to-nat index)
   xs))

(defun sls-cut-seq (cut-list)
  (reverse cut-list))

(defun sls-cut-read (cut-list index)
  (sls-nth-zero
   (sls-cut-seq cut-list)
   index))

(defun sls-cut-last (cut-list)
  (sls-cut-read
   cut-list
   (- (len (sls-cut-seq cut-list)) 1)))

;; This is source List.take rather than ACL2 TAKE: it truncates at the end and
;; never pads. The source drop by zero is then definitionally the same list.

(defun sls-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      nil
    (cons
     (car xs)
     (sls-take
      (- count 1)
      (cdr xs)))))

;; These recursive predicates are exactly the source strict-increasing,
;; nondecreasing, and nonincreasing inductive list relations.

(defun sls-strict-increasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (and
       (consp xs)
       (consp (cdr xs)))
      (and
       (< (car xs) (cadr xs))
       (sls-strict-increasing-p
        (cdr xs)))
    t))

(defun sls-nondecreasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (and
       (consp xs)
       (consp (cdr xs)))
      (and
       (<= (car xs) (cadr xs))
       (sls-nondecreasing-p
        (cdr xs)))
    t))

(defun sls-nonincreasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (and
       (consp xs)
       (consp (cdr xs)))
      (and
       (<= (cadr xs) (car xs))
       (sls-nonincreasing-p
        (cdr xs)))
    t))

(defun sls-all-lists-nondecreasing-p (xss)
  (declare (xargs :measure (acl2-count xss)))
  (if (endp xss)
      t
    (and
     (sls-nondecreasing-p (car xss))
     (sls-all-lists-nondecreasing-p
      (cdr xss)))))

;; Right-folded append, occurrence count, and deletion-based multiset equality
;; faithfully encode the source list operations and finite-list permutation.

(defun sls-flatten (xss)
  (declare (xargs :measure (acl2-count xss)))
  (if (endp xss)
      nil
    (append
     (car xss)
     (sls-flatten (cdr xss)))))

(defun sls-count-occ (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      0
    (+
     (if (equal value (car xs)) 1 0)
     (sls-count-occ value (cdr xs)))))

(defun sls-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (sls-remove-first
        value
        (cdr xs))))))

(defun sls-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (sls-permutation-p
      (cdr left)
      (sls-remove-first
       (car left)
       right)))))

;; MAP-OCC is the finite cardinality of the source set of mathematical integer
;; indices in [LOWER, UPPER) whose array lookup equals VALUE.

(defun sls-map-occ-step
    (value array index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if (equal
          value
          (sls-nth-zero array index))
         1
       0)
     (sls-map-occ-step
      value
      array
      (+ index 1)
      (- remaining 1)))))

(defun sls-map-occ
    (value array lower upper)
  (if (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (sls-map-occ-step
       value array lower (- upper lower))
    0))

;; The two segment predicates retain the source universal integer quantifiers.

(defun-sk sls-strict-segment-p
    (array lower upper)
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
      (< (sls-nth-zero array z1)
         (sls-nth-zero array z2))))))

(defun-sk sls-nonincreasing-segment-p
    (array lower upper)
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
      (<= (sls-nth-zero array z2)
          (sls-nth-zero array z1))))))

(defun sls-monotonic-segment-p
    (array lower upper)
  (or
   (sls-strict-segment-p
    array lower upper)
   (sls-nonincreasing-segment-p
    array lower upper)))

(defun-sk sls-all-segments-monotonic-p
    (array cut-list)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (<= 0 k)
       (< k (- (len (sls-cut-seq cut-list)) 1)))
      (let ((ck
             (sls-cut-read cut-list k))
            (ck1
             (sls-cut-read cut-list (+ k 1))))
        (sls-monotonic-segment-p
         array ck ck1))))))

(defun-sk sls-cut-seq-nondecreasing-p
    (cut-list)
  (forall (x y)
    (implies
     (and
      (integerp x)
      (integerp y))
     (implies
      (and
       (<= 0 x)
       (< x y)
       (< y (len (sls-cut-seq cut-list))))
      (<= (sls-cut-read cut-list x)
          (sls-cut-read cut-list y))))))

(defun sls-cut-list-bounded-p
    (cut-list upper)
  (declare (xargs :measure (acl2-count cut-list)))
  (if (endp cut-list)
      t
    (and
     (<= 0 (car cut-list))
     (<= (car cut-list) upper)
     (sls-cut-list-bounded-p
      (cdr cut-list)
      upper))))

;; The source order operation is uniquely specified on every list satisfying
;; either strict increase or nonincrease, which is exactly where it is used.

(defun sls-order (xs)
  (if (endp xs)
      xs
    (if (endp (cdr xs))
        xs
      (if (< (car xs) (cadr xs))
          xs
        (reverse xs)))))

;; The following predicates preserve the internal universal and existential
;; scopes describing a list containing exactly one monotonic array segment.

(defun-sk sls-counts-match-segment-p
    (array seqi lower upper)
  (forall (x)
    (implies
     (integerp x)
     (equal
      (sls-count-occ x seqi)
      (sls-map-occ
       x array lower upper)))))

(defun-sk sls-value-occurs-in-segment-p
    (array value lower upper)
  (exists (z)
    (and
     (integerp z)
     (and
      (<= lower z)
      (< z upper))
     (equal
      (sls-nth-zero array z)
      value))))

(defun-sk sls-members-from-segment-p
    (array seqi lower upper)
  (forall (x)
    (implies
     (integerp x)
     (implies
      (member-equal x seqi)
      (sls-value-occurs-in-segment-p
       array x lower upper)))))

(defun sls-seqi-package-p
    (array seqi lower upper)
  (and
   (sls-counts-match-segment-p
    array seqi lower upper)
   (sls-members-from-segment-p
    array seqi lower upper)
   (implies
    (sls-strict-segment-p
     array lower upper)
    (sls-strict-increasing-p seqi))
   (implies
    (sls-nonincreasing-segment-p
     array lower upper)
    (sls-nonincreasing-p seqi))
   (or
    (sls-strict-increasing-p seqi)
    (sls-nonincreasing-p seqi))))

;; These are the source slice facts for o2 = drop 0 (take (toNat o1) seq1).

(defun-sk sls-prefix-copies-seq-p
    (prefix seq1 o1)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (<= 0 k)
       (< k o1))
      (equal
       (sls-nth-zero prefix k)
       (sls-nth-zero seq1 (+ 0 k)))))))

(defun sls-prefix-facts-p
    (prefix seq1 o1)
  (and
   (equal (len prefix) (- o1 0))
   (sls-prefix-copies-seq-p
    prefix seq1 o1)))

;; O4 remains universally quantified over lists of lists. Its antecedent is
;; exactly sortedness of every component and equality of all multiplicities.

(defun-sk sls-flatten-counts-match-cut-interval-p
    (array cut-list segment-lists)
  (forall (x)
    (implies
     (integerp x)
     (equal
      (sls-count-occ
       x
       (sls-flatten segment-lists))
      (sls-map-occ
       x
       array
       (sls-cut-read cut-list 0)
       (sls-cut-last cut-list))))))

(defun sls-segment-lists-package-p
    (array cut-list segment-lists)
  (and
   (sls-all-lists-nondecreasing-p
    segment-lists)
   (sls-flatten-counts-match-cut-interval-p
    array cut-list segment-lists)))

(defun-sk sls-all-segment-list-packages-imply-monotonic-p
    (array cut-list seqi)
  (forall (segment-lists)
    (implies
     (sls-integer-list-list-p segment-lists)
     (implies
      (sls-segment-lists-package-p
       array cut-list segment-lists)
      (or
       (sls-strict-increasing-p seqi)
       (sls-nonincreasing-p seqi))))))

;; This is the recursive-call context for each list_seq whose projections are
;; o3 and o2. Representing the record by o3 makes seq(lseq)=reverse(o3)
;; definitional while preserving the source universal quantifier.

(defun sls-recursive-list-seq-conclusion-p
    (cut-list array seqi lseq)
  (and
   (if (endp cut-list)
       nil
     (equal (cdr cut-list) lseq))
   (< 0 (len lseq))
   (sls-cut-seq-nondecreasing-p
    lseq)
   (sls-cut-list-bounded-p
    lseq
    (len array))
   (sls-all-segments-monotonic-p
    array lseq)
   (sls-all-segment-list-packages-imply-monotonic-p
    array lseq seqi)))

(defun-sk sls-all-recursive-list-seqs-p
    (cut-list array seqi o3 o2)
  (forall (lseq)
    (implies
     (sls-integer-list-p lseq)
     (implies
      (and
       (equal lseq o3)
       (equal (sls-cut-seq lseq) o2))
      (sls-recursive-list-seq-conclusion-p
       cut-list array seqi lseq)))))

(defun sls-seqi-recursive-obligation-p
    (cut-list array seqi h2 tail)
  (let* ((seq1 (sls-cut-seq cut-list))
         (o1 (- (len seq1) 1))
         (o2
          (sls-take
           (sls-int-to-nat o1)
           seq1))
         (o3 (cons h2 tail)))
    (and
     (and
      (<= 0 0)
      (<= 0 o1)
      (<= o1 (len seq1)))
     (implies
      (sls-prefix-facts-p
       o2 seq1 o1)
      (and
       (equal o2 (reverse o3))
       (sls-all-recursive-list-seqs-p
        cut-list array seqi o3 o2))))))

(defun-sk sls-all-seqi-recursive-obligations-p
    (cut-list array lower upper tail)
  (forall (seqi)
    (implies
     (sls-integer-list-p seqi)
     (implies
      (sls-seqi-package-p
       array seqi lower upper)
      (sls-seqi-recursive-obligation-p
       cut-list array seqi lower tail)))))

(defun sls-head-recursion-obligation-p
    (cut-list array)
  (if (endp cut-list)
      t
    (if (endp (cdr cut-list))
        t
      (let ((h1 (car cut-list))
            (h2 (cadr cut-list))
            (tail (cddr cut-list)))
        (and
         (and
          (<= 0 h2)
          (<= h2 (len array)))
         (and
          (<= 0 h1)
          (<= h1 (len array)))
         (sls-monotonic-segment-p
          array h2 h1)
         (sls-all-seqi-recursive-obligations-p
          cut-list array h2 h1 tail))))))

;; The existential construction branch retains seqi, lseq, and o3 internally.

(defun-sk sls-ordered-tail-exists-p
    (array seqi lseq result)
  (exists (o3)
    (and
     (sls-integer-list-list-p o3)
     (sls-segment-lists-package-p
      array lseq o3)
     (let ((o4 (sls-order seqi)))
       (and
        (and
         (sls-nondecreasing-p o4)
         (sls-permutation-p seqi o4))
        (equal result (cons o4 o3)))))))

(defun-sk sls-list-seq-construction-exists-p
    (array seqi expected-list prefix result)
  (exists (lseq)
    (and
     (sls-integer-list-p lseq)
     (and
      (equal lseq expected-list)
      (equal (sls-cut-seq lseq) prefix))
     (sls-ordered-tail-exists-p
      array seqi lseq result))))

(defun sls-seqi-produces-result-p
    (cut-list array seqi h2 tail result)
  (let* ((seq1 (sls-cut-seq cut-list))
         (o1 (- (len seq1) 1))
         (o2
          (sls-take
           (sls-int-to-nat o1)
           seq1)))
    (and
     (sls-seqi-package-p
      array seqi h2 (car cut-list))
     (and
      (sls-prefix-facts-p
       o2 seq1 o1)
      (sls-list-seq-construction-exists-p
       array
       seqi
       (cons h2 tail)
       o2
       result)))))

(defun-sk sls-long-result-premise-p
    (cut-list array result)
  (exists (seqi)
    (and
     (sls-integer-list-p seqi)
     (sls-seqi-produces-result-p
      cut-list
      array
      seqi
      (cadr cut-list)
      (cddr cut-list)
      result))))

(defun sls-result-premise-p
    (cut-list array result)
  (if (endp cut-list)
      (equal result nil)
    (if (endp (cdr cut-list))
        (equal result nil)
      (sls-long-result-premise-p
       cut-list array result))))

;; The final result keeps both postconditions: every returned segment list is
;; nondecreasing, and their concatenation has exactly the source interval's
;; multiplicities.

(defun sls-result-postcondition-p
    (cut-list array result)
  (and
   (sls-all-lists-nondecreasing-p result)
   (sls-flatten-counts-match-cut-interval-p
    array cut-list result)))

(defun-sk sls-all-results-correct-p
    (cut-list array)
  (forall (result)
    (implies
     (sls-integer-list-list-p result)
     (implies
      (sls-result-premise-p
       cut-list array result)
      (sls-result-postcondition-p
       cut-list array result)))))

;; This closed predicate is the complete unproved sorted_lists verification
;; condition, including all four source assumptions and both conclusion
;; conjuncts.

(defun-sk
    ntp4vc-pearl-verifythis-2019-ghc-sort-top-sorted-listsqtvc-statement
    ()
  (forall (cut-list array)
    (implies
     (and
      (sls-integer-list-p cut-list)
      (sls-integer-list-p array))
     (implies
      (and
       (< 0 (len cut-list))
       (sls-cut-seq-nondecreasing-p
        cut-list)
       (sls-cut-list-bounded-p
        cut-list
        (len array))
       (sls-all-segments-monotonic-p
        array cut-list))
      (and
       (sls-head-recursion-obligation-p
        cut-list array)
       (sls-all-results-correct-p
        cut-list array))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
