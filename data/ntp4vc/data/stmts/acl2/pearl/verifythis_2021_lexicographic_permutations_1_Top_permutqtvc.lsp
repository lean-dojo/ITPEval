;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2021_lexicographic_permutations_1_Top_permutqtvc:
;; the complete verification condition for enumerating every permutation of
;; an integer sequence in strict lexicographic order. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Why3 arrays and finite sequences of mathematical integers are represented
;; bijectively by proper ACL2 lists of unbounded ACL2 integers.

(defun lp-permut-int-list-p (sequence)
  (declare (xargs :measure (acl2-count sequence)))
  (if (consp sequence)
      (and
       (integerp (car sequence))
       (lp-permut-int-list-p (cdr sequence)))
    (equal sequence nil)))

(defun lp-permut-int-list-list-p (sequences)
  (declare (xargs :measure (acl2-count sequences)))
  (if (consp sequences)
      (and
       (lp-permut-int-list-p (car sequences))
       (lp-permut-int-list-list-p (cdr sequences)))
    (equal sequences nil)))

;; Integer indexing follows the exported Int.toNat convention and uses the
;; source inhabited integer value zero outside the finite sequence.

(defun lp-permut-read-nat (index sequence)
  (declare (xargs :measure (nfix index)))
  (if (and
       (natp index)
       (< 0 index)
       (consp sequence))
      (lp-permut-read-nat (- index 1) (cdr sequence))
    (if (consp sequence) (car sequence) 0)))

(defun lp-permut-read (sequence index)
  (lp-permut-read-nat (nfix index) sequence))

;; Under the list representation, the source array-to-sequence operation is
;; extensionally the identity.

(defun lp-permut-to-seq (array)
  array)

(defun-sk lp-permut-pointwise-copy-p (output input)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len output)))
      (equal
       (lp-permut-read output index)
       (lp-permut-read input index))))))

(defun lp-permut-to-seq-spec-p (output input)
  (and
   (lp-permut-int-list-p output)
   (lp-permut-int-list-p input)
   (equal (len output) (len input))
   (lp-permut-pointwise-copy-p output input)))

;; Occurrence equality is the source definition of permutation. The quantified
;; value ranges over all mathematical integers, without a finite carrier bound.

(defun lp-permut-count (value sequence)
  (declare (xargs :measure (acl2-count sequence)))
  (if (consp sequence)
      (+
       (if (equal value (car sequence)) 1 0)
       (lp-permut-count value (cdr sequence)))
    0))

(defun-sk lp-permut-same-counts-p (left right)
  (forall (value)
    (implies
     (integerp value)
     (equal
      (lp-permut-count value left)
      (lp-permut-count value right)))))

(defun lp-permut-permutation-p (left right)
  (and
   (lp-permut-int-list-p left)
   (lp-permut-int-list-p right)
   (equal (len left) (len right))
   (lp-permut-same-counts-p left right)))

;; This is the source strict lexicographic relation, including equal positive
;; length and its internally existential first differing index.

(defun-sk lp-permut-prefix-equal-p (left right bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index bound))
      (equal
       (lp-permut-read left index)
       (lp-permut-read right index))))))

(defun-sk lp-permut-lex-less-p (left right)
  (exists (index)
    (and
     (integerp index)
     (lp-permut-int-list-p left)
     (lp-permut-int-list-p right)
     (equal (len left) (len right))
     (< 0 (len right))
     (<= 0 index)
     (< index (len left))
     (lp-permut-prefix-equal-p left right index)
     (<
      (lp-permut-read left index)
      (lp-permut-read right index)))))

(defun-sk lp-permut-nondecreasing-p (sequence)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index))
     (implies
      (and
       (<= 0 left-index)
       (<= left-index right-index)
       (< right-index (len sequence)))
      (<=
       (lp-permut-read sequence left-index)
       (lp-permut-read sequence right-index))))))

;; Why3 finite sets of integer sequences are represented extensionally by
;; duplicate-free proper lists. Membership, insertion, cardinality, and subset
;; therefore coincide with their finite-set counterparts.

(defun lp-permut-fset-p (set)
  (declare (xargs :measure (acl2-count set)))
  (if (consp set)
      (and
       (lp-permut-int-list-p (car set))
       (not (member-equal (car set) (cdr set)))
       (lp-permut-fset-p (cdr set)))
    (equal set nil)))

(defun lp-permut-fset-insert (sequence set)
  (if (member-equal sequence set)
      set
    (cons sequence set)))

(defun lp-permut-fset-subset-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (member-equal (car left) right)
       (lp-permut-fset-subset-p (cdr left) right))
    (equal left nil)))

;; ALL-PERMUTATIONS is abstract in the generated VC. DEFSTUB is the
;; conservative interface for that source function; its type and sole
;; contract are explicit in the statement premise below.

(defstub lp-permut-all-permutations (sequence) t)

(defun-sk lp-permut-all-permutations-contained-p (base set)
  (forall (candidate)
    (implies
     (lp-permut-int-list-p candidate)
     (implies
      (lp-permut-permutation-p candidate base)
      (member-equal candidate set)))))

(defun lp-permut-all-permutations-spec-p (base set)
  (and
   (lp-permut-int-list-p base)
   (lp-permut-fset-p set)
   (lp-permut-all-permutations-contained-p base set)))

;; The remaining helpers are direct definitional renderings of the generated
;; sequence and finite-set quantifiers.

(defun-sk lp-permut-occurs-before-p (result candidate bound)
  (exists (index)
    (and
     (integerp index)
     (<= 0 index)
     (< index bound)
     (equal
      (lp-permut-read result index)
      candidate))))

(defun-sk lp-permut-all-items-permutations-p (result base)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len result)))
      (lp-permut-permutation-p
       (lp-permut-read result index)
       base)))))

(defun-sk lp-permut-strictly-ordered-p (result)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index))
     (implies
      (and
       (<= 0 left-index)
       (< left-index right-index)
       (< right-index (len result)))
      (lp-permut-lex-less-p
       (lp-permut-read result left-index)
       (lp-permut-read result right-index))))))

(defun-sk lp-permut-covers-before-last-p (result base last)
  (forall (candidate)
    (implies
     (lp-permut-int-list-p candidate)
     (implies
      (and
       (lp-permut-permutation-p candidate base)
       (lp-permut-lex-less-p candidate last))
      (lp-permut-occurs-before-p
       result candidate (- (len result) 1))))))

(defun-sk lp-permut-set-enumerates-result-p (set result)
  (forall (candidate)
    (implies
     (lp-permut-int-list-p candidate)
     (iff
      (member-equal candidate set)
      (lp-permut-occurs-before-p
       result candidate (len result))))))

(defun-sk lp-permut-all-permutations-enumerated-p (result base)
  (forall (candidate)
    (implies
     (lp-permut-int-list-p candidate)
     (implies
      (lp-permut-permutation-p candidate base)
      (lp-permut-occurs-before-p
       result candidate (len result))))))

(defun-sk lp-permut-append-prefix-copy-p (old new)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len old)))
      (equal
       (lp-permut-read new index)
       (lp-permut-read old index))))))

(defun lp-permut-append-one-spec-p (old added new)
  (and
   (lp-permut-int-list-list-p old)
   (lp-permut-int-list-p added)
   (lp-permut-int-list-list-p new)
   (equal (len new) (+ 1 (len old)))
   (equal (lp-permut-read new (len old)) added)
   (lp-permut-append-prefix-copy-p old new)))

;; This is the invariant established by the explicitly unrolled first
;; iteration of the source loop.

(defun lp-permut-initial-invariant-p
    (all1 a0 a1 result last inserted)
  (let ((singleton
         (lp-permut-fset-insert inserted nil)))
    (and
     (< 0 (len result))
     (lp-permut-permutation-p
      (lp-permut-to-seq a1)
      a0)
     (lp-permut-all-items-permutations-p result a0)
     (equal
      last
      (lp-permut-read result (- (len result) 1)))
     (equal
      (lp-permut-read result (- (len result) 1))
      (lp-permut-to-seq a1))
     (lp-permut-permutation-p last a0)
     (lp-permut-strictly-ordered-p result)
     (lp-permut-covers-before-last-p result a0 last)
     (lp-permut-set-enumerates-result-p singleton result)
     (lp-permut-fset-subset-p singleton all1))))

;; This is the source while-loop invariant at an arbitrary current array,
;; result sequence, and ghost result set.

(defun lp-permut-loop-invariant-p
    (all1 a0 current result sresult)
  (and
   (< 0 (len result))
   (lp-permut-permutation-p
    (lp-permut-to-seq current)
    a0)
   (lp-permut-all-items-permutations-p result a0)
   (equal
    (lp-permut-read result (- (len result) 1))
    (lp-permut-to-seq current))
   (lp-permut-permutation-p
    (lp-permut-read result (- (len result) 1))
    a0)
   (lp-permut-strictly-ordered-p result)
   (lp-permut-covers-before-last-p
    result
    a0
    (lp-permut-read result (- (len result) 1)))
   (lp-permut-set-enumerates-result-p sresult result)
   (lp-permut-fset-subset-p sresult all1)))

(defun-sk lp-permut-unchanged-p (new old)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len new)))
      (equal
       (lp-permut-read new index)
       (lp-permut-read old index))))))

(defun-sk lp-permut-no-greater-permutation-p (sequence base)
  (forall (candidate)
    (implies
     (lp-permut-int-list-p candidate)
     (implies
      (lp-permut-permutation-p candidate base)
      (not
       (lp-permut-lex-less-p sequence candidate))))))

(defun-sk lp-permut-no-between-p (lower upper base)
  (forall (candidate)
    (implies
     (lp-permut-int-list-p candidate)
     (implies
      (lp-permut-permutation-p candidate base)
      (not
       (and
        (lp-permut-lex-less-p lower candidate)
        (lp-permut-lex-less-p candidate upper)))))))

;; These are exactly the five postconditions supplied by a call to NEXT.

(defun lp-permut-next-result-premises-p (a0 old new result)
  (and
   (lp-permut-permutation-p
    (lp-permut-to-seq new)
    a0)
   (implies
    (not (equal result t))
    (lp-permut-unchanged-p new old))
   (implies
    (not (equal result t))
    (lp-permut-no-greater-permutation-p
     (lp-permut-to-seq new)
     a0))
   (implies
    (equal result t)
    (lp-permut-lex-less-p
     (lp-permut-to-seq old)
     (lp-permut-to-seq new)))
   (implies
    (equal result t)
    (lp-permut-no-between-p
     (lp-permut-to-seq old)
     (lp-permut-to-seq new)
     a0))))

;; The true branch appends the new permutation, updates the finite ghost set,
;; decreases the cardinality variant, and re-establishes every invariant.

(defun lp-permut-true-update-conclusion-p
    (all1 a0 sresult new-result new-array last inserted)
  (let ((new-set
         (lp-permut-fset-insert inserted sresult)))
    (and
     (<= 0 (- (len all1) (len sresult)))
     (<
      (- (len all1) (len new-set))
      (- (len all1) (len sresult)))
     (< 0 (len new-result))
     (lp-permut-permutation-p
      (lp-permut-to-seq new-array)
      a0)
     (lp-permut-all-items-permutations-p new-result a0)
     (equal
      last
      (lp-permut-read new-result (- (len new-result) 1)))
     (equal
      (lp-permut-read new-result (- (len new-result) 1))
      (lp-permut-to-seq new-array))
     (lp-permut-permutation-p last a0)
     (lp-permut-strictly-ordered-p new-result)
     (lp-permut-covers-before-last-p
      new-result a0 last)
     (lp-permut-set-enumerates-result-p
      new-set new-result)
     (lp-permut-fset-subset-p new-set all1))))

(defun lp-permut-true-branch-p
    (all1 a0 sresult result new-array)
  (let ((output
         (lp-permut-to-seq new-array)))
    (implies
     (lp-permut-to-seq-spec-p output new-array)
     (let ((new-result
            (append result (list output))))
       (implies
        (lp-permut-append-one-spec-p
         result output new-result)
        (let ((last
               (lp-permut-to-seq new-array)))
          (implies
           (lp-permut-to-seq-spec-p last new-array)
           (let ((inserted
                  (lp-permut-to-seq new-array)))
             (implies
              (lp-permut-to-seq-spec-p
               inserted new-array)
              (lp-permut-true-update-conclusion-p
               all1
               a0
               sresult
               new-result
               new-array
               last
               inserted))))))))))

;; When NEXT returns false, the accumulated result is the strictly ordered,
;; complete enumeration required by the function contract.

(defun lp-permut-false-branch-p (original result)
  (and
   (lp-permut-all-items-permutations-p
    result
    (lp-permut-to-seq original))
   (lp-permut-strictly-ordered-p result)
   (lp-permut-all-permutations-enumerated-p
    result
    (lp-permut-to-seq original))))

(defun lp-permut-next-result-case-p
    (all1 original a0 sresult result old new next-result)
  (implies
   (lp-permut-next-result-premises-p
    a0 old new next-result)
   (if (equal next-result t)
       (lp-permut-true-branch-p
        all1 a0 sresult result new)
     (lp-permut-false-branch-p
      original result))))

(defun-sk lp-permut-all-next-results-p
    (all1 original a0 sresult result old new)
  (forall (next-result)
    (implies
     (booleanp next-result)
     (lp-permut-next-result-case-p
      all1
      original
      a0
      sresult
      result
      old
      new
      next-result))))

(defun-sk lp-permut-all-next-arrays-p
    (all1 original a0 sresult result current)
  (forall (new-array)
    (implies
     (lp-permut-int-list-p new-array)
     (implies
      (equal (len new-array) (len current))
      (lp-permut-all-next-results-p
       all1
       original
       a0
       sresult
       result
       current
       new-array)))))

(defun lp-permut-loop-continuation-conclusion-p
    (all1 original a0 sresult result current)
  (and
   (equal (len current) (len a0))
   (lp-permut-permutation-p
    (lp-permut-to-seq current)
    a0)
   (lp-permut-all-next-arrays-p
    all1
    original
    a0
    sresult
    result
    current)))

;; RESULT, SRESULT, and the current array remain universally quantified inside
;; the VC, as the continuation generated for the source while loop.

(defun-sk lp-permut-all-loop-continuations-p
    (all1 original a0 initial-array)
  (forall (sresult result current)
    (implies
     (and
      (lp-permut-fset-p sresult)
      (lp-permut-int-list-list-p result)
      (lp-permut-int-list-p current))
     (implies
      (equal (len current) (len initial-array))
      (implies
       (lp-permut-loop-invariant-p
        all1 a0 current result sresult)
       (lp-permut-loop-continuation-conclusion-p
        all1
        original
        a0
        sresult
        result
        current))))))

;; This preserves the nested contracts of sorting, the first sequence append,
;; the ghost LAST assignment, and the ghost finite-set insertion.

(defun lp-permut-initial-array-body-p
    (all1 original a0 initial-array)
  (let ((first-output
         (lp-permut-to-seq initial-array)))
    (implies
     (lp-permut-to-seq-spec-p
      first-output initial-array)
     (let* ((empty-result nil)
            (first-result
             (append empty-result
                     (list first-output))))
       (implies
        (lp-permut-append-one-spec-p
         empty-result first-output first-result)
        (let ((last
               (lp-permut-to-seq initial-array)))
          (implies
           (lp-permut-to-seq-spec-p
            last initial-array)
           (let ((inserted
                  (lp-permut-to-seq initial-array)))
             (implies
              (lp-permut-to-seq-spec-p
               inserted initial-array)
              (and
               (lp-permut-initial-invariant-p
                all1
                a0
                initial-array
                first-result
                last
                inserted)
               (lp-permut-all-loop-continuations-p
                all1
                original
                a0
                initial-array)))))))))))

(defun-sk lp-permut-all-sorted-arrays-p
    (all1 original a0)
  (forall (initial-array)
    (implies
     (lp-permut-int-list-p initial-array)
     (implies
      (equal (len initial-array) (len original))
      (implies
       (and
        (lp-permut-nondecreasing-p initial-array)
        (lp-permut-permutation-p
         (lp-permut-to-seq initial-array)
         (lp-permut-to-seq original)))
       (lp-permut-initial-array-body-p
        all1
        original
        a0
        initial-array))))))

;; This closed predicate is the complete unproved PERMUT verification
;; condition. The source function contracts appear as implications, and all
;; array, sequence, set, integer, Boolean, and witness domains remain explicit.

(defun-sk
    ntp4vc-pearl-verifythis-2021-lexicographic-permutations-1-top-permutqtvc-statement
    ()
  (forall (original)
    (implies
     (lp-permut-int-list-p original)
     (let ((a0
            (lp-permut-to-seq original)))
       (implies
        (lp-permut-to-seq-spec-p a0 original)
        (let ((all1
               (lp-permut-all-permutations a0)))
          (implies
           (lp-permut-all-permutations-spec-p
            a0 all1)
           (lp-permut-all-sorted-arrays-p
            all1 original a0))))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
