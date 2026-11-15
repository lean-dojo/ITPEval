;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/linked_list_rev_Termination_list_reversalqtvc: the linked-list
;; reversal termination verification condition over finite memory, ranks,
;; seen-cell counts, and a lexicographic decrease. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the arbitrary location carrier,
;; distinguished null location, integer-indexed cell enumeration, and the
;; universally arbitrary loc -> loc and loc -> integer functions in the
;; source statement.  Their source typing laws remain explicit below.

(defstub llrt-loc-p (x) t)
(defstub llrt-null () t)
(defstub llrt-s (i) t)
(defstub llrt-mem1 (location) t)
(defstub llrt-idx (location) t)
(defstub llrt-mem3 (location) t)

(defun-sk llrt-s-typed-p ()
  (forall (i)
    (implies
     (integerp i)
     (llrt-loc-p (llrt-s i)))))

(defun-sk llrt-mem1-typed-p ()
  (forall (location)
    (implies
     (llrt-loc-p location)
     (llrt-loc-p (llrt-mem1 location)))))

(defun-sk llrt-idx-typed-p ()
  (forall (location)
    (implies
     (llrt-loc-p location)
     (integerp (llrt-idx location)))))

(defun-sk llrt-mem3-typed-p ()
  (forall (location)
    (implies
     (llrt-loc-p location)
     (llrt-loc-p (llrt-mem3 location)))))

(defun llrt-outer-interface-p ()
  (and
   (llrt-loc-p (llrt-null))
   (llrt-s-typed-p)
   (llrt-mem1-typed-p)))

;; The source function o1 is completely determined by o'def.

(defun llrt-o1 (location)
  (if (equal location (llrt-null))
      0
    -1))

;; Dispatch gives exact applications of the original and single-point-updated
;; rank and memory functions.  It is the ACL2 counterpart of Function.update.

(defun llrt-idx-apply
    (kind update-key update-value location)
  (cond
   ((eq kind :o1)
    (llrt-o1 location))
   ((eq kind :idx)
    (llrt-idx location))
   ((eq kind :updated-idx)
    (if (equal location update-key)
        update-value
      (llrt-idx location)))
   (t 0)))

(defun llrt-next-apply
    (kind update-key update-value location)
  (cond
   ((eq kind :mem1)
    (llrt-mem1 location))
   ((eq kind :mem3)
    (llrt-mem3 location))
   ((eq kind :updated-mem3)
    (if (equal location update-key)
        update-value
      (llrt-mem3 location)))
   (t (llrt-null))))

;; This counts exactly the integers i in [lo,hi) for which
;; 0 < idx(s(i)).  Recursing from hi-1 downward matches Why3's numof
;; definition, including the value zero when hi <= lo.

(defun llrt-seen-count
    (idx-kind idx-key idx-value lo count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (let ((i (+ (ifix lo) (- count 1))))
      (+
       (if (< 0
              (llrt-idx-apply
               idx-kind idx-key idx-value (llrt-s i)))
           1
         0)
       (llrt-seen-count
        idx-kind idx-key idx-value lo (- count 1))))))

(defun llrt-seen
    (idx-kind idx-key idx-value lo hi)
  (if (and
       (integerp lo)
       (integerp hi)
       (< lo hi))
      (llrt-seen-count
       idx-kind idx-key idx-value lo (- hi lo))
    0))

(defun-sk llrt-valid-cells-nonnull-p (n)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and (<= 0 i)
           (< i n))
      (not
       (equal (llrt-s i) (llrt-null)))))))

(defun-sk llrt-valid-cells-distinct-p (n)
  (forall (i j)
    (implies
     (and (integerp i)
          (integerp j))
     (implies
      (and
       (<= 0 i)
       (< i n)
       (<= 0 j)
       (< j n)
       (not (equal i j)))
      (not
       (equal (llrt-s i) (llrt-s j)))))))

(defun llrt-valid-cells-p (n)
  (and
   (llrt-valid-cells-nonnull-p n)
   (llrt-valid-cells-distinct-p n)))

(defun-sk llrt-indexed-location-p (n location)
  (exists (i)
    (and
     (integerp i)
     (<= 0 i)
     (< i n)
     (equal location (llrt-s i)))))

(defun llrt-inside-memory-p (n location)
  (or
   (equal location (llrt-null))
   (llrt-indexed-location-p n location)))

(defun-sk llrt-finite-memory-p
    (next-kind next-key next-value n)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i n))
      (llrt-inside-memory-p
       n
       (llrt-next-apply
        next-kind next-key next-value (llrt-s i)))))))

(defun-sk llrt-ranks-bounded-p
    (idx-kind idx-key idx-value n upper)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i n))
      (and
       (<= -1
           (llrt-idx-apply
            idx-kind idx-key idx-value (llrt-s i)))
       (<=
        (llrt-idx-apply
         idx-kind idx-key idx-value (llrt-s i))
        upper))))))

(defun-sk llrt-zero-iff-null-p
    (idx-kind idx-key idx-value)
  (forall (location)
    (implies
     (llrt-loc-p location)
     (equal
      (equal
       (llrt-idx-apply
        idx-kind idx-key idx-value location)
       0)
      (equal location (llrt-null))))))

;; If use-cutoff is nil, this is the source's positive-rank link condition.
;; Otherwise it additionally restricts the premise to ranks no greater than
;; the rank of cutoff-location.

(defun-sk llrt-rank-chain-p
    (idx-kind idx-key idx-value
     next-kind next-key next-value
     n use-cutoff cutoff-location)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i n))
      (implies
       (and
        (< 0
           (llrt-idx-apply
            idx-kind idx-key idx-value (llrt-s i)))
        (or
         (not use-cutoff)
         (<=
          (llrt-idx-apply
           idx-kind idx-key idx-value (llrt-s i))
          (llrt-idx-apply
           idx-kind idx-key idx-value cutoff-location))))
       (equal
        (llrt-idx-apply
         idx-kind
         idx-key
         idx-value
         (llrt-next-apply
          next-kind next-key next-value (llrt-s i)))
        (-
         (llrt-idx-apply
          idx-kind idx-key idx-value (llrt-s i))
         1)))))))

(defun llrt-initial-invariant-p (n l)
  (let ((seen0
         (llrt-seen
          :o1 (llrt-null) 0 0 n)))
    (and
     (llrt-inside-memory-p n l)
     (llrt-inside-memory-p n (llrt-null))
     (llrt-finite-memory-p
      :mem1 (llrt-null) (llrt-null) n)
     (and
      (equal 0 seen0)
      (<= 0 seen0))
     (llrt-ranks-bounded-p
      :o1 (llrt-null) 0 n 0)
     (llrt-zero-iff-null-p
      :o1 (llrt-null) 0)
     (if (equal (llrt-o1 l) -1)
         (and
          (equal (llrt-o1 (llrt-null)) 0)
          (llrt-rank-chain-p
           :o1 (llrt-null) 0
           :mem1 (llrt-null) (llrt-null)
           n nil (llrt-null)))
       (llrt-rank-chain-p
        :o1 (llrt-null) 0
        :mem1 (llrt-null) (llrt-null)
        n t l)))))

(defun llrt-continuation-antecedent-p (n r l1)
  (let ((seen0
         (llrt-seen
          :idx (llrt-null) 0 0 n)))
    (and
     (llrt-idx-typed-p)
     (llrt-mem3-typed-p)
     (llrt-inside-memory-p n l1)
     (llrt-inside-memory-p n r)
     (llrt-finite-memory-p
      :mem3 (llrt-null) (llrt-null) n)
     (<= 0 seen0)
     (llrt-ranks-bounded-p
      :idx (llrt-null) 0 n seen0)
     (llrt-zero-iff-null-p
      :idx (llrt-null) 0)
     (if (equal (llrt-idx l1) -1)
         (and
          (equal (llrt-idx r) seen0)
          (llrt-rank-chain-p
           :idx (llrt-null) 0
           :mem3 (llrt-null) (llrt-null)
           n nil (llrt-null)))
       (llrt-rank-chain-p
        :idx (llrt-null) 0
        :mem3 (llrt-null) (llrt-null)
        n t l1)))))

(defun llrt-updated-decrease-p (n l1)
  (let* ((seen0
          (llrt-seen
           :idx (llrt-null) 0 0 n))
         (new-rank (+ seen0 1))
         (first-before (- n seen0))
         (first-after (- n (+ seen0 1)))
         (second-before (+ 1 (llrt-idx l1)))
         (second-after
          (+
           1
           (llrt-idx-apply
            :updated-idx
            l1
            new-rank
            (llrt-mem3 l1)))))
    (or
     (and
      (<= 0 first-before)
      (< first-after first-before))
     (and
      (equal first-before first-after)
      (<= 0 second-before)
      (< second-after second-before)))))

(defun llrt-nonupdated-decrease-p (n l1)
  (let* ((seen0
          (llrt-seen
           :idx (llrt-null) 0 0 n))
         (first-value (- n seen0))
         (second-before (+ 1 (llrt-idx l1)))
         (second-after
          (+ 1 (llrt-idx (llrt-mem3 l1)))))
    (or
     (and
      (<= 0 first-value)
      (< first-value first-value))
     (and
      (<= 0 second-before)
      (< second-after second-before)))))

(defun llrt-updated-post-p (n r l1)
  (let* ((seen0
          (llrt-seen
           :idx (llrt-null) 0 0 n))
         (new-rank (+ seen0 1))
         (updated-seen
          (llrt-seen
           :updated-idx l1 new-rank 0 n))
         (next-location (llrt-mem3 l1)))
    (and
     (not (equal l1 (llrt-null)))
     (not (equal l1 (llrt-null)))
     (llrt-updated-decrease-p n l1)
     (llrt-inside-memory-p n next-location)
     (llrt-inside-memory-p n l1)
     (llrt-finite-memory-p
      :updated-mem3 l1 r n)
     (and
      (equal new-rank updated-seen)
      (<= 0 updated-seen))
     (llrt-ranks-bounded-p
      :updated-idx l1 new-rank n new-rank)
     (llrt-zero-iff-null-p
      :updated-idx l1 new-rank)
     (if
         (equal
          (llrt-idx-apply
           :updated-idx l1 new-rank next-location)
          -1)
         (and
          (equal
           (llrt-idx-apply
            :updated-idx l1 new-rank l1)
           new-rank)
          (llrt-rank-chain-p
           :updated-idx l1 new-rank
           :updated-mem3 l1 r
           n nil (llrt-null)))
       (llrt-rank-chain-p
        :updated-idx l1 new-rank
        :updated-mem3 l1 r
        n t next-location)))))

(defun llrt-minus-one-branch-p (n r l1)
  (let* ((seen0
          (llrt-seen
           :idx (llrt-null) 0 0 n))
         (new-rank (+ seen0 1))
         (updated-seen
          (llrt-seen
           :updated-idx l1 new-rank 0 n)))
    (and
     (llrt-valid-cells-p n)
     (llrt-inside-memory-p n l1)
     (not (equal l1 (llrt-null)))
     (equal (llrt-idx l1) -1)
     (<= 0 seen0)
     (implies
      (equal updated-seen (+ 1 seen0))
      (llrt-updated-post-p n r l1)))))

(defun llrt-nonminus-one-post-p (n r l1)
  (let* ((seen0
          (llrt-seen
           :idx (llrt-null) 0 0 n))
         (next-location (llrt-mem3 l1)))
    (and
     (not (equal l1 (llrt-null)))
     (not (equal l1 (llrt-null)))
     (llrt-nonupdated-decrease-p n l1)
     (llrt-inside-memory-p n next-location)
     (llrt-inside-memory-p n l1)
     (llrt-finite-memory-p
      :updated-mem3 l1 r n)
     (<= 0 seen0)
     (llrt-ranks-bounded-p
      :idx (llrt-null) 0 n seen0)
     (llrt-zero-iff-null-p
      :idx (llrt-null) 0)
     (if (equal (llrt-idx next-location) -1)
         (and
          (equal (llrt-idx l1) seen0)
          (llrt-rank-chain-p
           :idx (llrt-null) 0
           :updated-mem3 l1 r
           n nil (llrt-null)))
       (llrt-rank-chain-p
        :idx (llrt-null) 0
        :updated-mem3 l1 r
        n t next-location)))))

(defun llrt-continuation-case-p (n r l1)
  (implies
   (llrt-continuation-antecedent-p n r l1)
   (implies
    (not (equal l1 (llrt-null)))
    (if (equal (llrt-idx l1) -1)
        (llrt-minus-one-branch-p n r l1)
      (llrt-nonminus-one-post-p n r l1)))))

;; r and l1 remain universally quantified inside the conclusion.  The
;; conservative idx and mem3 interfaces above represent the source's
;; universally arbitrary function parameters without replacing them by
;; finite tables.

(defun-sk llrt-all-continuations-p (n)
  (forall (r l1)
    (implies
     (and
      (llrt-loc-p r)
      (llrt-loc-p l1))
     (llrt-continuation-case-p n r l1))))

(defun
  ntp4vc-pearl-linked-list-rev-termination-list-reversalqtvc-statement
  (n l)
  (implies
   (and
    (llrt-outer-interface-p)
    (integerp n)
    (llrt-loc-p l)
    (<= 0 n)
    (llrt-valid-cells-p n)
    (llrt-finite-memory-p
     :mem1 (llrt-null) (llrt-null) n)
    (llrt-inside-memory-p n l))
   (and
    (llrt-initial-invariant-p n l)
    (llrt-all-continuations-p n))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
