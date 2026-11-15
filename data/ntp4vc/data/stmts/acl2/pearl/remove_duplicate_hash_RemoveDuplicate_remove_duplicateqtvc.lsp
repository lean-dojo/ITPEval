;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/remove_duplicate_hash_RemoveDuplicate_remove_duplicateqtvc: the
;; duplicate-removal verification condition for finite-set accumulation,
;; list initialization, loop invariants, and duplicate-free output. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces retain the source's arbitrary inhabited element
;; and mutable-set carriers. Their typing and choose specification are explicit
;; hypotheses of the final statement predicate.

(defstub rdh-elt-p (value) t)
(defstub rdh-set-p (value) t)
(defstub rdh-default-elt () t)
(defstub rdh-to-fset (set) t)
(defstub rdh-choose1 (set) t)

(defun rdh-elt-list-p (xs)
  (if (consp xs)
      (and
       (rdh-elt-p (car xs))
       (rdh-elt-list-p (cdr xs)))
    (equal xs nil)))

;; Source finite sets are represented extensionally by duplicate-free proper
;; lists. This covers every finite set, and list order is ignored by all set
;; equality and subset predicates below.

(defun rdh-fset-p (set)
  (if (consp set)
      (and
       (rdh-elt-p (car set))
       (not (member-equal (car set) (cdr set)))
       (rdh-fset-p (cdr set)))
    (equal set nil)))

(defun rdh-fset-member-p (value set)
  (if (member-equal value set)
      t
    nil))

(defun rdh-fset-subset-p (left right)
  (if (consp left)
      (and
       (rdh-fset-member-p (car left) right)
       (rdh-fset-subset-p (cdr left) right))
    (equal left nil)))

(defun rdh-fset-equal-p (left right)
  (and
   (rdh-fset-subset-p left right)
   (rdh-fset-subset-p right left)))

(defun rdh-fset-insert (value set)
  (if (rdh-fset-member-p value set)
      set
    (cons value set)))

(defun-sk rdh-elt-domain-nonempty-p ()
  (exists (value)
    (rdh-elt-p value)))

(defun-sk rdh-set-domain-nonempty-p ()
  (exists (set)
    (rdh-set-p set)))

(defun-sk rdh-set-interface-laws-p ()
  (forall (set)
    (implies
     (rdh-set-p set)
     (and
      (rdh-fset-p (rdh-to-fset set))
      (rdh-elt-p (rdh-choose1 set))
      (implies
       (not (rdh-fset-equal-p
             (rdh-to-fset set)
             nil))
       (rdh-fset-member-p
        (rdh-choose1 set)
        (rdh-to-fset set)))))))

(defun rdh-source-context-p ()
  (and
   (rdh-elt-domain-nonempty-p)
   (rdh-set-domain-nonempty-p)
   (rdh-elt-p (rdh-default-elt))
   (rdh-set-interface-laws-p)))

;; Int.toNat sends negative integers to zero. Total list indexing then returns
;; the distinguished source inhabitant when the natural index is out of range.

(defun rdh-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun rdh-nth (xs index)
  (let ((tail
         (nthcdr
          (rdh-int-to-nat index)
          xs)))
    (if (consp tail)
        (car tail)
      (rdh-default-elt))))

;; This is List.set at a natural index: an out-of-range update leaves the list
;; unchanged, rather than extending it.

(defun rdh-list-set-nat (xs index value)
  (declare (xargs :measure (nfix index)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (rdh-list-set-nat
        (cdr xs)
        (- index 1)
        value)))))

(defun rdh-list-set (xs index value)
  (rdh-list-set-nat
   xs
   (rdh-int-to-nat index)
   value))

;; The source predicates appears and nodup retain their mathematical-integer
;; quantifiers and half-open prefix bounds.

(defun-sk rdh-appears-p (value xs size)
  (exists (index)
    (and
     (integerp index)
     (<= 0 index)
     (< index size)
     (equal
      (rdh-nth xs index)
      value))))

(defun-sk rdh-nodup-p (xs size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index size))
      (not
       (rdh-appears-p
        (rdh-nth xs index)
        xs
        index))))))

(defun-sk rdh-appears-equals-fset-p
    (xs size set)
  (forall (value)
    (implies
     (rdh-elt-p value)
     (equal
      (rdh-appears-p value xs size)
      (rdh-fset-member-p
       value
       (rdh-to-fset set))))))

(defun-sk rdh-fset-equals-appears-p
    (set xs size)
  (forall (value)
    (implies
     (rdh-elt-p value)
     (equal
      (rdh-fset-member-p
       value
       (rdh-to-fset set))
      (rdh-appears-p value xs size)))))

(defun-sk rdh-appears-equals-appears-p
    (left left-size right right-size)
  (forall (value)
    (implies
     (rdh-elt-p value)
     (equal
      (rdh-appears-p value left left-size)
      (rdh-appears-p value right right-size)))))

(defun rdh-add-premise-p (new-set value old-set)
  (and
   (rdh-fset-equal-p
    (rdh-to-fset new-set)
    (rdh-fset-insert
     value
     (rdh-to-fset old-set)))
   (if (rdh-fset-member-p
        value
        (rdh-to-fset old-set))
       (equal
        (len (rdh-to-fset new-set))
        (len (rdh-to-fset old-set)))
     (equal
      (len (rdh-to-fset new-set))
      (+ (len (rdh-to-fset old-set)) 1)))))

;; Pointwise equality over every integer argument is the exact ACL2 rendering
;; of the source equality between the total indexing function after List.set
;; and Function.update at the mathematical integer key.

(defun-sk rdh-list-set-update-law-p
    (xs index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (rdh-nth
       (rdh-list-set xs index value)
       argument)
      (if (equal argument index)
          value
        (rdh-nth xs argument))))))

(defun rdh-second-invariant-p
    (a outer-set r current-set i j o3)
  (and
   (and
    (<= 0 i)
    (<= i o3))
   (rdh-appears-equals-fset-p
    a i current-set)
   (rdh-fset-equals-appears-p
    current-set r j)
   (rdh-nodup-p r j)
   (and
    (<= 0 j)
    (equal
     j
     (len (rdh-to-fset current-set)))
    (<=
     (len (rdh-to-fset current-set))
     (len r)))
   (rdh-fset-subset-p
    (rdh-to-fset current-set)
    (rdh-to-fset outer-set))))

(defun rdh-second-updated-invariant-p
    (a outer-set updated-r updated-set i j)
  (and
   (rdh-appears-equals-fset-p
    a
    (+ i 1)
    updated-set)
   (rdh-fset-equals-appears-p
    updated-set
    updated-r
    (+ j 1))
   (rdh-nodup-p updated-r (+ j 1))
   (and
    (<= 0 (+ j 1))
    (equal
     (+ j 1)
     (len (rdh-to-fset updated-set)))
    (<=
     (len (rdh-to-fset updated-set))
     (len updated-r)))
   (rdh-fset-subset-p
    (rdh-to-fset updated-set)
    (rdh-to-fset outer-set))))

(defun rdh-inserted-list-conclusion-p
    (a outer-set r current-set new-set i j)
  (declare (ignore current-set))
  (let* ((value (rdh-nth a i))
         (updated-r
          (rdh-list-set r j value)))
    (and
     (and
      (<= 0 j)
      (< j (len r)))
     (implies
      (equal
       (len updated-r)
       (len r))
      (implies
       (rdh-list-set-update-law-p
        r j value)
       (rdh-second-updated-invariant-p
        a
        outer-set
        updated-r
        new-set
        i
        j))))))

(defun-sk rdh-after-set-insert-p
    (a outer-set r current-set i j)
  (forall (new-set)
    (implies
     (rdh-set-p new-set)
     (implies
      (rdh-add-premise-p
       new-set
       (rdh-nth a i)
       current-set)
      (and
       (and
        (<= 0 i)
        (< i (len a)))
       (rdh-inserted-list-conclusion-p
        a
        outer-set
        r
        current-set
        new-set
        i
        j))))))

(defun rdh-second-loop-step-p
    (a outer-set r current-set i j)
  (and
   (and
    (<= 0 i)
    (< i (len a)))
   (if
       (not
        (rdh-fset-member-p
         (rdh-nth a i)
         (rdh-to-fset current-set)))
       (and
        (and
         (<= 0 i)
         (< i (len a)))
        (rdh-after-set-insert-p
         a
         outer-set
         r
         current-set
         i
         j))
     (and
      (rdh-appears-equals-fset-p
       a
       (+ i 1)
       current-set)
      (rdh-fset-equals-appears-p
       current-set
       r
       j)
      (rdh-nodup-p r j)
      (and
       (<= 0 j)
       (equal
        j
        (len (rdh-to-fset current-set)))
       (<=
        (len (rdh-to-fset current-set))
        (len r)))
      (rdh-fset-subset-p
       (rdh-to-fset current-set)
       (rdh-to-fset outer-set))))))

(defun rdh-second-loop-case-p
    (a outer-set r current-set i j o3)
  (implies
   (rdh-second-invariant-p
    a outer-set r current-set i j o3)
   (rdh-second-loop-step-p
    a outer-set r current-set i j)))

(defun-sk rdh-all-second-loop-cases-p
    (a outer-set r current-set j o3)
  (forall (i)
    (implies
     (integerp i)
     (rdh-second-loop-case-p
      a
      outer-set
      r
      current-set
      i
      j
      o3))))

(defun rdh-second-final-invariant-p
    (a outer-set r current-set j o3)
  (and
   (rdh-appears-equals-fset-p
    a
    (+ o3 1)
    current-set)
   (rdh-fset-equals-appears-p
    current-set
    r
    j)
   (rdh-nodup-p r j)
   (and
    (<= 0 j)
    (equal
     j
     (len (rdh-to-fset current-set)))
    (<=
     (len (rdh-to-fset current-set))
     (len r)))
   (rdh-fset-subset-p
    (rdh-to-fset current-set)
    (rdh-to-fset outer-set))))

(defun rdh-output-postcondition-p (a r)
  (and
   (rdh-nodup-p r (len r))
   (rdh-appears-equals-appears-p
    a
    (len a)
    r
    (len r))))

(defun rdh-second-state-conclusion-p
    (a outer-set r current-set j o3)
  (and
   (rdh-all-second-loop-cases-p
    a
    outer-set
    r
    current-set
    j
    o3)
   (implies
    (rdh-second-final-invariant-p
     a
     outer-set
     r
     current-set
     j
     o3)
    (rdh-output-postcondition-p a r))))

(defun-sk rdh-all-second-loop-states-p
    (a outer-set initial-r o3)
  (forall (j r current-set)
    (implies
     (and
      (integerp j)
      (rdh-elt-list-p r)
      (rdh-set-p current-set))
     (implies
      (equal (len r) (len initial-r))
      (rdh-second-state-conclusion-p
       a
       outer-set
       r
       current-set
       j
       o3)))))

(defun rdh-second-loop-initial-p
    (a outer-set initial-r empty-set)
  (and
   (rdh-appears-equals-fset-p
    a 0 empty-set)
   (rdh-fset-equals-appears-p
    empty-set initial-r 0)
   (rdh-nodup-p initial-r 0)
   (and
    (<= 0 0)
    (equal
     0
     (len (rdh-to-fset empty-set)))
    (<=
     (len (rdh-to-fset empty-set))
     (len initial-r)))
   (rdh-fset-subset-p
    (rdh-to-fset empty-set)
    (rdh-to-fset outer-set))))

(defun rdh-second-loop-vc-p
    (a outer-set initial-r empty-set)
  (let ((o3 (- (len a) 1)))
    (and
     (implies
      (<= 0 (+ o3 1))
      (and
       (rdh-second-loop-initial-p
        a
        outer-set
        initial-r
        empty-set)
       (rdh-all-second-loop-states-p
        a
        outer-set
        initial-r
        o3)))
     (implies
      (< (+ o3 1) 0)
      (rdh-output-postcondition-p
       a
       initial-r)))))

(defun-sk rdh-all-empty-set-continuations-p
    (a outer-set initial-r)
  (forall (empty-set)
    (implies
     (rdh-set-p empty-set)
     (implies
      (rdh-fset-equal-p
       (rdh-to-fset empty-set)
       nil)
      (rdh-second-loop-vc-p
       a
       outer-set
       initial-r
       empty-set)))))

(defun-sk rdh-initialized-list-p (a r size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index size))
      (equal
       (rdh-nth r index)
       (rdh-nth a 0))))))

(defun-sk rdh-all-result-lists-p
    (a outer-set size)
  (forall (r)
    (implies
     (rdh-elt-list-p r)
     (implies
      (and
       (rdh-initialized-list-p
        a r size)
       (equal (len r) size))
      (rdh-all-empty-set-continuations-p
       a
       outer-set
       r)))))

(defun rdh-second-phase-p (a outer-set)
  (and
   (and
    (<= 0 0)
    (< 0 (len a)))
   (let ((size
          (len (rdh-to-fset outer-set))))
     (and
      (<= 0 size)
      (rdh-all-result-lists-p
       a
       outer-set
       size)))))

(defun rdh-first-invariant-p
    (a current-set i o1)
  (and
   (and
    (<= 0 i)
    (<= i o1))
   (rdh-appears-equals-fset-p
    a i current-set)))

(defun-sk rdh-first-after-insert-p
    (a current-set i)
  (forall (new-set)
    (implies
     (rdh-set-p new-set)
     (implies
      (rdh-add-premise-p
       new-set
       (rdh-nth a i)
       current-set)
      (rdh-appears-equals-fset-p
       a
       (+ i 1)
       new-set)))))

(defun rdh-first-loop-case-p
    (a current-set i o1)
  (implies
   (rdh-first-invariant-p
    a current-set i o1)
   (and
    (and
     (<= 0 i)
     (< i (len a)))
    (rdh-first-after-insert-p
     a
     current-set
     i))))

(defun-sk rdh-all-first-loop-cases-p
    (a current-set o1)
  (forall (i)
    (implies
     (integerp i)
     (rdh-first-loop-case-p
      a
      current-set
      i
      o1))))

(defun rdh-first-loop-set-conclusion-p
    (a current-set o1)
  (and
   (rdh-all-first-loop-cases-p
    a
    current-set
    o1)
   (implies
    (rdh-appears-equals-fset-p
     a
     (+ o1 1)
     current-set)
    (rdh-second-phase-p
     a
     current-set))))

(defun-sk rdh-all-first-loop-sets-p (a o1)
  (forall (current-set)
    (implies
     (rdh-set-p current-set)
     (rdh-first-loop-set-conclusion-p
      a
      current-set
      o1))))

(defun rdh-main-vc-p (a initial-set)
  (let ((o1 (- (len a) 1)))
    (and
     (implies
      (<= 0 (+ o1 1))
      (and
       (rdh-appears-equals-fset-p
        a
        0
        initial-set)
       (rdh-all-first-loop-sets-p
        a
        o1)))
     (implies
      (< (+ o1 1) 0)
      (rdh-second-phase-p
       a
       initial-set)))))

(defun
    ntp4vc-pearl-remove-duplicate-hash-removeduplicate-remove-duplicateqtvc-statement
    (a initial-set)
  (implies
   (and
    (rdh-source-context-p)
    (rdh-elt-list-p a)
    (rdh-set-p initial-set)
    (<= 1 (len a))
    (rdh-fset-equal-p
     (rdh-to-fset initial-set)
     nil)
    (equal
     (len (rdh-to-fset initial-set))
     0))
   (rdh-main-vc-p
    a
    initial-set)))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
