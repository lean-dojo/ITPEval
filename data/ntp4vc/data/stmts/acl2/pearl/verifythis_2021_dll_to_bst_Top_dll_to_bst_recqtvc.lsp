;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2021_dll_to_bst_Top_dll_to_bst_recqtvc: the recursive
;; conversion of a doubly linked list segment into a height-balanced binary
;; search tree while preserving map domains and the untouched list links.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; LOC and the imperative map-state type remain arbitrary, unbounded source
;; carriers.  TO-FMAP is the source abstraction from a state to a finite map.

(defstub dbst-loc-p (value) t)
(defstub dbst-state-p (object) t)
(defstub dbst-null () t)
(defstub dbst-default-loc () t)
(defstub dbst-to-fmap (object) t)

;; Finite maps are represented extensionally by duplicate-free alists whose
;; dotted entries are (key . value).  This covers arbitrary finite source
;; fmaps without bounding or enumerating the location carrier.

(defun dbst-fmap-p (map)
  (declare (xargs :measure (acl2-count map)))
  (if (consp map)
      (let ((entry (car map)))
        (and
         (consp entry)
         (dbst-loc-p (car entry))
         (dbst-loc-p (cdr entry))
         (not (assoc-equal (car entry) (cdr map)))
         (dbst-fmap-p (cdr map))))
    (equal map nil)))

(defun dbst-fmap-mem-p (key map)
  (if (assoc-equal key map) t nil))

(defun dbst-fmap-lookup (key map)
  (let ((entry (assoc-equal key map)))
    (if entry
        (cdr entry)
      (dbst-default-loc))))

(defun dbst-fmap-update (key value map)
  (declare (xargs :measure (acl2-count map)))
  (if (endp map)
      (list (cons key value))
    (if (equal key (caar map))
        (cons (cons key value) (cdr map))
      (cons
       (car map)
       (dbst-fmap-update key value (cdr map))))))

(defun-sk dbst-fmap-domain-equal-p (left right)
  (forall (key)
    (implies
     (dbst-loc-p key)
     (equal
      (dbst-fmap-mem-p key left)
      (dbst-fmap-mem-p key right)))))

(defun-sk dbst-fmap-equal-p (left right)
  (forall (key)
    (implies
     (dbst-loc-p key)
     (and
      (equal
       (dbst-fmap-mem-p key left)
       (dbst-fmap-mem-p key right))
      (implies
       (dbst-fmap-mem-p key left)
       (equal
        (dbst-fmap-lookup key left)
        (dbst-fmap-lookup key right)))))))

(defun-sk dbst-to-fmap-typed-p ()
  (forall (object)
    (implies
     (dbst-state-p object)
     (dbst-fmap-p (dbst-to-fmap object)))))

(defun dbst-interface-p ()
  (and
   (dbst-loc-p (dbst-null))
   (dbst-loc-p (dbst-default-loc))
   (dbst-to-fmap-typed-p)))

;; Proper finite ACL2 lists are exact representations of source sequences.
;; INT.TONAT sends negative integers to zero, and out-of-range indexing uses
;; the fixed inhabitant required by the exported source statement.

(defun dbst-loc-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (dbst-loc-p (car xs))
       (dbst-loc-list-p (cdr xs)))
    (equal xs nil)))

(defun dbst-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun dbst-nth-loc (xs index)
  (let ((tail
         (nthcdr
          (dbst-int-to-nat index)
          xs)))
    (if (consp tail)
        (car tail)
      (dbst-default-loc))))

(defun dbst-boundary-loc (xs index)
  (if (equal index (len xs))
      (dbst-null)
    (dbst-nth-loc xs index)))

;; Exact tagged representation of the source binary-tree datatype over
;; mathematical integers.

(defun dbst-empty ()
  :dbst-empty)

(defun dbst-node (left pivot right)
  (list :dbst-node left pivot right))

(defun dbst-empty-p (tree)
  (equal tree :dbst-empty))

(defun dbst-node-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :dbst-node)))

(defun dbst-node-left (tree)
  (cadr tree))

(defun dbst-node-pivot (tree)
  (caddr tree))

(defun dbst-node-right (tree)
  (cadddr tree))

(defun dbst-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((dbst-empty-p tree)
    t)
   ((dbst-node-p tree)
    (and
     (dbst-tree-p (dbst-node-left tree))
     (integerp (dbst-node-pivot tree))
     (dbst-tree-p (dbst-node-right tree))))
   (t nil)))

(defun dbst-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (dbst-node-p tree)
      (let ((left-height
             (dbst-height (dbst-node-left tree)))
            (right-height
             (dbst-height (dbst-node-right tree))))
        (+
         1
         (if (< left-height right-height)
             right-height
           left-height)))
    0))

;; Why3 integer power is used only at nonnegative tree heights in nonvacuous
;; balance obligations.  Nfix gives the exported Int.toNat behavior elsewhere.

(defun dbst-power-two (exponent)
  (expt 2 (nfix exponent)))

(defun dbst-balanced-size-bound-p (tree size)
  (implies
   (< 0 size)
   (let ((height (dbst-height tree)))
     (and
      (<=
       (dbst-power-two (- height 1))
       size)
      (< size (dbst-power-two height))))))

;; VALID, DLL, and TREE are direct target-native renderings of the source
;; predicates, including every integer quantifier and half-open interval.

(defun-sk dbst-later-elements-distinct-p (xs index)
  (forall (later)
    (implies
     (integerp later)
     (implies
      (and
       (< index later)
       (< later (len xs)))
      (not
       (equal
        (dbst-nth-loc xs index)
        (dbst-nth-loc xs later)))))))

(defun-sk dbst-valid-indices-p (prev next xs)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len xs)))
      (and
       (not
        (equal
         (dbst-nth-loc xs index)
         (dbst-null)))
       (dbst-fmap-mem-p
        (dbst-nth-loc xs index)
        prev)
       (dbst-fmap-mem-p
        (dbst-nth-loc xs index)
        next)
       (dbst-later-elements-distinct-p
        xs index))))))

(defun dbst-valid-p (prev next xs)
  (and
   (dbst-fmap-p prev)
   (dbst-fmap-p next)
   (dbst-loc-list-p xs)
   (dbst-valid-indices-p prev next xs)))

(defun-sk dbst-forward-links-p (next xs low high)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= low index)
       (< index (- high 1)))
      (equal
       (dbst-fmap-lookup
        (dbst-nth-loc xs index)
        next)
       (dbst-nth-loc xs (+ index 1)))))))

(defun-sk dbst-backward-links-p (prev xs low high)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (< low index)
       (< index high))
      (equal
       (dbst-fmap-lookup
        (dbst-nth-loc xs index)
        prev)
       (dbst-nth-loc xs (- index 1)))))))

(defun dbst-dll-p (prev next xs head low high)
  (and
   (dbst-loc-p head)
   (integerp low)
   (integerp high)
   (dbst-valid-p prev next xs)
   (<= 0 low)
   (<= low high)
   (<= high (len xs))
   (equal
    head
    (dbst-boundary-loc xs low))
   (dbst-forward-links-p next xs low high)
   (dbst-backward-links-p prev xs low high)
   (implies
    (< low high)
    (equal
     (dbst-fmap-lookup
      (dbst-nth-loc xs (- high 1))
      next)
     (dbst-boundary-loc xs high)))
   (implies
    (< low high)
    (equal
     (dbst-fmap-lookup
      (dbst-nth-loc xs low)
      prev)
     (if (equal low 0)
         (dbst-null)
       (dbst-nth-loc xs (- low 1)))))))

(defun dbst-tree-relation-p
    (prev next xs root tree low high)
  (declare (xargs :measure (acl2-count tree)))
  (and
   (dbst-fmap-p prev)
   (dbst-fmap-p next)
   (dbst-loc-list-p xs)
   (dbst-loc-p root)
   (dbst-tree-p tree)
   (integerp low)
   (integerp high)
   (dbst-valid-p prev next xs)
   (<= 0 low)
   (<= low high)
   (<= high (len xs))
   (cond
    ((dbst-empty-p tree)
     (and
      (equal root (dbst-null))
      (equal low high)))
    ((dbst-node-p tree)
     (let ((left (dbst-node-left tree))
           (pivot (dbst-node-pivot tree))
           (right (dbst-node-right tree)))
       (and
        (<= low pivot)
        (< pivot high)
        (equal root (dbst-nth-loc xs pivot))
        (dbst-tree-relation-p
         prev
         next
         xs
         (dbst-fmap-lookup root prev)
         left
         low
         pivot)
        (dbst-tree-relation-p
         prev
         next
         xs
         (dbst-fmap-lookup root next)
         right
         (+ pivot 1)
         high))))
    (t nil))))

;; These predicates preserve the four pointwise frame conditions generated
;; for map contents before and after each recursively processed segment.

(defun-sk dbst-prefix-equal-p
    (new-map old-map xs upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index upper))
      (equal
       (dbst-fmap-lookup
        (dbst-nth-loc xs index)
        new-map)
       (dbst-fmap-lookup
        (dbst-nth-loc xs index)
        old-map))))))

(defun-sk dbst-suffix-equal-p
    (new-map old-map xs lower)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index (len xs)))
      (equal
       (dbst-fmap-lookup
        (dbst-nth-loc xs index)
        new-map)
       (dbst-fmap-lookup
        (dbst-nth-loc xs index)
        old-map))))))

(defun dbst-first-state-assumptions-p
    (prev next xs ihead nl next1 prev1 left1 left-tree)
  (let ((prev-map (dbst-to-fmap prev))
        (next-map (dbst-to-fmap next))
        (prev1-map (dbst-to-fmap prev1))
        (next1-map (dbst-to-fmap next1)))
    (and
     (dbst-tree-relation-p
      prev1-map
      next1-map
      xs
      left1
      left-tree
      ihead
      (+ ihead nl))
     (dbst-fmap-domain-equal-p prev1-map prev-map)
     (dbst-fmap-domain-equal-p next1-map next-map)
     (dbst-prefix-equal-p
      prev1-map prev-map xs ihead)
     (dbst-suffix-equal-p
      prev1-map prev-map xs (+ ihead nl))
     (dbst-prefix-equal-p
      next1-map next-map xs ihead)
     (dbst-suffix-equal-p
      next1-map next-map xs (+ ihead nl))
     (dbst-balanced-size-bound-p left-tree nl))))

(defun dbst-second-state-assumptions-p
    (prev2 next1 xs o1 o2 next2 prev3 temp right-tree)
  (let ((prev2-map (dbst-to-fmap prev2))
        (next1-map (dbst-to-fmap next1))
        (prev3-map (dbst-to-fmap prev3))
        (next2-map (dbst-to-fmap next2)))
    (and
     (dbst-tree-relation-p
      prev3-map
      next2-map
      xs
      temp
      right-tree
      o2
      (+ o2 o1))
     (dbst-fmap-domain-equal-p prev3-map prev2-map)
     (dbst-fmap-domain-equal-p next2-map next1-map)
     (dbst-prefix-equal-p
      prev3-map prev2-map xs o2)
     (dbst-suffix-equal-p
      prev3-map prev2-map xs (+ o2 o1))
     (dbst-prefix-equal-p
      next2-map next1-map xs o2)
     (dbst-suffix-equal-p
      next2-map next1-map xs (+ o2 o1))
     (dbst-balanced-size-bound-p right-tree o1))))

(defun dbst-final-result-p
    (prev next xs ihead n nl left-tree
          next2 prev3 temp right-tree next3)
  (declare (ignore next2 temp))
  (let* ((o1 (- (- n nl) 1))
         (o2 (+ ihead nl 1))
         (root (dbst-boundary-loc xs (+ ihead nl)))
         (whole-tree
          (dbst-node left-tree (+ ihead nl) right-tree))
         (prev-map (dbst-to-fmap prev))
         (next-map (dbst-to-fmap next))
         (prev3-map (dbst-to-fmap prev3))
         (next3-map (dbst-to-fmap next3)))
    (and
     (equal
      (dbst-boundary-loc xs (+ o2 o1))
      (dbst-boundary-loc xs (+ ihead n)))
     (dbst-tree-relation-p
      prev3-map
      next3-map
      xs
      root
      whole-tree
      ihead
      (+ ihead n))
     (dbst-fmap-domain-equal-p prev3-map prev-map)
     (dbst-fmap-domain-equal-p next3-map next-map)
     (dbst-prefix-equal-p
      prev3-map prev-map xs ihead)
     (dbst-suffix-equal-p
      prev3-map prev-map xs (+ ihead n))
     (dbst-prefix-equal-p
      next3-map next-map xs ihead)
     (dbst-suffix-equal-p
      next3-map next-map xs (+ ihead n))
     (dbst-balanced-size-bound-p whole-tree n))))

(defun-sk dbst-all-next3-states-p
    (prev next xs ihead n nl left-tree
          next2 prev3 temp right-tree)
  (forall (next3)
    (implies
     (dbst-state-p next3)
     (implies
      (dbst-fmap-equal-p
       (dbst-to-fmap next3)
       (dbst-fmap-update
        (dbst-boundary-loc xs (+ ihead nl))
        temp
        (dbst-to-fmap next2)))
      (dbst-final-result-p
       prev next xs ihead n nl left-tree
       next2 prev3 temp right-tree next3)))))

(defun dbst-second-state-conclusion-p
    (prev next xs ihead n nl left-tree
          next2 prev3 temp right-tree)
  (let ((root
         (dbst-boundary-loc xs (+ ihead nl))))
    (and
     (dbst-fmap-mem-p
      root
      (dbst-to-fmap next2))
     (dbst-all-next3-states-p
      prev next xs ihead n nl left-tree
      next2 prev3 temp right-tree))))

(defun-sk dbst-all-second-states-p
    (prev next xs ihead n nl left-tree prev2 next1)
  (forall (next2 prev3 temp right-tree)
    (implies
     (and
      (dbst-state-p next2)
      (dbst-state-p prev3)
      (dbst-loc-p temp)
      (dbst-tree-p right-tree))
     (implies
      (dbst-second-state-assumptions-p
       prev2 next1 xs
       (- (- n nl) 1)
       (+ ihead nl 1)
       next2 prev3 temp right-tree)
      (dbst-second-state-conclusion-p
       prev next xs ihead n nl left-tree
       next2 prev3 temp right-tree)))))

(defun dbst-after-prev2-p
    (prev next xs head ihead n nl
          next1 prev2 left-tree)
  (declare (ignore head))
  (let* ((o1 (- (- n nl) 1))
         (o2 (+ ihead nl 1))
         (root
          (dbst-boundary-loc xs (+ ihead nl)))
         (next1-map (dbst-to-fmap next1))
         (o3 (dbst-fmap-lookup root next1-map)))
    (and
     (dbst-fmap-mem-p root next1-map)
     (implies
      (equal
       o3
       (dbst-fmap-lookup root next1-map))
      (and
       (and
        (<= 0 n)
        (< o1 n))
       (dbst-dll-p
        (dbst-to-fmap prev2)
        next1-map
        xs
        o3
        o2
        (+ o2 o1))
       (dbst-all-second-states-p
        prev next xs ihead n nl left-tree
        prev2 next1))))))

(defun-sk dbst-all-prev2-states-p
    (prev next xs head ihead n nl
          next1 prev1 left1 left-tree)
  (forall (prev2)
    (implies
     (dbst-state-p prev2)
     (implies
      (dbst-fmap-equal-p
       (dbst-to-fmap prev2)
       (dbst-fmap-update
        (dbst-boundary-loc xs (+ ihead nl))
        left1
        (dbst-to-fmap prev1)))
      (dbst-after-prev2-p
       prev next xs head ihead n nl
       next1 prev2 left-tree)))))

(defun dbst-first-state-conclusion-p
    (prev next xs head ihead n nl
          next1 prev1 left1 left-tree)
  (let ((root
         (dbst-boundary-loc xs (+ ihead nl))))
    (and
     (dbst-fmap-mem-p
      root
      (dbst-to-fmap prev1))
     (dbst-all-prev2-states-p
      prev next xs head ihead n nl
      next1 prev1 left1 left-tree))))

(defun-sk dbst-all-first-states-p
    (prev next xs head ihead n nl)
  (forall (next1 prev1 left1 left-tree)
    (implies
     (and
      (dbst-state-p next1)
      (dbst-state-p prev1)
      (dbst-loc-p left1)
      (dbst-tree-p left-tree))
     (implies
      (dbst-first-state-assumptions-p
       prev next xs ihead nl
       next1 prev1 left1 left-tree)
      (dbst-first-state-conclusion-p
       prev next xs head ihead n nl
       next1 prev1 left1 left-tree)))))

(defun dbst-zero-case-p
    (prev next xs head ihead n)
  (let ((prev-map (dbst-to-fmap prev))
        (next-map (dbst-to-fmap next)))
    (and
     (equal
      head
      (dbst-boundary-loc xs (+ ihead n)))
     (dbst-tree-relation-p
      prev-map
      next-map
      xs
      (dbst-null)
      (dbst-empty)
      ihead
      (+ ihead n))
     (dbst-fmap-domain-equal-p prev-map prev-map)
     (dbst-fmap-domain-equal-p next-map next-map)
     (dbst-balanced-size-bound-p (dbst-empty) n))))

(defun dbst-nonzero-case-p
    (prev next xs head ihead n)
  ;; The DLL premise implies n >= 0.  Hence FLOOR n 2 is exactly Why3's
  ;; ComputerDivision.div n 2 (division toward zero) in this branch.
  (let ((nl (floor n 2)))
    (and
     (not (equal 2 0))
     (and
      (and
       (<= 0 n)
       (< nl n))
      (dbst-dll-p
       (dbst-to-fmap prev)
       (dbst-to-fmap next)
       xs
       head
       ihead
       (+ ihead nl)))
     (dbst-all-first-states-p
      prev next xs head ihead n nl))))

(defun
  ntp4vc-pearl-verifythis-2021-dll-to-bst-top-dll-to-bst-recqtvc-statement
  (prev next xs head ihead n)
  (implies
   (and
    (dbst-interface-p)
    (dbst-state-p prev)
    (dbst-state-p next)
    (dbst-loc-list-p xs)
    (dbst-loc-p head)
    (integerp ihead)
    (integerp n)
    (dbst-dll-p
     (dbst-to-fmap prev)
     (dbst-to-fmap next)
     xs
     head
     ihead
     (+ ihead n)))
   (if (equal n 0)
       (dbst-zero-case-p
        prev next xs head ihead n)
     (dbst-nonzero-case-p
      prev next xs head ihead n))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
