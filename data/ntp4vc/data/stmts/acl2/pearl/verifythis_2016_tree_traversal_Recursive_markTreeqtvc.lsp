;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2016_tree_traversal_Recursive_markTreeqtvc: the recursive
;; Morris tree-traversal verification condition for pointer rotations,
;; recursive subtree marking, and restoration of the original tree shape.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Locations form an arbitrary inhabited carrier. Pointer-field and mark maps
;; are arbitrary ACL2 function objects evaluated by APPLY$. A memory is the
;; exact pair (accessor-map, mark-map).

(defstub mtt-loc-p (location) t)
(defstub mtt-null () t)

(defun mtt-kind-p (kind)
  (or
   (equal kind :parent)
   (equal kind :left)
   (equal kind :right)))

(defun mtt-phase-p (phase)
  (or
   (equal phase :go-left)
   (equal phase :go-right)
   (equal phase :go-back)
   (equal phase :finish)))

(defun mtt-bool-p (value)
  (or (equal value t)
      (equal value nil)))

(defun mtt-pmem-at (pointer-map kind location)
  (apply$ pointer-map (list kind location)))

(defun mtt-mark-at (mark-map location)
  (apply$ mark-map (list location)))

(defun-sk mtt-pointer-map-p (pointer-map)
  (forall (kind location)
    (implies
     (and
      (mtt-kind-p kind)
      (mtt-loc-p location))
     (mtt-loc-p
      (mtt-pmem-at pointer-map kind location)))))

(defun-sk mtt-mark-map-p (mark-map)
  (forall (location)
    (implies
     (mtt-loc-p location)
     (mtt-bool-p
      (mtt-mark-at mark-map location)))))

(defun mtt-memory-p (memory)
  (and
   (true-listp memory)
   (equal (len memory) 2)
   (mtt-pointer-map-p (car memory))
   (mtt-mark-map-p (cadr memory))))

(defun mtt-accessor (memory)
  (car memory))

(defun mtt-marks (memory)
  (cadr memory))

(defun-sk mtt-loc-domain-nonempty-p ()
  (exists (location)
    (mtt-loc-p location)))

(defun-sk mtt-memory-domain-nonempty-p ()
  (exists (memory)
    (mtt-memory-p memory)))

(defun mtt-interface-p ()
  (and
   (mtt-loc-domain-nonempty-p)
   (mtt-loc-p (mtt-null))
   (mtt-memory-domain-nonempty-p)))

;; Empty trees are NIL. Nodes are exact records
;; (:MTT-NODE left location right), preserving the finite inductive tree type.

(defun mtt-node (left location right)
  (list :mtt-node left location right))

(defun mtt-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :mtt-node)))

(defun mtt-tree-left (tree)
  (cadr tree))

(defun mtt-tree-location (tree)
  (caddr tree))

(defun mtt-tree-right (tree)
  (cadddr tree))

(defun mtt-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (mtt-node-shape-p tree)
     (mtt-loc-p (mtt-tree-location tree))
     (mtt-tree-p (mtt-tree-left tree))
     (mtt-tree-p (mtt-tree-right tree)))))

(defun mtt-footprint-member-p (location tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      nil
    (and
     (mtt-node-shape-p tree)
     (or
      (equal location (mtt-tree-location tree))
      (mtt-footprint-member-p
       location
       (mtt-tree-left tree))
      (mtt-footprint-member-p
       location
       (mtt-tree-right tree))))))

;; This is the source TreeShape.is_tree recursion, including the full-binary
;; child-null equivalence and parent-pointer conditions.

(defun mtt-is-tree-p
    (pointer-map tree current parent)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      (equal current (mtt-null))
    (and
     (mtt-node-shape-p tree)
     (not (equal current (mtt-null)))
     (equal current (mtt-tree-location tree))
     (equal
      (mtt-pmem-at pointer-map :parent current)
      parent)
     (let ((left-current
            (mtt-pmem-at pointer-map :left current))
           (right-current
            (mtt-pmem-at pointer-map :right current)))
       (and
        (iff
         (equal left-current (mtt-null))
         (equal right-current (mtt-null)))
        (mtt-is-tree-p
         pointer-map
         (mtt-tree-left tree)
         left-current
         current)
        (mtt-is-tree-p
         pointer-map
         (mtt-tree-right tree)
         right-current
         current))))))

;; Source map equality is represented extensionally. The update predicates
;; are the exact pointwise meanings of Function.update at one mark location
;; and at one nested pointer-field/location pair.

(defun-sk mtt-pointer-maps-equal-p (left right)
  (forall (kind location)
    (implies
     (and
      (mtt-kind-p kind)
      (mtt-loc-p location))
     (equal
      (mtt-pmem-at left kind location)
      (mtt-pmem-at right kind location)))))

(defun-sk mtt-mark-maps-equal-p (left right)
  (forall (location)
    (implies
     (mtt-loc-p location)
     (equal
      (mtt-mark-at left location)
      (mtt-mark-at right location)))))

(defun-sk mtt-mark-true-update-p
    (new-map old-map updated-location)
  (forall (location)
    (implies
     (mtt-loc-p location)
     (equal
      (mtt-mark-at new-map location)
      (if (equal location updated-location)
          t
        (mtt-mark-at old-map location))))))

(defun-sk mtt-pointer-update-p
    (new-map old-map updated-kind updated-location value)
  (forall (kind location)
    (implies
     (and
      (mtt-kind-p kind)
      (mtt-loc-p location))
     (equal
      (mtt-pmem-at new-map kind location)
      (if (equal kind updated-kind)
          (if (equal location updated-location)
              value
            (mtt-pmem-at old-map kind location))
        (mtt-pmem-at old-map kind location))))))

(defun-sk mtt-ext-p (tree left right)
  (forall (kind location)
    (implies
     (and
      (mtt-kind-p kind)
      (mtt-loc-p location)
      (mtt-footprint-member-p location tree))
     (equal
      (mtt-pmem-at left kind location)
      (mtt-pmem-at right kind location)))))

(defun mtt-unchanged-p (left right)
  (mtt-pointer-maps-equal-p left right))

(defun-sk mtt-was-marked-p
    (tree before after)
  (forall (location)
    (implies
     (mtt-loc-p location)
     (and
      (implies
       (mtt-footprint-member-p location tree)
       (equal (mtt-mark-at after location) t))
      (implies
       (not (mtt-footprint-member-p location tree))
       (equal
        (mtt-mark-at after location)
        (mtt-mark-at before location)))))))

(defun-sk mtt-all-other-marks-equal-p
    (new-map old-map distinguished)
  (forall (location)
    (implies
     (and
      (mtt-loc-p location)
      (not (equal location distinguished)))
     (equal
      (mtt-mark-at new-map location)
      (mtt-mark-at old-map location)))))

(defun-sk mtt-away-from-current-unchanged-p
    (left right current)
  (forall (kind location)
    (implies
     (and
      (mtt-kind-p kind)
      (mtt-loc-p location)
      (not (equal location current)))
     (equal
      (mtt-pmem-at left kind location)
      (mtt-pmem-at right kind location)))))

(defun mtt-next-phase (phase)
  (cond
   ((equal phase :go-left) :go-right)
   ((equal phase :go-right) :go-back)
   ((equal phase :go-back) :go-left)
   (t :finish)))

(defun mtt-rotated-p
    (initial current phase location)
  (and
   (mtt-away-from-current-unchanged-p
    initial current location)
   (implies
    (not (equal phase :finish))
    (not (equal location (mtt-null))))
   (cond
    ((equal phase :go-left)
     (mtt-unchanged-p initial current))
    ((equal phase :go-right)
     (and
      (equal
       (mtt-pmem-at current :left location)
       (mtt-pmem-at initial :right location))
      (equal
       (mtt-pmem-at current :right location)
       (mtt-pmem-at initial :parent location))
      (equal
       (mtt-pmem-at current :parent location)
       (mtt-pmem-at initial :left location))))
    ((equal phase :go-back)
     (and
      (equal
       (mtt-pmem-at initial :left location)
       (mtt-pmem-at current :right location))
      (equal
       (mtt-pmem-at initial :right location)
       (mtt-pmem-at current :parent location))
      (equal
       (mtt-pmem-at initial :parent location)
       (mtt-pmem-at current :left location))))
    (t
     (equal location (mtt-null))))))

(defun mtt-old-node-is-leaf-p (memory location)
  (and
   (equal
    (mtt-pmem-at
     (mtt-accessor memory)
     :left
     location)
    (mtt-null))
   (equal
    (mtt-null)
    (mtt-pmem-at
     (mtt-accessor memory)
     :right
     location))))

;; Common postcondition of one normal loop-body block.

(defun mtt-bloc-post-p
    (old-memory new-memory initial phase location)
  (and
   (equal
    (mtt-mark-at (mtt-marks new-memory) location)
    t)
   (mtt-all-other-marks-equal-p
    (mtt-marks new-memory)
    (mtt-marks old-memory)
    location)
   (if (mtt-old-node-is-leaf-p old-memory location)
       (mtt-pointer-maps-equal-p
        (mtt-accessor new-memory)
        (mtt-accessor old-memory))
     (mtt-rotated-p
      initial
      (mtt-accessor new-memory)
      (mtt-next-phase phase)
      location))))

;; First major conjunct: every call of the non-recursive loop-body block
;; satisfies the generated update and rotation obligations.

(defun mtt-bloc-final-update-conclusion-p
    (location memo1 initial phase memo2 memo5)
  (and
   (equal
    (mtt-pmem-at
     (mtt-accessor memo2)
     :left
     location)
    (mtt-pmem-at
     (mtt-accessor memo5)
     :parent
     location))
   (not (equal phase :finish))
   (equal
    (mtt-mark-at (mtt-marks memo5) location)
    t)
   (mtt-all-other-marks-equal-p
    (mtt-marks memo5)
    (mtt-marks memo1)
    location)
   (if (mtt-old-node-is-leaf-p memo1 location)
       (mtt-pointer-maps-equal-p
        (mtt-accessor memo5)
        (mtt-accessor memo1))
     (mtt-rotated-p
      initial
      (mtt-accessor memo5)
      (mtt-next-phase phase)
      location))))

(defun-sk mtt-all-bloc-memo5-p
    (location memo1 initial phase memo2 memo4)
  (forall (memo5)
    (implies
     (mtt-memory-p memo5)
     (implies
      (mtt-mark-maps-equal-p
       (mtt-marks memo5)
       (mtt-marks memo4))
      (implies
       (mtt-pointer-update-p
        (mtt-accessor memo5)
        (mtt-accessor memo4)
        :parent
        location
        (mtt-pmem-at
         (mtt-accessor memo2)
         :left
         location))
       (mtt-bloc-final-update-conclusion-p
        location memo1 initial phase memo2 memo5))))))

(defun-sk mtt-all-bloc-memo4-p
    (location memo1 initial phase memo2 memo3)
  (forall (memo4)
    (implies
     (mtt-memory-p memo4)
     (implies
      (mtt-mark-maps-equal-p
       (mtt-marks memo4)
       (mtt-marks memo3))
      (implies
       (mtt-pointer-update-p
        (mtt-accessor memo4)
        (mtt-accessor memo3)
        :right
        location
        (mtt-pmem-at
         (mtt-accessor memo3)
         :parent
         location))
       (and
        (not (equal location (mtt-null)))
        (mtt-all-bloc-memo5-p
         location
         memo1
         initial
         phase
         memo2
         memo4)))))))

(defun-sk mtt-all-bloc-memo3-p
    (location memo1 initial phase memo2)
  (forall (memo3)
    (implies
     (mtt-memory-p memo3)
     (implies
      (mtt-mark-maps-equal-p
       (mtt-marks memo3)
       (mtt-marks memo2))
      (implies
       (mtt-pointer-update-p
        (mtt-accessor memo3)
        (mtt-accessor memo2)
        :left
        location
        (mtt-pmem-at
         (mtt-accessor memo2)
         :right
         location))
       (and
        (not (equal location (mtt-null)))
        (mtt-all-bloc-memo4-p
         location
         memo1
         initial
         phase
         memo2
         memo3)))))))

(defun mtt-bloc-after-o4-p
    (o4 location memo1 initial phase memo2)
  (if (equal o4 t)
      (and
       (not (equal location (mtt-null)))
       (not (equal phase :finish))
       (mtt-bloc-post-p
        memo1 memo2 initial phase location))
    (and
     (not (equal location (mtt-null)))
     (not (equal location (mtt-null)))
     (not (equal location (mtt-null)))
     (mtt-all-bloc-memo3-p
      location memo1 initial phase memo2))))

(defun-sk mtt-all-o4-p
    (location memo1 initial phase memo2 o3)
  (forall (o4)
    (implies
     (mtt-bool-p o4)
     (implies
      (equal
       o4
       (if (equal o3 (mtt-null))
           (if
            (equal
             (mtt-pmem-at
              (mtt-accessor memo2)
              :right
              location)
             (mtt-null))
            t
          nil)
         nil))
      (mtt-bloc-after-o4-p
       o4 location memo1 initial phase memo2)))))

(defun mtt-bloc-after-memo2-p
    (location memo1 initial phase memo2)
  (and
   (not (equal location (mtt-null)))
   (let ((o3
          (mtt-pmem-at
           (mtt-accessor memo2)
           :left
           location)))
     (and
      (implies
       (equal o3 (mtt-null))
       (not (equal location (mtt-null))))
      (mtt-all-o4-p
       location memo1 initial phase memo2 o3)))))

(defun-sk mtt-all-bloc-memo2-p
    (location memo1 initial phase)
  (forall (memo2)
    (implies
     (mtt-memory-p memo2)
     (implies
      (mtt-pointer-maps-equal-p
       (mtt-accessor memo2)
       (mtt-accessor memo1))
      (implies
       (mtt-mark-true-update-p
        (mtt-marks memo2)
        (mtt-marks memo1)
        location)
       (mtt-bloc-after-memo2-p
        location memo1 initial phase memo2))))))

(defun mtt-bloc-after-o2-p
    (o2 location memo1 initial phase)
  (if (equal o2 t)
      (equal phase :finish)
    (and
     (not (equal location (mtt-null)))
     (mtt-all-bloc-memo2-p
      location memo1 initial phase))))

(defun-sk mtt-all-o2-p
    (entered location memo1 initial phase)
  (forall (o2)
    (implies
     (mtt-bool-p o2)
     (implies
      (equal
       o2
       (if (equal entered t)
           (if (equal location (mtt-null))
               t
             nil)
         nil))
      (mtt-bloc-after-o2-p
       o2 location memo1 initial phase)))))

(defun mtt-bloc-case-p
    (entered location memo1 initial phase)
  (implies
   (and
    (mtt-rotated-p
     initial
     (mtt-accessor memo1)
     phase
     location)
    (implies
     (equal phase :finish)
     (equal entered t)))
   (mtt-all-o2-p
    entered location memo1 initial phase)))

(defun-sk mtt-all-bloc-cases-p ()
  (forall (entered location memo1 initial phase)
    (implies
     (and
      (mtt-bool-p entered)
      (mtt-loc-p location)
      (mtt-memory-p memo1)
      (mtt-pointer-map-p initial)
      (mtt-phase-p phase))
     (mtt-bloc-case-p
      entered location memo1 initial phase))))

;; Second major conjunct: every recursive subtree call satisfies the generated
;; structural, frame, mark, and phase-transition obligations.

(defun mtt-tree-nonempty-p (tree)
  (not (equal tree nil)))

(defun mtt-subtrees-match-p (tree left right)
  (and
   (mtt-tree-nonempty-p tree)
   (equal left (mtt-tree-left tree))
   (equal right (mtt-tree-right tree))))

(defun mtt-child-of-p (tree subtree)
  (and
   (mtt-tree-nonempty-p tree)
   (or
    (equal (mtt-tree-left tree) subtree)
    (equal (mtt-tree-right tree) subtree))))

(defun-sk mtt-all-result-booleans-p
    (left-location right-location left-tree right-tree)
  (forall (result)
    (implies
     (mtt-bool-p result)
     (implies
      (equal
       result
       (if (equal left-location (mtt-null))
           (if (equal right-location (mtt-null))
               t
             nil)
         nil))
      (and
       (iff
        (equal result t)
        (and
         (equal left-location (mtt-null))
         (equal right-location (mtt-null))))
       (implies
        (equal result t)
        (and
         (equal left-tree nil)
         (equal right-tree nil))))))))

(defun mtt-recursive-final-post-p
    (initial-memory final-memory tree location parent)
  (and
   (mtt-unchanged-p
    (mtt-accessor initial-memory)
    (mtt-accessor final-memory))
   (equal
    (mtt-pmem-at
     (mtt-accessor final-memory)
     :parent
     location)
    parent)
   (mtt-was-marked-p
    tree
    (mtt-marks initial-memory)
    (mtt-marks final-memory))))

(defun-sk mtt-all-recursive-memo6-p
    (initial-memory tree initial location parent memo5)
  (forall (memo6)
    (implies
     (mtt-memory-p memo6)
     (implies
      (mtt-bloc-post-p
       memo5 memo6 initial :go-back location)
      (mtt-recursive-final-post-p
       initial-memory memo6 tree location parent)))))

(defun mtt-recursive-after-memo5-p
    (initial-memory tree initial location parent memo5)
  (and
   (mtt-rotated-p
    initial
    (mtt-accessor memo5)
    :go-back
    location)
   (mtt-all-recursive-memo6-p
    initial-memory tree initial location parent memo5)))

(defun-sk mtt-all-recursive-memo5-p
    (initial-memory tree right-tree initial
                    location parent memo4)
  (forall (memo5)
    (implies
     (mtt-memory-p memo5)
     (implies
      (and
       (mtt-unchanged-p
        (mtt-accessor memo4)
        (mtt-accessor memo5))
       (mtt-was-marked-p
        right-tree
        (mtt-marks memo4)
        (mtt-marks memo5)))
      (mtt-recursive-after-memo5-p
       initial-memory tree initial
       location parent memo5)))))

(defun mtt-recursive-after-memo4-p
    (initial-memory tree right-tree right-location
                    initial location parent memo4)
  (and
   (and
    (mtt-ext-p
     right-tree
     initial
     (mtt-accessor memo4))
    (mtt-is-tree-p
     initial
     right-tree
     right-location
     location))
   (implies
    (mtt-is-tree-p
     (mtt-accessor memo4)
     right-tree
     right-location
     location)
    (and
     (and
      (mtt-child-of-p tree right-tree)
      (not
       (equal
        (mtt-pmem-at
         (mtt-accessor memo4)
         :parent
         location)
        (mtt-null)))
      (mtt-is-tree-p
       (mtt-accessor memo4)
       right-tree
       (mtt-pmem-at
        (mtt-accessor memo4)
        :parent
        location)
       location))
     (mtt-all-recursive-memo5-p
      initial-memory tree right-tree initial
      location parent memo4)))))

(defun-sk mtt-all-recursive-memo4-p
    (initial-memory tree right-tree right-location
                    initial location parent memo3)
  (forall (memo4)
    (implies
     (mtt-memory-p memo4)
     (implies
      (mtt-bloc-post-p
       memo3 memo4 initial :go-right location)
      (mtt-recursive-after-memo4-p
       initial-memory tree right-tree right-location
       initial location parent memo4)))))

(defun mtt-recursive-after-memo3-p
    (initial-memory tree right-tree right-location
                    initial location parent memo3)
  (and
   (mtt-rotated-p
    initial
    (mtt-accessor memo3)
    :go-right
    location)
   (mtt-all-recursive-memo4-p
    initial-memory tree right-tree right-location
    initial location parent memo3)))

(defun-sk mtt-all-recursive-memo3-p
    (initial-memory tree left-tree right-tree right-location
                    initial location parent memo2)
  (forall (memo3)
    (implies
     (mtt-memory-p memo3)
     (implies
      (and
       (mtt-unchanged-p
        (mtt-accessor memo2)
        (mtt-accessor memo3))
       (mtt-was-marked-p
        left-tree
        (mtt-marks memo2)
        (mtt-marks memo3)))
      (mtt-recursive-after-memo3-p
       initial-memory tree right-tree right-location
       initial location parent memo3)))))

(defun mtt-recursive-nonleaf-after-memo2-p
    (initial-memory tree left-tree right-tree
                    left-location right-location
                    initial location parent memo2)
  (and
   (and
    (mtt-ext-p
     left-tree
     initial
     (mtt-accessor memo2))
    (mtt-is-tree-p
     initial
     left-tree
     left-location
     location))
   (implies
    (mtt-is-tree-p
     (mtt-accessor memo2)
     left-tree
     left-location
     location)
    (and
     (and
      (mtt-child-of-p tree left-tree)
      (not
       (equal
        (mtt-pmem-at
         (mtt-accessor memo2)
         :parent
         location)
        (mtt-null)))
      (mtt-is-tree-p
       (mtt-accessor memo2)
       left-tree
       (mtt-pmem-at
        (mtt-accessor memo2)
        :parent
        location)
       location))
     (mtt-all-recursive-memo3-p
      initial-memory tree left-tree right-tree
      right-location initial location parent memo2)))))

(defun mtt-recursive-after-memo2-p
    (initial-memory tree left-tree right-tree
                    left-location right-location
                    initial location parent memo2)
  (let ((both-null
         (and
          (equal left-location (mtt-null))
          (equal right-location (mtt-null)))))
    (and
     (mtt-all-result-booleans-p
      left-location right-location left-tree right-tree)
     (implies
      (implies
       both-null
       (and
        (equal left-tree nil)
        (equal right-tree nil)))
      (if (not both-null)
          (mtt-recursive-nonleaf-after-memo2-p
           initial-memory tree left-tree right-tree
           left-location right-location
           initial location parent memo2)
        (mtt-recursive-final-post-p
         initial-memory memo2 tree location parent))))))

(defun-sk mtt-all-recursive-memo2-p
    (initial-memory tree left-tree right-tree
                    left-location right-location
                    initial location parent)
  (forall (memo2)
    (implies
     (mtt-memory-p memo2)
     (implies
      (mtt-bloc-post-p
       initial-memory memo2 initial :go-left location)
      (mtt-recursive-after-memo2-p
       initial-memory tree left-tree right-tree
       left-location right-location
       initial location parent memo2)))))

(defun mtt-recursive-subtree-pair-case-p
    (initial-memory tree left-tree right-tree
                    left-location right-location
                    initial location parent)
  (and
   (mtt-is-tree-p
    initial
    (mtt-node left-tree location right-tree)
    location
    parent)
   (implies
    (and
     (not
      (mtt-footprint-member-p location left-tree))
     (not
      (mtt-footprint-member-p location right-tree)))
    (and
     (mtt-rotated-p
      initial
      (mtt-accessor initial-memory)
      :go-left
      location)
     (mtt-all-recursive-memo2-p
      initial-memory tree left-tree right-tree
      left-location right-location
      initial location parent)))))

(defun-sk mtt-all-subtree-pairs-p
    (initial-memory tree left-location right-location
                    initial location parent)
  (forall (left-tree right-tree)
    (implies
     (and
      (mtt-tree-p left-tree)
      (mtt-tree-p right-tree))
     (implies
      (mtt-subtrees-match-p
       tree left-tree right-tree)
      (mtt-recursive-subtree-pair-case-p
       initial-memory tree left-tree right-tree
       left-location right-location
       initial location parent)))))

(defun mtt-recursive-call-case-p
    (parent location initial-memory tree)
  (implies
   (and
    (not (equal location (mtt-null)))
    (mtt-is-tree-p
     (mtt-accessor initial-memory)
     tree
     location
     parent))
   (let* ((initial (mtt-accessor initial-memory))
          (left-location
           (mtt-pmem-at initial :left location))
          (right-location
           (mtt-pmem-at initial :right location)))
     (and
      (not (equal location (mtt-null)))
      (not (equal location (mtt-null)))
      (mtt-tree-nonempty-p tree)
      (mtt-all-subtree-pairs-p
       initial-memory tree left-location right-location
       initial location parent)))))

(defun-sk mtt-all-recursive-call-cases-p ()
  (forall (parent location initial-memory tree)
    (implies
     (and
      (mtt-loc-p parent)
      (mtt-loc-p location)
      (mtt-memory-p initial-memory)
      (mtt-tree-p tree))
     (mtt-recursive-call-case-p
      parent location initial-memory tree))))

;; Third major conjunct: the top recursive call and final Finish phase restore
;; the original accessors and establish the complete marking postcondition.

(defun mtt-finish-location-case-p
    (memory tree root initial final-memory location)
  (implies
   (mtt-rotated-p
    initial
    (mtt-accessor final-memory)
    :finish
    location)
   (and
    (mtt-rotated-p
     initial
     (mtt-accessor final-memory)
     :finish
     location)
    (and
     (and
      (mtt-ext-p
       tree initial (mtt-accessor final-memory))
      (mtt-is-tree-p
       initial tree root (mtt-null)))
     (implies
      (mtt-is-tree-p
       (mtt-accessor final-memory)
       tree
       root
       (mtt-null))
      (and
       (mtt-is-tree-p
        (mtt-accessor final-memory)
        tree
        root
        (mtt-null))
       (mtt-unchanged-p
        (mtt-accessor memory)
        (mtt-accessor final-memory))
       (mtt-was-marked-p
        tree
        (mtt-marks memory)
        (mtt-marks final-memory))))))))

(defun-sk mtt-all-finish-locations-p
    (memory tree root initial final-memory)
  (forall (location)
    (implies
     (mtt-loc-p location)
     (mtt-finish-location-case-p
      memory tree root initial final-memory location))))

(defun mtt-finish-memory-case-p
    (memory tree root initial final-memory)
  (implies
   (and
    (mtt-unchanged-p
     (mtt-accessor memory)
     (mtt-accessor final-memory))
    (mtt-was-marked-p
     tree
     (mtt-marks memory)
     (mtt-marks final-memory)))
   (and
    (mtt-rotated-p
     initial
     (mtt-accessor final-memory)
     :finish
     (mtt-null))
    (mtt-all-finish-locations-p
     memory tree root initial final-memory))))

(defun-sk mtt-all-finish-memories-p
    (memory tree root initial)
  (forall (final-memory)
    (implies
     (mtt-memory-p final-memory)
     (mtt-finish-memory-case-p
      memory tree root initial final-memory))))

(defun mtt-top-level-finish-p
    (memory tree root)
  (let ((initial (mtt-accessor memory)))
    (and
     (and
      (not (equal root (mtt-null)))
      (mtt-is-tree-p
       (mtt-accessor memory)
       tree
       root
       (mtt-null)))
     (mtt-all-finish-memories-p
      memory tree root initial))))

(defun-sk
  ntp4vc-pearl-verifythis-2016-tree-traversal-recursive-marktreeqtvc-statement
  ()
  (forall (memory tree root)
    (implies
     (and
      (mtt-interface-p)
      (mtt-memory-p memory)
      (mtt-tree-p tree)
      (mtt-loc-p root))
     (implies
      (and
       (mtt-is-tree-p
        (mtt-accessor memory)
        tree
        root
        (mtt-null))
       (not (equal root (mtt-null))))
      (and
       (mtt-all-bloc-cases-p)
       (mtt-all-recursive-call-cases-p)
       (mtt-top-level-finish-p
        memory tree root))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
