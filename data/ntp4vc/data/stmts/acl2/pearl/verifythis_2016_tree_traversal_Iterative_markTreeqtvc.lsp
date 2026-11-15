;; Statement-only formalization of the NTP4VC corpus artifact
;; pearl/verifythis_2016_tree_traversal_Iterative_markTreeqtvc: the
;; verification condition for iterative Morris-style binary-tree marking,
;; including snapshots, simulated call stacks, pointer rotations, marking,
;; and the integer termination measure. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source location type and the two source map types are arbitrary.
;; Defstubs provide conservative interfaces; all typing and extensional
;; properties used by the verification condition remain explicit below.

(defstub vtt-loc-p (*) => *)
(defstub vtt-ptr-map-p (*) => *)
(defstub vtt-mark-map-p (*) => *)
(defstub vtt-null () => *)
(defstub vtt-ptr-get (* * *) => *)
(defstub vtt-mark-get (* *) => *)

(defun vtt-kind-p (kind)
  (or (equal kind :parent)
      (equal kind :left)
      (equal kind :right)))

(defun-sk vtt-ptr-interface-typed-p ()
  (forall (map kind location)
    (implies
     (and (vtt-ptr-map-p map)
          (vtt-kind-p kind)
          (vtt-loc-p location))
     (vtt-loc-p (vtt-ptr-get map kind location)))))

(defun-sk vtt-mark-interface-typed-p ()
  (forall (map location)
    (implies
     (and (vtt-mark-map-p map)
          (vtt-loc-p location))
     (booleanp (vtt-mark-get map location)))))

;; Source map equality is functional extensional equality.

(defun-sk vtt-ptr-map-equal-p (left right)
  (forall (kind location)
    (implies
     (and (vtt-kind-p kind)
          (vtt-loc-p location))
     (equal (vtt-ptr-get left kind location)
            (vtt-ptr-get right kind location)))))

(defun-sk vtt-mark-map-equal-p (left right)
  (forall (location)
    (implies
     (vtt-loc-p location)
     (equal (vtt-mark-get left location)
            (vtt-mark-get right location)))))

(defun-sk vtt-ptr-map-update-equal-p
    (target base updated-kind updated-location updated-value)
  (forall (kind location)
    (implies
     (and (vtt-kind-p kind)
          (vtt-loc-p location))
     (equal
      (vtt-ptr-get target kind location)
      (if (and (equal kind updated-kind)
               (equal location updated-location))
          updated-value
        (vtt-ptr-get base kind location))))))

(defun-sk vtt-mark-map-update-equal-p
    (target base updated-location updated-value)
  (forall (location)
    (implies
     (vtt-loc-p location)
     (equal
      (vtt-mark-get target location)
      (if (equal location updated-location)
          updated-value
        (vtt-mark-get base location))))))

;; Exact records for memories and snapshots. Map-valued fields use the
;; extensional map interfaces above.

(defun vtt-memory (pointers marks)
  (list :vtt-memory pointers marks))

(defun vtt-memory-p (memory)
  (and (true-listp memory)
       (equal (len memory) 3)
       (equal (car memory) :vtt-memory)
       (vtt-ptr-map-p (cadr memory))
       (vtt-mark-map-p (caddr memory))))

(defun vtt-memory-pointers (memory)
  (cadr memory))

(defun vtt-memory-marks (memory)
  (caddr memory))

(defun vtt-snap (pointers cursor parent marks)
  (list :vtt-snap pointers cursor parent marks))

(defun vtt-snap-p (snap)
  (and (true-listp snap)
       (equal (len snap) 5)
       (equal (car snap) :vtt-snap)
       (vtt-ptr-map-p (cadr snap))
       (vtt-loc-p (caddr snap))
       (vtt-loc-p (cadddr snap))
       (vtt-mark-map-p (car (cddddr snap)))))

(defun vtt-snap-pointers (snap)
  (cadr snap))

(defun vtt-snap-cursor (snap)
  (caddr snap))

(defun vtt-snap-parent (snap)
  (cadddr snap))

(defun vtt-snap-marks (snap)
  (car (cddddr snap)))

(defun vtt-snap-equal-p (left right)
  (and
   (vtt-ptr-map-equal-p
    (vtt-snap-pointers left)
    (vtt-snap-pointers right))
   (equal (vtt-snap-cursor left)
          (vtt-snap-cursor right))
   (equal (vtt-snap-parent left)
          (vtt-snap-parent right))
   (vtt-mark-map-equal-p
    (vtt-snap-marks left)
    (vtt-snap-marks right))))

;; Exact inductive binary trees over locations.

(defun vtt-tree-empty ()
  (list :vtt-tree-empty))

(defun vtt-tree-node (left location right)
  (list :vtt-tree-node left location right))

(defun vtt-tree-empty-p (tree)
  (and (true-listp tree)
       (equal (len tree) 1)
       (equal (car tree) :vtt-tree-empty)))

(defun vtt-tree-node-p (tree)
  (and (true-listp tree)
       (equal (len tree) 4)
       (equal (car tree) :vtt-tree-node)))

(defun vtt-tree-left (tree)
  (cadr tree))

(defun vtt-tree-location (tree)
  (caddr tree))

(defun vtt-tree-right (tree)
  (cadddr tree))

(defun vtt-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((vtt-tree-empty-p tree) t)
   ((vtt-tree-node-p tree)
    (and (vtt-tree-p (vtt-tree-left tree))
         (vtt-loc-p (vtt-tree-location tree))
         (vtt-tree-p (vtt-tree-right tree))))
   (t nil)))

(defun vtt-tree-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (vtt-tree-node-p tree)
      (+ 1
         (vtt-tree-size (vtt-tree-left tree))
         (vtt-tree-size (vtt-tree-right tree)))
    0))

(defun vtt-tree-member-p (location tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (vtt-tree-node-p tree)
      (or (equal location (vtt-tree-location tree))
          (vtt-tree-member-p location (vtt-tree-left tree))
          (vtt-tree-member-p location (vtt-tree-right tree)))
    nil))

;; The Why3 is_tree predicate, translated definitionally.

(defun vtt-is-tree-p (pointers tree cursor parent)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((vtt-tree-empty-p tree)
    (equal cursor (vtt-null)))
   ((vtt-tree-node-p tree)
    (let ((left-cursor
           (vtt-ptr-get pointers :left cursor))
          (right-cursor
           (vtt-ptr-get pointers :right cursor)))
      (and
       (not (equal cursor (vtt-null)))
       (equal cursor (vtt-tree-location tree))
       (equal (vtt-ptr-get pointers :parent cursor)
              parent)
       (iff (equal left-cursor (vtt-null))
            (equal right-cursor (vtt-null)))
       (vtt-is-tree-p
        pointers (vtt-tree-left tree) left-cursor cursor)
       (vtt-is-tree-p
        pointers (vtt-tree-right tree) right-cursor cursor))))
   (t nil)))

(defun-sk vtt-tree-ext-p (tree left-pointers right-pointers)
  (forall (kind location)
    (implies
     (and (vtt-kind-p kind)
          (vtt-loc-p location)
          (vtt-tree-member-p location tree))
     (equal
      (vtt-ptr-get left-pointers kind location)
      (vtt-ptr-get right-pointers kind location)))))

(defun-sk vtt-was-marked-p (tree old-marks new-marks)
  (forall (location)
    (implies
     (vtt-loc-p location)
     (and
      (implies
       (vtt-tree-member-p location tree)
       (equal (vtt-mark-get new-marks location) t))
      (implies
       (not (vtt-tree-member-p location tree))
       (equal (vtt-mark-get new-marks location)
              (vtt-mark-get old-marks location)))))))

;; Pointer-rotation phases and their exact relation.

(defun vtt-phase-p (phase)
  (or (equal phase :go-left)
      (equal phase :go-right)
      (equal phase :go-back)
      (equal phase :finish)))

(defun vtt-next-phase (phase)
  (cond ((equal phase :go-left) :go-right)
        ((equal phase :go-right) :go-back)
        ((equal phase :go-back) :go-left)
        (t :finish)))

(defun-sk vtt-ptr-equal-off-location-p
    (left-pointers right-pointers excluded)
  (forall (kind location)
    (implies
     (and (vtt-kind-p kind)
          (vtt-loc-p location)
          (not (equal location excluded)))
     (equal
      (vtt-ptr-get left-pointers kind location)
      (vtt-ptr-get right-pointers kind location)))))

(defun vtt-rotated-p (old-pointers new-pointers phase cursor)
  (and
   (vtt-ptr-equal-off-location-p
    old-pointers new-pointers cursor)
   (implies
    (not (equal phase :finish))
    (not (equal cursor (vtt-null))))
   (cond
    ((equal phase :go-left)
     (vtt-ptr-map-equal-p old-pointers new-pointers))
    ((equal phase :go-right)
     (and
      (equal (vtt-ptr-get new-pointers :left cursor)
             (vtt-ptr-get old-pointers :right cursor))
      (equal (vtt-ptr-get new-pointers :right cursor)
             (vtt-ptr-get old-pointers :parent cursor))
      (equal (vtt-ptr-get new-pointers :parent cursor)
             (vtt-ptr-get old-pointers :left cursor))))
    ((equal phase :go-back)
     (and
      (equal (vtt-ptr-get old-pointers :left cursor)
             (vtt-ptr-get new-pointers :right cursor))
      (equal (vtt-ptr-get old-pointers :right cursor)
             (vtt-ptr-get new-pointers :parent cursor))
      (equal (vtt-ptr-get old-pointers :parent cursor)
             (vtt-ptr-get new-pointers :left cursor))))
    (t
     (equal cursor (vtt-null))))))

(defun-sk vtt-marks-equal-off-location-p
    (old-marks new-marks excluded)
  (forall (location)
    (implies
     (and (vtt-loc-p location)
          (not (equal location excluded)))
     (equal (vtt-mark-get new-marks location)
            (vtt-mark-get old-marks location)))))

(defun vtt-bloc-rel-p (initial-pointers phase before after)
  (and
   (equal (vtt-snap-parent after)
          (vtt-snap-cursor before))
   (equal
    (vtt-snap-cursor after)
    (vtt-ptr-get
     (vtt-snap-pointers after)
     :parent
     (vtt-snap-parent after)))
   (equal
    (vtt-mark-get
     (vtt-snap-marks after)
     (vtt-snap-parent after))
    t)
   (vtt-marks-equal-off-location-p
    (vtt-snap-marks before)
    (vtt-snap-marks after)
    (vtt-snap-parent after))
   (if
       (and
        (equal
         (vtt-ptr-get
          (vtt-snap-pointers before)
          :left
          (vtt-snap-cursor before))
         (vtt-null))
        (equal
         (vtt-null)
         (vtt-ptr-get
          (vtt-snap-pointers before)
          :right
          (vtt-snap-cursor before))))
       (vtt-ptr-map-equal-p
        (vtt-snap-pointers after)
        (vtt-snap-pointers before))
     (vtt-rotated-p
      initial-pointers
      (vtt-snap-pointers after)
      (vtt-next-phase phase)
      (vtt-snap-parent after)))))

(defun vtt-rec-rel-p (tree before after)
  (and
   (vtt-ptr-map-equal-p
    (vtt-snap-pointers before)
    (vtt-snap-pointers after))
   (equal (vtt-snap-cursor after)
          (vtt-snap-parent before))
   (equal (vtt-snap-parent after)
          (vtt-snap-cursor before))
   (vtt-was-marked-p
    tree
    (vtt-snap-marks before)
    (vtt-snap-marks after))))

;; Exact stack-frame records.

(defun vtt-frame
    (memo0 tree tleft pleft tright pright memo1 memo2 memo3 memo4)
  (list :vtt-frame memo0 tree tleft pleft tright pright
        memo1 memo2 memo3 memo4))

(defun vtt-frame-p (frame)
  (and
   (true-listp frame)
   (equal (len frame) 11)
   (equal (car frame) :vtt-frame)
   (vtt-snap-p (nth 1 frame))
   (vtt-tree-p (nth 2 frame))
   (vtt-tree-p (nth 3 frame))
   (vtt-loc-p (nth 4 frame))
   (vtt-tree-p (nth 5 frame))
   (vtt-loc-p (nth 6 frame))
   (vtt-snap-p (nth 7 frame))
   (vtt-snap-p (nth 8 frame))
   (vtt-snap-p (nth 9 frame))
   (vtt-snap-p (nth 10 frame))))

(defun vtt-frame-memo0 (frame) (nth 1 frame))
(defun vtt-frame-tree (frame) (nth 2 frame))
(defun vtt-frame-tleft (frame) (nth 3 frame))
(defun vtt-frame-pleft (frame) (nth 4 frame))
(defun vtt-frame-tright (frame) (nth 5 frame))
(defun vtt-frame-pright (frame) (nth 6 frame))
(defun vtt-frame-memo1 (frame) (nth 7 frame))
(defun vtt-frame-memo2 (frame) (nth 8 frame))
(defun vtt-frame-memo3 (frame) (nth 9 frame))
(defun vtt-frame-memo4 (frame) (nth 10 frame))

(defun vtt-frame-memo (frame pc)
  (cond ((<= pc 0) (vtt-frame-memo0 frame))
        ((<= pc 1) (vtt-frame-memo1 frame))
        ((<= pc 2) (vtt-frame-memo2 frame))
        ((<= pc 3) (vtt-frame-memo3 frame))
        (t (vtt-frame-memo4 frame))))

;; Exact source options over trees.

(defun vtt-none ()
  (list :vtt-none))

(defun vtt-some (tree)
  (list :vtt-some tree))

(defun vtt-none-p (option)
  (and (true-listp option)
       (equal (len option) 1)
       (equal (car option) :vtt-none)))

(defun vtt-some-p (option)
  (and (true-listp option)
       (equal (len option) 2)
       (equal (car option) :vtt-some)
       (vtt-tree-p (cadr option))))

(defun vtt-option-tree-p (option)
  (or (vtt-none-p option)
      (vtt-some-p option)))

(defun vtt-option-tree-value (option)
  (cadr option))

;; Exact source stack datatype and recursive invariant.

(defun vtt-bottom ()
  (list :vtt-bottom))

(defun vtt-done ()
  (list :vtt-done))

(defun vtt-running (stack pc frame)
  (list :vtt-running stack pc frame))

(defun vtt-bottom-p (stack)
  (and (true-listp stack)
       (equal (len stack) 1)
       (equal (car stack) :vtt-bottom)))

(defun vtt-done-p (stack)
  (and (true-listp stack)
       (equal (len stack) 1)
       (equal (car stack) :vtt-done)))

(defun vtt-running-p (stack)
  (and (true-listp stack)
       (equal (len stack) 4)
       (equal (car stack) :vtt-running)))

(defun vtt-running-stack (stack)
  (cadr stack))

(defun vtt-running-pc (stack)
  (caddr stack))

(defun vtt-running-frame (stack)
  (cadddr stack))

(defun vtt-stack-p (stack)
  (declare (xargs :measure (acl2-count stack)))
  (cond
   ((vtt-bottom-p stack) t)
   ((vtt-done-p stack) t)
   ((vtt-running-p stack)
    (and
     (vtt-stack-p (vtt-running-stack stack))
     (integerp (vtt-running-pc stack))
     (vtt-frame-p (vtt-running-frame stack))))
   (t nil)))

(defun vtt-is-stack-p (tree stop current stack calls)
  (declare (xargs :measure (acl2-count stack)))
  (cond
   ((vtt-bottom-p stack)
    (and
     (vtt-snap-equal-p stop current)
     (vtt-some-p calls)
     (equal (vtt-option-tree-value calls) tree)))
   ((vtt-running-p stack)
    (let* ((previous-stack (vtt-running-stack stack))
           (pc (vtt-running-pc stack))
           (frame (vtt-running-frame stack))
           (memo0 (vtt-frame-memo0 frame)))
      (and
       (<= 0 pc)
       (<= pc 4)
       (vtt-is-stack-p
        tree stop memo0 previous-stack
        (vtt-some (vtt-frame-tree frame)))
       (not (equal (vtt-snap-cursor memo0) (vtt-null)))
       (vtt-is-tree-p
        (vtt-snap-pointers memo0)
        (vtt-frame-tree frame)
        (vtt-snap-cursor memo0)
        (vtt-snap-parent memo0))
       (equal
        (vtt-frame-tree frame)
        (vtt-tree-node
         (vtt-frame-tleft frame)
         (vtt-snap-cursor memo0)
         (vtt-frame-tright frame)))
       (equal
        (vtt-frame-pleft frame)
        (vtt-ptr-get
         (vtt-snap-pointers memo0)
         :left
         (vtt-snap-cursor memo0)))
       (equal
        (vtt-frame-pright frame)
        (vtt-ptr-get
         (vtt-snap-pointers memo0)
         :right
         (vtt-snap-cursor memo0)))
       (implies
        (<= 1 pc)
        (and
         (vtt-bloc-rel-p
          (vtt-snap-pointers memo0)
          :go-left
          memo0
          (vtt-frame-memo1 frame))
         (not (equal (vtt-frame-pleft frame) (vtt-null)))
         (not (equal (vtt-frame-pright frame) (vtt-null)))))
       (implies
        (<= 2 pc)
        (vtt-rec-rel-p
         (vtt-frame-tleft frame)
         (vtt-frame-memo1 frame)
         (vtt-frame-memo2 frame)))
       (implies
        (<= 3 pc)
        (vtt-bloc-rel-p
         (vtt-snap-pointers memo0)
         :go-right
         (vtt-frame-memo2 frame)
         (vtt-frame-memo3 frame)))
       (implies
        (<= 4 pc)
        (vtt-rec-rel-p
         (vtt-frame-tright frame)
         (vtt-frame-memo3 frame)
         (vtt-frame-memo4 frame)))
       (vtt-snap-equal-p
        (vtt-frame-memo frame pc)
        current)
       (if (vtt-none-p calls)
           (and (not (equal pc 1))
                (not (equal pc 3)))
         (and
          (vtt-some-p calls)
          (if (equal pc 1)
              (equal (vtt-option-tree-value calls)
                     (vtt-frame-tleft frame))
            (and
             (equal pc 3)
             (equal (vtt-option-tree-value calls)
                    (vtt-frame-tright frame)))))))))
   ((vtt-done-p stack)
    (and
     (vtt-rec-rel-p tree stop current)
     (vtt-none-p calls)))
   (t nil)))

(defun vtt-stack-size (stack)
  (declare (xargs :measure (acl2-count stack)))
  (cond
   ((vtt-bottom-p stack) 1)
   ((vtt-done-p stack) 0)
   ((vtt-running-p stack)
    (let* ((previous-stack (vtt-running-stack stack))
           (pc (vtt-running-pc stack))
           (frame (vtt-running-frame stack)))
      (+
       (vtt-stack-size previous-stack)
       (- 100 pc)
       (cond
        ((equal pc 0)
         (* 100
            (+ (vtt-tree-size (vtt-frame-tleft frame))
               (vtt-tree-size (vtt-frame-tright frame)))))
        ((<= pc 2)
         (* 100
            (vtt-tree-size (vtt-frame-tright frame))))
        (t 0)))))
   (t 0)))

(defun vtt-current-phase (stack)
  (if (vtt-running-p stack)
      (let ((pc (vtt-running-pc stack)))
        (cond ((equal pc 0) :go-left)
              ((equal pc 2) :go-right)
              (t :go-back)))
    :finish))

;; Universal branch predicates for the verification condition.

(defun vtt-result-body-p (current entered result)
  (implies
   (booleanp result)
   (implies
    (equal
     result
     (if (equal entered t)
         (if (equal (vtt-snap-cursor current)
                    (vtt-null))
             t
           nil)
       nil))
    (iff (equal result t)
         (equal (vtt-snap-cursor current)
                (vtt-null))))))

(defun-sk vtt-all-results-p (current entered)
  (forall (result)
    (vtt-result-body-p current entered result)))

(defun vtt-return-stack-body-p
    (tree stop next-snap old-stack current next-stack
          next-pointers next-cursor next-marks)
  (implies
   (vtt-stack-p next-stack)
   (implies
    (and
     (vtt-is-stack-p
      tree stop next-snap next-stack (vtt-none))
     (< (vtt-stack-size next-stack)
        (vtt-stack-size old-stack)))
    (and
     (<= 0 (vtt-stack-size old-stack))
     (< (vtt-stack-size next-stack)
        (vtt-stack-size old-stack))
     (implies
      (equal next-cursor (vtt-null))
      t)
     (vtt-ptr-map-equal-p
      (vtt-snap-pointers next-snap)
      next-pointers)
     (equal (vtt-snap-cursor next-snap)
            next-cursor)
     (equal (vtt-snap-parent next-snap)
            (vtt-snap-cursor current))
     (vtt-mark-map-equal-p
      (vtt-snap-marks next-snap)
      next-marks)
     (vtt-is-stack-p
      tree stop next-snap next-stack (vtt-none))))))

(defun-sk vtt-all-return-stacks-p
    (tree stop next-snap old-stack current
          next-pointers next-cursor next-marks)
  (forall (next-stack)
    (vtt-return-stack-body-p
     tree stop next-snap old-stack current next-stack
     next-pointers next-cursor next-marks)))

(defun vtt-leaf-snap-body-p
    (tree stop current old-stack memory6 next-snap)
  (implies
   (vtt-snap-p next-snap)
   (implies
    (and
     (vtt-ptr-map-equal-p
      (vtt-snap-pointers next-snap)
      (vtt-memory-pointers memory6))
     (equal
      (vtt-snap-cursor next-snap)
      (vtt-ptr-get
       (vtt-memory-pointers memory6)
       :parent
       (vtt-snap-cursor current)))
     (equal (vtt-snap-parent next-snap)
            (vtt-snap-cursor current))
     (vtt-mark-map-equal-p
      (vtt-snap-marks next-snap)
      (vtt-memory-marks memory6)))
    (and
     (and
      (vtt-is-stack-p
       tree stop current old-stack (vtt-none))
      (and
       (vtt-running-p old-stack)
       (vtt-bloc-rel-p
        (vtt-snap-pointers
         (vtt-frame-memo0
          (vtt-running-frame old-stack)))
        (vtt-current-phase old-stack)
        current
        next-snap)))
     (vtt-all-return-stacks-p
      tree stop next-snap old-stack current
      (vtt-memory-pointers memory6)
      (vtt-ptr-get
       (vtt-memory-pointers memory6)
       :parent
       (vtt-snap-cursor current))
      (vtt-memory-marks memory6))))))

(defun-sk vtt-all-leaf-snaps-p
    (tree stop current old-stack memory6)
  (forall (next-snap)
    (vtt-leaf-snap-body-p
     tree stop current old-stack memory6 next-snap)))

(defun vtt-rotated-snap-body-p
    (tree stop current old-stack memory6 memory9 next-snap)
  (implies
   (vtt-snap-p next-snap)
   (implies
    (and
     (vtt-ptr-map-equal-p
      (vtt-snap-pointers next-snap)
      (vtt-memory-pointers memory9))
     (equal
      (vtt-snap-cursor next-snap)
      (vtt-ptr-get
       (vtt-memory-pointers memory6)
       :left
       (vtt-snap-cursor current)))
     (equal (vtt-snap-parent next-snap)
            (vtt-snap-cursor current))
     (vtt-mark-map-equal-p
      (vtt-snap-marks next-snap)
      (vtt-memory-marks memory9)))
    (and
     (and
      (vtt-is-stack-p
       tree stop current old-stack (vtt-none))
      (and
       (vtt-running-p old-stack)
       (vtt-bloc-rel-p
        (vtt-snap-pointers
         (vtt-frame-memo0
          (vtt-running-frame old-stack)))
        (vtt-current-phase old-stack)
        current
        next-snap)))
     (vtt-all-return-stacks-p
      tree stop next-snap old-stack current
      (vtt-memory-pointers memory9)
      (vtt-ptr-get
       (vtt-memory-pointers memory6)
       :left
       (vtt-snap-cursor current))
      (vtt-memory-marks memory9))))))

(defun-sk vtt-all-rotated-snaps-p
    (tree stop current old-stack memory6 memory9)
  (forall (next-snap)
    (vtt-rotated-snap-body-p
     tree stop current old-stack memory6 memory9 next-snap)))

(defun vtt-memory9-body-p
    (tree stop current old-stack memory6 memory8 memory9)
  (implies
   (vtt-memory-p memory9)
   (implies
    (vtt-mark-map-equal-p
     (vtt-memory-marks memory9)
     (vtt-memory-marks memory8))
    (implies
     (vtt-ptr-map-update-equal-p
      (vtt-memory-pointers memory9)
      (vtt-memory-pointers memory8)
      :parent
      (vtt-snap-cursor current)
      (vtt-ptr-get
       (vtt-memory-pointers memory6)
       :left
       (vtt-snap-cursor current)))
     (vtt-all-rotated-snaps-p
      tree stop current old-stack memory6 memory9)))))

(defun-sk vtt-all-memory9-p
    (tree stop current old-stack memory6 memory8)
  (forall (memory9)
    (vtt-memory9-body-p
     tree stop current old-stack memory6 memory8 memory9)))

(defun vtt-memory8-body-p
    (tree stop current old-stack memory6 memory7 memory8)
  (implies
   (vtt-memory-p memory8)
   (implies
    (vtt-mark-map-equal-p
     (vtt-memory-marks memory8)
     (vtt-memory-marks memory7))
    (implies
     (vtt-ptr-map-update-equal-p
      (vtt-memory-pointers memory8)
      (vtt-memory-pointers memory7)
      :right
      (vtt-snap-cursor current)
      (vtt-ptr-get
       (vtt-memory-pointers memory7)
       :parent
       (vtt-snap-cursor current)))
     (and
      (not (equal (vtt-snap-cursor current)
                  (vtt-null)))
      (vtt-all-memory9-p
       tree stop current old-stack memory6 memory8))))))

(defun-sk vtt-all-memory8-p
    (tree stop current old-stack memory6 memory7)
  (forall (memory8)
    (vtt-memory8-body-p
     tree stop current old-stack memory6 memory7 memory8)))

(defun vtt-memory7-body-p
    (tree stop current old-stack memory6 memory7)
  (implies
   (vtt-memory-p memory7)
   (implies
    (vtt-mark-map-equal-p
     (vtt-memory-marks memory7)
     (vtt-memory-marks memory6))
    (implies
     (vtt-ptr-map-update-equal-p
      (vtt-memory-pointers memory7)
      (vtt-memory-pointers memory6)
      :left
      (vtt-snap-cursor current)
      (vtt-ptr-get
       (vtt-memory-pointers memory6)
       :right
       (vtt-snap-cursor current)))
     (and
      (not (equal (vtt-snap-cursor current)
                  (vtt-null)))
      (vtt-all-memory8-p
       tree stop current old-stack memory6 memory7))))))

(defun-sk vtt-all-memory7-p
    (tree stop current old-stack memory6)
  (forall (memory7)
    (vtt-memory7-body-p
     tree stop current old-stack memory6 memory7)))

(defun vtt-o3-body-p
    (tree stop current old-stack memory6 left-child o3)
  (implies
   (booleanp o3)
   (implies
    (equal
     o3
     (if (equal left-child (vtt-null))
         (if
             (equal
              (vtt-ptr-get
               (vtt-memory-pointers memory6)
               :right
               (vtt-snap-cursor current))
              (vtt-null))
             t
           nil)
       nil))
    (if (equal o3 t)
        (and
         (not (equal (vtt-snap-cursor current)
                     (vtt-null)))
         (vtt-all-leaf-snaps-p
          tree stop current old-stack memory6))
      (and
       (not (equal (vtt-snap-cursor current)
                   (vtt-null)))
       (not (equal (vtt-snap-cursor current)
                   (vtt-null)))
       (not (equal (vtt-snap-cursor current)
                   (vtt-null)))
       (vtt-all-memory7-p
        tree stop current old-stack memory6))))))

(defun-sk vtt-all-o3-p
    (tree stop current old-stack memory6 left-child)
  (forall (o3)
    (vtt-o3-body-p
     tree stop current old-stack memory6 left-child o3)))

(defun vtt-memory6-body-p
    (tree stop current old-stack memory5 memory6)
  (implies
   (vtt-memory-p memory6)
   (implies
    (vtt-ptr-map-equal-p
     (vtt-memory-pointers memory6)
     (vtt-memory-pointers memory5))
    (implies
     (vtt-mark-map-update-equal-p
      (vtt-memory-marks memory6)
      (vtt-memory-marks memory5)
      (vtt-snap-cursor current)
      t)
     (and
      (not (equal (vtt-snap-cursor current)
                  (vtt-null)))
      (let ((left-child
             (vtt-ptr-get
              (vtt-memory-pointers memory6)
              :left
              (vtt-snap-cursor current))))
        (and
         (implies
          (equal left-child (vtt-null))
          (not (equal (vtt-snap-cursor current)
                      (vtt-null))))
         (vtt-all-o3-p
          tree stop current old-stack memory6 left-child))))))))

(defun-sk vtt-all-memory6-p
    (tree stop current old-stack memory5)
  (forall (memory6)
    (vtt-memory6-body-p
     tree stop current old-stack memory5 memory6)))

(defun vtt-done-branch-p
    (tree root stop old-stack initial-memory memory5)
  (and
   (vtt-done-p old-stack)
   (implies
    (vtt-done-p old-stack)
    (and
     (and
      (vtt-tree-ext-p
       tree
       (vtt-snap-pointers stop)
       (vtt-memory-pointers memory5))
     (vtt-is-tree-p
       (vtt-snap-pointers stop)
       tree
       root
       (vtt-null)))
     (implies
      (vtt-is-tree-p
       (vtt-memory-pointers memory5)
       tree
       root
       (vtt-null))
      (and
       (vtt-is-tree-p
        (vtt-memory-pointers memory5)
        tree
        root
        (vtt-null))
       (vtt-ptr-map-equal-p
        (vtt-memory-pointers initial-memory)
        (vtt-memory-pointers memory5))
       (vtt-was-marked-p
        tree
        (vtt-memory-marks initial-memory)
        (vtt-memory-marks memory5))))))))

(defun vtt-loop-state-body-p
    (tree root stop initial-memory entered old-stack current memory5)
  (implies
   (and (booleanp entered)
        (vtt-stack-p old-stack)
        (vtt-snap-p current)
        (vtt-memory-p memory5))
   (implies
    (and
     (implies
      (equal (vtt-snap-cursor current)
             (vtt-null))
      (equal entered t))
     (vtt-ptr-map-equal-p
      (vtt-snap-pointers current)
      (vtt-memory-pointers memory5))
     (vtt-mark-map-equal-p
      (vtt-snap-marks current)
      (vtt-memory-marks memory5))
     (vtt-is-stack-p
      tree stop current old-stack (vtt-none)))
    (and
     (vtt-all-results-p current entered)
     (if
         (not (equal (vtt-snap-cursor current)
                     (vtt-null)))
         (and
          (not (equal (vtt-snap-cursor current)
                      (vtt-null)))
          (vtt-all-memory6-p
           tree stop current old-stack memory5))
       (vtt-done-branch-p
        tree root stop old-stack initial-memory memory5))))))

(defun-sk vtt-all-loop-states-p
    (tree root stop initial-memory)
  (forall (entered old-stack current memory5)
    (vtt-loop-state-body-p
     tree root stop initial-memory entered old-stack current memory5)))

(defun vtt-stack-body-p (tree root stop initial-memory stack)
  (implies
   (vtt-stack-p stack)
   (implies
    (and
     (vtt-is-stack-p
      tree stop stop stack (vtt-none))
     (<=
      (vtt-stack-size stack)
      (+ (vtt-stack-size (vtt-bottom))
         (* 100 (vtt-tree-size tree)))))
    (and
     (and
      (not (equal root
                  (vtt-null)))
      (vtt-ptr-map-equal-p
       (vtt-snap-pointers stop)
       (vtt-memory-pointers initial-memory))
      (equal (vtt-snap-cursor stop)
             root)
      (equal (vtt-snap-parent stop)
             (vtt-null))
      (vtt-mark-map-equal-p
       (vtt-snap-marks stop)
       (vtt-memory-marks initial-memory))
      (vtt-is-stack-p
       tree stop stop stack (vtt-none)))
     (vtt-all-loop-states-p
      tree root stop initial-memory)))))

(defun-sk vtt-all-stacks-p (tree root stop initial-memory)
  (forall (stack)
    (vtt-stack-body-p tree root stop initial-memory stack)))

(defun vtt-stop-body-p (tree root initial-memory stop)
  (implies
   (vtt-snap-p stop)
   (implies
    (and
     (vtt-ptr-map-equal-p
      (vtt-snap-pointers stop)
      (vtt-memory-pointers initial-memory))
     (equal (vtt-snap-cursor stop) root)
     (equal (vtt-snap-parent stop) (vtt-null))
     (vtt-mark-map-equal-p
      (vtt-snap-marks stop)
      (vtt-memory-marks initial-memory)))
    (and
     (and
      (vtt-is-stack-p
       tree stop stop (vtt-bottom) (vtt-some tree))
      (vtt-is-tree-p
       (vtt-snap-pointers stop)
       tree
       (vtt-snap-cursor stop)
       (vtt-snap-parent stop))
      (not (equal (vtt-snap-cursor stop)
                  (vtt-null))))
     (vtt-all-stacks-p tree root stop initial-memory)))))

(defun-sk vtt-all-stops-p (tree root initial-memory)
  (forall (stop)
    (vtt-stop-body-p tree root initial-memory stop)))

(defun vtt-top-body-p (initial-memory tree root)
  (implies
   (and
    (vtt-memory-p initial-memory)
    (vtt-tree-p tree)
    (vtt-loc-p root))
   (implies
    (and
     (vtt-is-tree-p
      (vtt-memory-pointers initial-memory)
      tree root (vtt-null))
     (not (equal root (vtt-null))))
    (vtt-all-stops-p tree root initial-memory))))

(defun-sk
  ntp4vc-pearl-verifythis-2016-tree-traversal-iterative-marktreeqtvc-statement
  ()
  (forall (initial-memory tree root)
    (implies
     (and
      (vtt-loc-p (vtt-null))
      (vtt-ptr-interface-typed-p)
      (vtt-mark-interface-typed-p))
     (vtt-top-body-p initial-memory tree root))))

(value-triple :itpeval-statement-checked)
:q
