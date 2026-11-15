;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/vstte12_bfs_BFS_bfsqtvc: the breadth-first-search verification
;; condition for shortest-path frontier invariants, successor closure, target
;; detection, frontier rotation, and failure when no path exists. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces preserve the arbitrary inhabited source vertex and
;; mutable-set carriers. Their typing and specification laws are explicit in
;; the final statement predicate.

(defstub bfsq-vertex-p (x) t)
(defstub bfsq-set-p (x) t)
(defstub bfsq-default-vertex () t)
(defstub bfsq-default-set () t)
(defstub bfsq-to-fset (set) t)
(defstub bfsq-choose (set) t)
(defstub bfsq-vertex-eq (left right) t)
(defstub bfsq-successors (vertex) t)

;; Duplicate-free proper lists represent finite sets of source vertices.
;; Equality and all set operations below are extensional, so list order is
;; irrelevant.

(defun bfsq-vertex-fset-p (set)
  (if (consp set)
      (and
       (bfsq-vertex-p (car set))
       (not (member-equal (car set) (cdr set)))
       (bfsq-vertex-fset-p (cdr set)))
    (equal set nil)))

(defun bfsq-fset-subset-p (left right)
  (if (consp left)
      (and
       (member-equal (car left) right)
       (bfsq-fset-subset-p (cdr left) right))
    (equal left nil)))

(defun bfsq-fset-equal-p (left right)
  (and
   (bfsq-fset-subset-p left right)
   (bfsq-fset-subset-p right left)))

(defun bfsq-fset-insert (vertex set)
  (if (member-equal vertex set)
      set
    (cons vertex set)))

(defun bfsq-fset-remove (vertex set)
  (if (consp set)
      (if (equal vertex (car set))
          (cdr set)
        (cons
         (car set)
         (bfsq-fset-remove vertex (cdr set))))
    nil))

;; A nonempty finite vertex sequence is constructor evidence for the source
;; inductive path relation. A singleton is path_empty, and each additional
;; vertex is one application of path_succ.

(defun bfsq-vertex-list-p (vertices)
  (if (consp vertices)
      (and
       (bfsq-vertex-p (car vertices))
       (bfsq-vertex-list-p (cdr vertices)))
    (equal vertices nil)))

(defun bfsq-path-edges-p (vertices)
  (if (and
       (consp vertices)
       (consp (cdr vertices)))
      (and
       (member-equal
        (cadr vertices)
        (bfsq-successors (car vertices)))
       (bfsq-path-edges-p (cdr vertices)))
    (and
     (consp vertices)
     (equal (cdr vertices) nil))))

(defun bfsq-path-witness-p
    (vertices source target length)
  (and
   (integerp length)
   (<= 0 length)
   (bfsq-vertex-list-p vertices)
   (consp vertices)
   (equal (len vertices) (+ length 1))
   (equal (car vertices) source)
   (equal (car (last vertices)) target)
   (bfsq-path-edges-p vertices)))

(defun-sk bfsq-path-p (source target length)
  (exists (vertices)
    (and
     (bfsq-vertex-p source)
     (bfsq-vertex-p target)
     (bfsq-path-witness-p
      vertices source target length))))

(defun-sk bfsq-no-shorter-path-p
    (source target length)
  (forall (other-length)
    (implies
     (integerp other-length)
     (implies
      (< other-length length)
      (not
       (bfsq-path-p
        source target other-length))))))

(defun bfsq-shortest-path-p
    (source target length)
  (and
   (bfsq-path-p source target length)
   (bfsq-no-shorter-path-p
    source target length)))

;; Source-context laws for the two abstract carriers, finite successor sets,
;; set conversion and choice, and the executable equality predicate.

(defun-sk bfsq-vertex-inhabited-p ()
  (exists (vertex)
    (bfsq-vertex-p vertex)))

(defun-sk bfsq-set-inhabited-p ()
  (exists (set)
    (bfsq-set-p set)))

(defun-sk bfsq-successor-interface-p ()
  (forall (vertex)
    (implies
     (bfsq-vertex-p vertex)
     (bfsq-vertex-fset-p
      (bfsq-successors vertex)))))

(defun-sk bfsq-set-interface-p ()
  (forall (set)
    (implies
     (bfsq-set-p set)
     (and
      (bfsq-vertex-fset-p
       (bfsq-to-fset set))
      (bfsq-vertex-p
       (bfsq-choose set))
      (implies
       (not
        (equal
         (bfsq-to-fset set)
         nil))
       (member-equal
        (bfsq-choose set)
        (bfsq-to-fset set)))))))

(defun-sk bfsq-equality-interface-p ()
  (forall (left right)
    (implies
     (and
      (bfsq-vertex-p left)
      (bfsq-vertex-p right))
     (iff
      (bfsq-vertex-eq left right)
      (equal left right)))))

(defun bfsq-background-p ()
  (and
   (bfsq-vertex-p
    (bfsq-default-vertex))
   (bfsq-set-p
    (bfsq-default-set))
   (bfsq-vertex-inhabited-p)
   (bfsq-set-inhabited-p)
   (bfsq-successor-interface-p)
   (bfsq-set-interface-p)
   (bfsq-equality-interface-p)))

;; Exact components of the global breadth-first-search invariant.

(defun-sk bfsq-current-shortest-p
    (source current depth)
  (forall (vertex)
    (implies
     (bfsq-vertex-p vertex)
     (implies
      (member-equal vertex current)
      (bfsq-shortest-path-p
       source vertex depth)))))

(defun-sk bfsq-next-shortest-p
    (source next depth)
  (forall (vertex)
    (implies
     (bfsq-vertex-p vertex)
     (implies
      (member-equal vertex next)
      (bfsq-shortest-path-p
       source vertex (+ depth 1))))))

(defun-sk bfsq-short-paths-visited-p
    (source visited depth)
  (forall (vertex length)
    (implies
     (and
      (bfsq-vertex-p vertex)
      (integerp length))
     (implies
      (and
       (bfsq-path-p source vertex length)
       (<= length depth))
      (member-equal vertex visited)))))

(defun-sk bfsq-has-bounded-path-p
    (source vertex bound)
  (exists (length)
    (and
     (integerp length)
     (bfsq-path-p source vertex length)
     (<= length bound))))

(defun-sk bfsq-visited-path-bounds-p
    (source visited depth)
  (forall (vertex)
    (implies
     (bfsq-vertex-p vertex)
     (implies
      (member-equal vertex visited)
      (bfsq-has-bounded-path-p
       source vertex (+ depth 1))))))

(defun-sk bfsq-next-or-unvisited-p
    (source visited next depth)
  (forall (vertex)
    (implies
     (bfsq-vertex-p vertex)
     (implies
      (bfsq-shortest-path-p
       source vertex (+ depth 1))
      (or
       (member-equal vertex next)
       (not
        (member-equal vertex visited)))))))

(defun bfsq-invariant-p
    (source target visited current next depth)
  (and
   (bfsq-vertex-p source)
   (bfsq-vertex-p target)
   (bfsq-vertex-fset-p visited)
   (bfsq-vertex-fset-p current)
   (bfsq-vertex-fset-p next)
   (integerp depth)
   (bfsq-fset-subset-p current visited)
   (bfsq-current-shortest-p
    source current depth)
   (bfsq-fset-subset-p next visited)
   (bfsq-next-shortest-p
    source next depth)
   (bfsq-short-paths-visited-p
    source visited depth)
   (bfsq-visited-path-bounds-p
    source visited depth)
   (bfsq-next-or-unvisited-p
    source visited next depth)
   (implies
    (member-equal target visited)
    (or
     (member-equal target current)
     (member-equal target next)))))

;; The source closure predicate and its universally quantified variants.

(defun-sk bfsq-successors-visited-p
    (visited vertex)
  (forall (successor)
    (implies
     (bfsq-vertex-p successor)
     (implies
      (member-equal
       successor
       (bfsq-successors vertex))
      (member-equal successor visited)))))

(defun bfsq-closure-p
    (visited current next vertex)
  (and
   (bfsq-vertex-fset-p visited)
   (bfsq-vertex-fset-p current)
   (bfsq-vertex-fset-p next)
   (bfsq-vertex-p vertex)
   (implies
    (and
     (member-equal vertex visited)
     (not
      (member-equal vertex current))
     (not
      (member-equal vertex next)))
    (bfsq-successors-visited-p
     visited vertex))))

(defun-sk bfsq-all-closure-p
    (visited current next)
  (forall (vertex)
    (implies
     (bfsq-vertex-p vertex)
     (bfsq-closure-p
      visited current next vertex))))

(defun-sk bfsq-all-closure-except-p
    (visited current next excluded)
  (forall (vertex)
    (implies
     (bfsq-vertex-p vertex)
     (implies
      (not (equal vertex excluded))
      (bfsq-closure-p
       visited current next vertex)))))

;; When the current frontier becomes empty, the source rotates NEXT into
;; CURRENT, replaces NEXT by an arbitrary empty set value, and increments the
;; integer distance.

(defun-sk bfsq-empty-frontier-rotation-p
    (source target visited next depth)
  (forall (empty-set)
    (implies
     (bfsq-set-p empty-set)
     (implies
      (and
       (bfsq-fset-equal-p
        (bfsq-to-fset empty-set)
        nil)
       (equal
        (len (bfsq-to-fset empty-set))
        0))
      (and
       (bfsq-invariant-p
        source target
        visited next
        (bfsq-to-fset empty-set)
        (+ depth 1))
       (implies
        (equal next nil)
        (equal
         (bfsq-to-fset empty-set)
         nil))
       (bfsq-all-closure-p
        visited next
        (bfsq-to-fset empty-set))
       (<= 0 (+ depth 1)))))))

(defun bfsq-after-fill-branch-p
    (source target visited current next depth)
  (if (equal current nil)
      (bfsq-empty-frontier-rotation-p
       source target visited next depth)
    (and
     (bfsq-invariant-p
      source target visited current next depth)
     (implies
      (equal current nil)
      (equal next nil))
     (bfsq-all-closure-p
      visited current next)
     (<= 0 depth))))

(defun-sk bfsq-all-after-fill-p
    (source target current depth selected)
  (forall (next-set visited-set)
    (implies
     (and
      (bfsq-set-p next-set)
      (bfsq-set-p visited-set))
     (let ((next
            (bfsq-to-fset next-set))
           (visited
            (bfsq-to-fset visited-set)))
       (implies
        (and
         (bfsq-invariant-p
          source target
          visited current next depth)
         (bfsq-fset-subset-p
          (bfsq-successors selected)
          visited)
         (bfsq-all-closure-p
          visited current next))
        (bfsq-after-fill-branch-p
         source target
         visited current next depth))))))

;; This is the branch after choose-and-remove selects one current-frontier
;; vertex. The local equality postcondition retains its original implication
;; scope even though the global equality interface states the same law.

(defun bfsq-selected-vertex-body-p
    (source target visited current next depth selected)
  (if (bfsq-vertex-eq selected target)
      (bfsq-shortest-path-p
       source target depth)
    (and
     (bfsq-invariant-p
      source target
      visited current next depth)
     (bfsq-shortest-path-p
      source selected depth)
     (bfsq-all-closure-except-p
      visited current next selected)
     (bfsq-all-after-fill-p
      source target current depth selected))))

(defun-sk bfsq-all-current-removals-p
    (source target visited current next depth current-set)
  (forall (remaining-set)
    (implies
     (bfsq-set-p remaining-set)
     (let ((selected
            (bfsq-choose current-set))
           (remaining
            (bfsq-to-fset remaining-set)))
       (implies
        (and
         (member-equal selected current)
         (bfsq-fset-equal-p
          remaining
          (bfsq-fset-remove
           selected current)))
        (implies
         (iff
          (bfsq-vertex-eq selected target)
          (equal selected target))
         (bfsq-selected-vertex-body-p
          source target visited remaining
          next depth selected)))))))

(defun-sk bfsq-no-path-to-target-p
    (source target)
  (forall (length)
    (implies
     (integerp length)
     (not
      (bfsq-path-p
       source target length)))))

(defun bfsq-loop-branch-p
    (source target visited current next depth current-set)
  (if (not (equal current nil))
      (and
       (not (equal current nil))
       (bfsq-all-current-removals-p
        source target
        visited current next depth current-set))
    (bfsq-no-path-to-target-p
     source target)))

(defun-sk bfsq-all-loop-steps-p
    (source target)
  (forall (depth next-set current-set visited-set)
    (implies
     (and
      (integerp depth)
      (bfsq-set-p next-set)
      (bfsq-set-p current-set)
      (bfsq-set-p visited-set))
     (let ((next
            (bfsq-to-fset next-set))
           (current
            (bfsq-to-fset current-set))
           (visited
            (bfsq-to-fset visited-set)))
       (implies
        (and
         (bfsq-invariant-p
          source target
          visited current next depth)
         (implies
          (equal current nil)
          (equal next nil))
         (bfsq-all-closure-p
          visited current next)
         (<= 0 depth))
        (bfsq-loop-branch-p
         source target
         visited current next depth current-set))))))

;; The initial set-operation postconditions are retained as the ten explicit
;; hypotheses of the generated verification condition.

(defun bfsq-initial-facts-p
    (visited empty-current empty-next
             visited-after source current)
  (and
   (bfsq-fset-equal-p
    (bfsq-to-fset visited)
    nil)
   (equal
    (len (bfsq-to-fset visited))
    0)
   (bfsq-fset-equal-p
    (bfsq-to-fset empty-current)
    nil)
   (equal
    (len (bfsq-to-fset empty-current))
    0)
   (bfsq-fset-equal-p
    (bfsq-to-fset empty-next)
    nil)
   (equal
    (len (bfsq-to-fset empty-next))
    0)
   (bfsq-fset-equal-p
    (bfsq-to-fset visited-after)
    (bfsq-fset-insert
     source
     (bfsq-to-fset visited)))
   (if
       (member-equal
        source
        (bfsq-to-fset visited))
       (equal
        (len (bfsq-to-fset visited-after))
        (len (bfsq-to-fset visited)))
     (equal
      (len (bfsq-to-fset visited-after))
      (+ (len (bfsq-to-fset visited)) 1)))
   (bfsq-fset-equal-p
    (bfsq-to-fset current)
    (bfsq-fset-insert
     source
     (bfsq-to-fset empty-current)))
   (if
       (member-equal
        source
        (bfsq-to-fset empty-current))
       (equal
        (len (bfsq-to-fset current))
        (len (bfsq-to-fset empty-current)))
     (equal
      (len (bfsq-to-fset current))
      (+ (len (bfsq-to-fset empty-current)) 1)))))

(defun bfsq-main-conclusion-p
    (visited-after source current target empty-next)
  (let ((visited
         (bfsq-to-fset visited-after))
        (frontier
         (bfsq-to-fset current))
        (next
         (bfsq-to-fset empty-next)))
    (and
     (bfsq-invariant-p
      source target visited frontier next 0)
     (implies
      (equal frontier nil)
      (equal next nil))
     (bfsq-all-closure-p
      visited frontier next)
     (<= 0 0)
     (bfsq-all-loop-steps-p
      source target))))

(defun-sk
  ntp4vc-pearl-vstte12-bfs-bfs-bfsqtvc-statement
  ()
  (forall
    (visited empty-current empty-next visited-after
             source current target)
    (implies
     (and
      (bfsq-set-p visited)
      (bfsq-set-p empty-current)
      (bfsq-set-p empty-next)
      (bfsq-set-p visited-after)
      (bfsq-vertex-p source)
      (bfsq-set-p current)
      (bfsq-vertex-p target))
     (implies
      (and
       (bfsq-background-p)
       (bfsq-initial-facts-p
        visited empty-current empty-next
        visited-after source current))
      (bfsq-main-conclusion-p
       visited-after source current
       target empty-next)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
