;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/vstte12_bfs_BFS_fill_nextqtvc: the breadth-first-search fill-next
;; verification condition for successor processing, frontier invariants,
;; visited-set updates, closure, and loop termination. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces for the arbitrary inhabited vertex and mutable-set
;; carriers, finite successor sets, set conversion, and finite-set choice.

(defstub bfs-fill-vertex-p (x) t)
(defstub bfs-fill-set-p (x) t)
(defstub bfs-fill-default-vertex () t)
(defstub bfs-fill-default-set () t)
(defstub bfs-fill-to-fset (set) t)
(defstub bfs-fill-choose (set) t)
(defstub bfs-fill-successors (vertex) t)

;; Duplicate-free proper lists represent finite sets of vertices.  Equality,
;; subset, insertion, removal, and difference are extensional in list order.

(defun bfs-fill-vertex-fset-p (set)
  (if (consp set)
      (and
       (bfs-fill-vertex-p (car set))
       (not (member-equal (car set) (cdr set)))
       (bfs-fill-vertex-fset-p (cdr set)))
    (equal set nil)))

(defun bfs-fill-fset-subset-p (left right)
  (if (consp left)
      (and
       (member-equal (car left) right)
       (bfs-fill-fset-subset-p (cdr left) right))
    (equal left nil)))

(defun bfs-fill-fset-equal-p (left right)
  (and
   (bfs-fill-fset-subset-p left right)
   (bfs-fill-fset-subset-p right left)))

(defun bfs-fill-fset-insert (vertex set)
  (if (member-equal vertex set)
      set
    (cons vertex set)))

(defun bfs-fill-fset-remove (vertex set)
  (if (consp set)
      (if (equal vertex (car set))
          (cdr set)
        (cons
         (car set)
         (bfs-fill-fset-remove vertex (cdr set))))
    nil))

(defun bfs-fill-fset-difference (left right)
  (if (consp left)
      (if (member-equal (car left) right)
          (bfs-fill-fset-difference (cdr left) right)
        (cons
         (car left)
         (bfs-fill-fset-difference (cdr left) right)))
    nil))

;; A nonempty finite vertex sequence is constructor evidence for the source
;; inductive path relation.  A singleton is path_empty, and each additional
;; vertex is one application of path_succ.

(defun bfs-fill-vertex-list-p (vertices)
  (if (consp vertices)
      (and
       (bfs-fill-vertex-p (car vertices))
       (bfs-fill-vertex-list-p (cdr vertices)))
    (equal vertices nil)))

(defun bfs-fill-path-edges-p (vertices)
  (if (and
       (consp vertices)
       (consp (cdr vertices)))
      (and
       (member-equal
        (cadr vertices)
        (bfs-fill-successors (car vertices)))
       (bfs-fill-path-edges-p (cdr vertices)))
    (and
     (consp vertices)
     (equal (cdr vertices) nil))))

(defun bfs-fill-path-witness-p
    (vertices source target length)
  (and
   (integerp length)
   (<= 0 length)
   (bfs-fill-vertex-list-p vertices)
   (consp vertices)
   (equal (len vertices) (+ length 1))
   (equal (car vertices) source)
   (equal (car (last vertices)) target)
   (bfs-fill-path-edges-p vertices)))

(defun-sk bfs-fill-path-p (source target length)
  (exists (vertices)
    (and
     (bfs-fill-vertex-p source)
     (bfs-fill-vertex-p target)
     (bfs-fill-path-witness-p
      vertices source target length))))

(defun-sk bfs-fill-no-shorter-path-p
    (source target length)
  (forall (other-length)
    (implies
     (integerp other-length)
     (implies
      (< other-length length)
      (not
       (bfs-fill-path-p
        source target other-length))))))

(defun bfs-fill-shortest-path-p
    (source target length)
  (and
   (bfs-fill-path-p source target length)
   (bfs-fill-no-shorter-path-p
    source target length)))

;; Source-context laws for the abstract carriers and total finite-set
;; interfaces.  The choice specification is asserted only for nonempty sets,
;; exactly as in the source.

(defun-sk bfs-fill-vertex-inhabited-p ()
  (exists (vertex)
    (bfs-fill-vertex-p vertex)))

(defun-sk bfs-fill-set-inhabited-p ()
  (exists (set)
    (bfs-fill-set-p set)))

(defun-sk bfs-fill-successor-interface-p ()
  (forall (vertex)
    (implies
     (bfs-fill-vertex-p vertex)
     (bfs-fill-vertex-fset-p
      (bfs-fill-successors vertex)))))

(defun-sk bfs-fill-set-interface-p ()
  (forall (set)
    (implies
     (bfs-fill-set-p set)
     (and
      (bfs-fill-vertex-fset-p
       (bfs-fill-to-fset set))
      (bfs-fill-vertex-p
       (bfs-fill-choose set))
      (implies
       (not
        (equal
         (bfs-fill-to-fset set)
         nil))
       (member-equal
        (bfs-fill-choose set)
        (bfs-fill-to-fset set)))))))

(defun bfs-fill-background-p ()
  (and
   (bfs-fill-vertex-p
    (bfs-fill-default-vertex))
   (bfs-fill-set-p
    (bfs-fill-default-set))
   (bfs-fill-vertex-inhabited-p)
   (bfs-fill-set-inhabited-p)
   (bfs-fill-successor-interface-p)
   (bfs-fill-set-interface-p)))

;; Exact components of the breadth-first-search invariant.

(defun-sk bfs-fill-current-shortest-p
    (source current depth)
  (forall (vertex)
    (implies
     (bfs-fill-vertex-p vertex)
     (implies
      (member-equal vertex current)
      (bfs-fill-shortest-path-p
       source vertex depth)))))

(defun-sk bfs-fill-next-shortest-p
    (source next depth)
  (forall (vertex)
    (implies
     (bfs-fill-vertex-p vertex)
     (implies
      (member-equal vertex next)
      (bfs-fill-shortest-path-p
       source vertex (+ depth 1))))))

(defun-sk bfs-fill-short-paths-visited-p
    (source visited depth)
  (forall (vertex length)
    (implies
     (and
      (bfs-fill-vertex-p vertex)
      (integerp length))
     (implies
      (and
       (bfs-fill-path-p source vertex length)
       (<= length depth))
      (member-equal vertex visited)))))

(defun-sk bfs-fill-has-bounded-path-p
    (source vertex bound)
  (exists (length)
    (and
     (integerp length)
     (bfs-fill-path-p source vertex length)
     (<= length bound))))

(defun-sk bfs-fill-visited-path-bounds-p
    (source visited depth)
  (forall (vertex)
    (implies
     (bfs-fill-vertex-p vertex)
     (implies
      (member-equal vertex visited)
      (bfs-fill-has-bounded-path-p
       source vertex (+ depth 1))))))

(defun-sk bfs-fill-next-or-unvisited-p
    (source visited next depth)
  (forall (vertex)
    (implies
     (bfs-fill-vertex-p vertex)
     (implies
      (bfs-fill-shortest-path-p
       source vertex (+ depth 1))
      (or
       (member-equal vertex next)
       (not
        (member-equal vertex visited)))))))

(defun bfs-fill-invariant-p
    (source target visited current next depth)
  (and
   (bfs-fill-vertex-p source)
   (bfs-fill-vertex-p target)
   (bfs-fill-vertex-fset-p visited)
   (bfs-fill-vertex-fset-p current)
   (bfs-fill-vertex-fset-p next)
   (integerp depth)
   (bfs-fill-fset-subset-p current visited)
   (bfs-fill-current-shortest-p
    source current depth)
   (bfs-fill-fset-subset-p next visited)
   (bfs-fill-next-shortest-p
    source next depth)
   (bfs-fill-short-paths-visited-p
    source visited depth)
   (bfs-fill-visited-path-bounds-p
    source visited depth)
   (bfs-fill-next-or-unvisited-p
    source visited next depth)
   (implies
    (member-equal target visited)
    (or
     (member-equal target current)
     (member-equal target next)))))

;; The source closure predicate and its universally quantified variants.

(defun-sk bfs-fill-successors-visited-p
    (visited vertex)
  (forall (successor)
    (implies
     (bfs-fill-vertex-p successor)
     (implies
      (member-equal
       successor
       (bfs-fill-successors vertex))
      (member-equal successor visited)))))

(defun bfs-fill-closure-p
    (visited current next vertex)
  (and
   (bfs-fill-vertex-fset-p visited)
   (bfs-fill-vertex-fset-p current)
   (bfs-fill-vertex-fset-p next)
   (bfs-fill-vertex-p vertex)
   (implies
    (and
     (member-equal vertex visited)
     (not
      (member-equal vertex current))
     (not
      (member-equal vertex next)))
    (bfs-fill-successors-visited-p
     visited vertex))))

(defun-sk bfs-fill-all-closure-p
    (visited current next)
  (forall (vertex)
    (implies
     (bfs-fill-vertex-p vertex)
     (bfs-fill-closure-p
      visited current next vertex))))

(defun-sk bfs-fill-all-closure-except-p
    (visited current next excluded)
  (forall (vertex)
    (implies
     (bfs-fill-vertex-p vertex)
     (implies
      (not (equal vertex excluded))
      (bfs-fill-closure-p
       visited current next vertex)))))

;; Set-update postconditions and the loop invariant after one accumulator
;; element has been removed.

(defun bfs-fill-insert-cardinality-p
    (vertex old-set new-set)
  (if (member-equal vertex old-set)
      (equal (len new-set) (len old-set))
    (equal (len new-set) (+ (len old-set) 1))))

(defun bfs-fill-after-removal-state-p
    (source target current depth selected
            accumulator-before accumulator-after visited next)
  (and
   (<= 0 (len accumulator-before))
   (< (len accumulator-after)
      (len accumulator-before))
   (bfs-fill-invariant-p
    source target visited current next depth)
   (bfs-fill-fset-subset-p
    accumulator-after
    (bfs-fill-successors selected))
   (bfs-fill-fset-subset-p
    (bfs-fill-fset-difference
     (bfs-fill-successors selected)
     accumulator-after)
    visited)
   (bfs-fill-all-closure-except-p
    visited current next selected)))

(defun-sk bfs-fill-all-next-updates-p
    (source target current depth selected
            accumulator-before accumulator-after
            visited next-before chosen)
  (forall (next-after-set)
    (implies
     (bfs-fill-set-p next-after-set)
     (let ((next-after
            (bfs-fill-to-fset next-after-set)))
       (implies
        (and
         (bfs-fill-fset-equal-p
          next-after
          (bfs-fill-fset-insert
           chosen next-before))
         (bfs-fill-insert-cardinality-p
          chosen next-before next-after))
        (bfs-fill-after-removal-state-p
         source target current depth selected
         accumulator-before accumulator-after
         visited next-after))))))

(defun-sk bfs-fill-all-visited-updates-p
    (source target current depth selected
            accumulator-before accumulator-after
            visited-before next-before chosen)
  (forall (visited-after-set)
    (implies
     (bfs-fill-set-p visited-after-set)
     (let ((visited-after
            (bfs-fill-to-fset visited-after-set)))
       (implies
        (and
         (bfs-fill-fset-equal-p
          visited-after
          (bfs-fill-fset-insert
           chosen visited-before))
         (bfs-fill-insert-cardinality-p
          chosen visited-before visited-after))
        (bfs-fill-all-next-updates-p
         source target current depth selected
         accumulator-before accumulator-after
         visited-after next-before chosen))))))

(defun bfs-fill-after-removal-p
    (source target current depth selected
            accumulator-before accumulator-after
            visited next chosen)
  (if (not (member-equal chosen visited))
      (bfs-fill-all-visited-updates-p
       source target current depth selected
       accumulator-before accumulator-after
       visited next chosen)
    (bfs-fill-after-removal-state-p
     source target current depth selected
     accumulator-before accumulator-after
     visited next)))

(defun-sk bfs-fill-all-accumulator-removals-p
    (source target current depth selected
            accumulator-set visited next)
  (forall (accumulator-after-set)
    (implies
     (bfs-fill-set-p accumulator-after-set)
     (let ((chosen
            (bfs-fill-choose accumulator-set))
           (accumulator-before
            (bfs-fill-to-fset accumulator-set))
           (accumulator-after
            (bfs-fill-to-fset accumulator-after-set)))
       (implies
        (and
         (member-equal chosen accumulator-before)
         (bfs-fill-fset-equal-p
          accumulator-after
          (bfs-fill-fset-remove
           chosen accumulator-before)))
        (bfs-fill-after-removal-p
         source target current depth selected
         accumulator-before accumulator-after
         visited next chosen))))))

(defun bfs-fill-loop-branch-p
    (source target current depth selected
            accumulator-set visited next)
  (let ((accumulator
         (bfs-fill-to-fset accumulator-set)))
    (if (not (equal accumulator nil))
        (and
         (not (equal accumulator nil))
         (bfs-fill-all-accumulator-removals-p
          source target current depth selected
          accumulator-set visited next))
      (and
       (bfs-fill-invariant-p
        source target visited current next depth)
       (bfs-fill-fset-subset-p
        (bfs-fill-successors selected)
        visited)
       (bfs-fill-all-closure-p
        visited current next)))))

(defun bfs-fill-loop-invariant-p
    (source target current depth selected
            accumulator visited next)
  (and
   (bfs-fill-invariant-p
    source target visited current next depth)
   (bfs-fill-fset-subset-p
    accumulator
    (bfs-fill-successors selected))
   (bfs-fill-fset-subset-p
    (bfs-fill-fset-difference
     (bfs-fill-successors selected)
     accumulator)
    visited)
   (bfs-fill-all-closure-except-p
    visited current next selected)))

(defun-sk bfs-fill-all-loop-steps-p
    (source target current depth selected)
  (forall (accumulator-set next-set visited-set)
    (implies
     (and
      (bfs-fill-set-p accumulator-set)
      (bfs-fill-set-p next-set)
      (bfs-fill-set-p visited-set))
     (let ((accumulator
            (bfs-fill-to-fset accumulator-set))
           (next
            (bfs-fill-to-fset next-set))
           (visited
            (bfs-fill-to-fset visited-set)))
       (implies
        (bfs-fill-loop-invariant-p
         source target current depth selected
         accumulator visited next)
        (bfs-fill-loop-branch-p
         source target current depth selected
         accumulator-set visited next))))))

;; The top-level assumptions are the four generated pre-loop facts.  The
;; conclusion reproduces the initial loop invariant and every quantified
;; verification condition for the loop body.

(defun bfs-fill-initial-facts-p
    (source target visited current next
            depth selected accumulator)
  (and
   (bfs-fill-invariant-p
    source target visited current next depth)
   (bfs-fill-shortest-path-p
    source selected depth)
   (bfs-fill-all-closure-except-p
    visited current next selected)
   (bfs-fill-fset-equal-p
    accumulator
    (bfs-fill-successors selected))))

(defun bfs-fill-main-conclusion-p
    (source target visited current next
            depth selected accumulator)
  (and
   (bfs-fill-invariant-p
    source target visited current next depth)
   (bfs-fill-fset-subset-p
    accumulator
    (bfs-fill-successors selected))
   (bfs-fill-fset-subset-p
    (bfs-fill-fset-difference
     (bfs-fill-successors selected)
     accumulator)
    visited)
   (bfs-fill-all-closure-except-p
    visited current next selected)
   (bfs-fill-all-loop-steps-p
    source target current depth selected)))

(defun-sk
  ntp4vc-pearl-vstte12-bfs-bfs-fill-nextqtvc-statement
  ()
  (forall
    (source target visited-set current-set next-set
            depth selected accumulator-set)
    (implies
     (and
      (bfs-fill-vertex-p source)
      (bfs-fill-vertex-p target)
      (bfs-fill-set-p visited-set)
      (bfs-fill-set-p current-set)
      (bfs-fill-set-p next-set)
      (integerp depth)
      (bfs-fill-vertex-p selected)
      (bfs-fill-set-p accumulator-set))
     (let ((visited
            (bfs-fill-to-fset visited-set))
           (current
            (bfs-fill-to-fset current-set))
           (next
            (bfs-fill-to-fset next-set))
           (accumulator
            (bfs-fill-to-fset accumulator-set)))
       (implies
        (and
         (bfs-fill-background-p)
         (bfs-fill-initial-facts-p
          source target visited current next
          depth selected accumulator))
        (bfs-fill-main-conclusion-p
         source target visited current next
         depth selected accumulator))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
