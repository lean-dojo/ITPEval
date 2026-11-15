;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/dijkstra_DijkstraShortestPath_shortest_path_codeqtvc: the Dijkstra
;; shortest-path verification condition for initialization, loop invariants,
;; edge relaxation, termination measures, and final path optimality.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces retain the arbitrary source vertex, set, and
;; integer-map carriers. Their typing and source specification laws are
;; explicit hypotheses of the final statement predicate.

(defstub dsp-vertex-p (x) t)
(defstub dsp-set-p (x) t)
(defstub dsp-map-p (x) t)

(defstub dsp-to-fset (set) t)
(defstub dsp-choose (set) t)
(defstub dsp-map-get (map vertex) t)
(defstub dsp-map-update (map vertex value) t)

(defstub dsp-vertices () t)
(defstub dsp-successors (vertex) t)
(defstub dsp-weight (left right) t)

;; Duplicate-free proper lists represent finite sets of source vertices.
;; All operations below are extensional, so list order is irrelevant.

(defun dsp-vertex-fset-p (set)
  (if (consp set)
      (and
       (dsp-vertex-p (car set))
       (not (member-equal (car set) (cdr set)))
       (dsp-vertex-fset-p (cdr set)))
    (equal set nil)))

(defun dsp-fset-subset-p (left right)
  (if (consp left)
      (and
       (member-equal (car left) right)
       (dsp-fset-subset-p (cdr left) right))
    (equal left nil)))

(defun dsp-fset-equal-p (left right)
  (and
   (dsp-fset-subset-p left right)
   (dsp-fset-subset-p right left)))

(defun dsp-fset-insert (vertex set)
  (if (member-equal vertex set)
      set
    (cons vertex set)))

(defun dsp-fset-remove (vertex set)
  (if (consp set)
      (if (equal vertex (car set))
          (cdr set)
        (cons
         (car set)
         (dsp-fset-remove vertex (cdr set))))
    nil))

;; A source inductive path is represented by a nonempty finite vertex
;; sequence. Consecutive vertices follow the successor relation, and the sum
;; of their edge weights is the source path's integer distance. This is
;; bidirectionally equivalent to Path_nil and repeated Path_cons.

(defun dsp-vertex-list-p (vertices)
  (if (consp vertices)
      (and
       (dsp-vertex-p (car vertices))
       (dsp-vertex-list-p (cdr vertices)))
    (equal vertices nil)))

(defun dsp-path-edges-p (vertices)
  (if (and (consp vertices)
           (consp (cdr vertices)))
      (and
       (member-equal
        (cadr vertices)
        (dsp-successors (car vertices)))
       (dsp-path-edges-p (cdr vertices)))
    (and
     (consp vertices)
     (equal (cdr vertices) nil))))

(defun dsp-path-weight (vertices)
  (if (and (consp vertices)
           (consp (cdr vertices)))
      (+
       (dsp-weight (car vertices) (cadr vertices))
       (dsp-path-weight (cdr vertices)))
    0))

(defun dsp-path-witness-p (vertices source destination distance)
  (and
   (dsp-vertex-list-p vertices)
   (consp vertices)
   (equal (car vertices) source)
   (equal (car (last vertices)) destination)
   (dsp-path-edges-p vertices)
   (equal (dsp-path-weight vertices) distance)))

(defun-sk dsp-path-p (source destination distance)
  (exists (vertices)
    (and
     (dsp-vertex-p source)
     (dsp-vertex-p destination)
     (integerp distance)
     (dsp-path-witness-p
      vertices source destination distance))))

;; Explicit source-context laws.

(defun-sk dsp-vertex-inhabited-p ()
  (exists (vertex)
    (dsp-vertex-p vertex)))

(defun-sk dsp-set-inhabited-p ()
  (exists (set)
    (dsp-set-p set)))

(defun-sk dsp-map-inhabited-p ()
  (exists (map)
    (dsp-map-p map)))

(defun-sk dsp-set-interface-laws-p ()
  (forall (set)
    (implies
     (dsp-set-p set)
     (and
      (dsp-vertex-fset-p
       (dsp-to-fset set))
      (dsp-vertex-p
       (dsp-choose set))
      (implies
       (not (equal (dsp-to-fset set) nil))
       (member-equal
        (dsp-choose set)
        (dsp-to-fset set)))))))

(defun-sk dsp-map-get-type-law-p ()
  (forall (map vertex)
    (implies
     (and
      (dsp-map-p map)
      (dsp-vertex-p vertex))
     (integerp
      (dsp-map-get map vertex)))))

(defun-sk dsp-map-update-laws-p ()
  (forall (map key value vertex)
    (implies
     (and
      (dsp-map-p map)
      (dsp-vertex-p key)
      (integerp value)
      (dsp-vertex-p vertex))
     (and
      (dsp-map-p
       (dsp-map-update map key value))
      (equal
       (dsp-map-get
        (dsp-map-update map key value)
        vertex)
       (if (equal vertex key)
           value
         (dsp-map-get map vertex)))))))

(defun-sk dsp-successor-laws-p ()
  (forall (vertex)
    (implies
     (dsp-vertex-p vertex)
     (and
      (dsp-vertex-fset-p
       (dsp-successors vertex))
      (dsp-fset-subset-p
       (dsp-successors vertex)
       (dsp-vertices))))))

(defun-sk dsp-weight-laws-p ()
  (forall (left right)
    (implies
     (and
      (dsp-vertex-p left)
      (dsp-vertex-p right))
     (and
      (integerp
       (dsp-weight left right))
      (<= 0
          (dsp-weight left right))))))

(defun dsp-background-p ()
  (and
   (dsp-vertex-inhabited-p)
   (dsp-set-inhabited-p)
   (dsp-map-inhabited-p)
   (dsp-vertex-fset-p
    (dsp-vertices))
   (dsp-set-interface-laws-p)
   (dsp-map-get-type-law-p)
   (dsp-map-update-laws-p)
   (dsp-successor-laws-p)
   (dsp-weight-laws-p)))

;; Source definitions: minimum queue element, shortest path, and invariants.

(defun-sk dsp-minimum-lower-bound-p (minimum queue map)
  (forall (vertex)
    (implies
     (dsp-vertex-p vertex)
     (implies
      (member-equal
       vertex
       (dsp-to-fset queue))
      (<=
       (dsp-map-get map minimum)
       (dsp-map-get map vertex))))))

(defun dsp-minimum-p (minimum queue map)
  (and
   (dsp-vertex-p minimum)
   (dsp-set-p queue)
   (dsp-map-p map)
   (member-equal
    minimum
    (dsp-to-fset queue))
   (dsp-minimum-lower-bound-p
    minimum queue map)))

(defun-sk dsp-shortest-lower-bound-p
    (source destination distance)
  (forall (other-distance)
    (implies
     (integerp other-distance)
     (implies
      (dsp-path-p
       source destination other-distance)
      (<= distance other-distance)))))

(defun dsp-shortest-path-p
    (source destination distance)
  (and
   (dsp-path-p source destination distance)
   (dsp-shortest-lower-bound-p
    source destination distance)))

(defun dsp-inv-src-p (source visited queue)
  (or
   (member-equal
    source
    (dsp-to-fset visited))
   (member-equal
    source
    (dsp-to-fset queue))))

(defun-sk dsp-inv-vertex-conditions-p
    (source visited queue map)
  (forall (vertex)
    (implies
     (dsp-vertex-p vertex)
     (and
      (implies
       (member-equal
        vertex
        (dsp-to-fset queue))
       (not
        (member-equal
         vertex
         (dsp-to-fset visited))))
      (implies
       (member-equal
        vertex
        (dsp-to-fset visited))
       (dsp-shortest-path-p
        source vertex
        (dsp-map-get map vertex)))
      (implies
       (member-equal
        vertex
        (dsp-to-fset queue))
       (dsp-path-p
        source vertex
        (dsp-map-get map vertex)))))))

(defun dsp-inv-p (source visited queue map)
  (and
   (dsp-vertex-p source)
   (dsp-set-p visited)
   (dsp-set-p queue)
   (dsp-map-p map)
   (dsp-inv-src-p source visited queue)
   (equal (dsp-map-get map source) 0)
   (dsp-fset-subset-p
    (dsp-to-fset visited)
    (dsp-vertices))
   (dsp-fset-subset-p
    (dsp-to-fset queue)
    (dsp-vertices))
   (dsp-inv-vertex-conditions-p
    source visited queue map)))

(defun-sk dsp-inv-succ-conditions-p
    (visited queue map)
  (forall (left right)
    (implies
     (and
      (dsp-vertex-p left)
      (dsp-vertex-p right))
     (implies
      (and
       (member-equal
        left
        (dsp-to-fset visited))
       (member-equal
        right
        (dsp-successors left)))
      (and
       (or
        (member-equal
         right
         (dsp-to-fset visited))
        (member-equal
         right
         (dsp-to-fset queue)))
       (<=
        (dsp-map-get map right)
        (+
         (dsp-map-get map left)
         (dsp-weight left right))))))))

(defun dsp-inv-succ-p (source visited queue map)
  (and
   (dsp-vertex-p source)
   (dsp-set-p visited)
   (dsp-set-p queue)
   (dsp-map-p map)
   (dsp-inv-succ-conditions-p
    visited queue map)))

(defun-sk dsp-inv-succ2-conditions-p
    (visited queue map selected remaining-successors)
  (forall (left right)
    (implies
     (and
      (dsp-vertex-p left)
      (dsp-vertex-p right))
     (implies
      (and
       (member-equal
        left
        (dsp-to-fset visited))
       (member-equal
        right
        (dsp-successors left))
       (or
        (not (equal left selected))
        (and
         (equal left selected)
         (not
          (member-equal
           right
           (dsp-to-fset
            remaining-successors))))))
      (and
       (or
        (member-equal
         right
         (dsp-to-fset visited))
        (member-equal
         right
         (dsp-to-fset queue)))
       (<=
        (dsp-map-get map right)
        (+
         (dsp-map-get map left)
         (dsp-weight left right))))))))

(defun dsp-inv-succ2-p
    (source visited queue map selected remaining-successors)
  (and
   (dsp-vertex-p source)
   (dsp-set-p visited)
   (dsp-set-p queue)
   (dsp-map-p map)
   (dsp-vertex-p selected)
   (dsp-set-p remaining-successors)
   (dsp-inv-succ2-conditions-p
    visited queue map selected remaining-successors)))

;; Vertices whose path distance is below a queue minimum have already been
;; visited. This is the repeated quantified invariant in the VC.

(defun-sk dsp-below-minimum-visited-p
    (source visited queue map)
  (forall (minimum vertex distance)
    (implies
     (and
      (dsp-vertex-p minimum)
      (dsp-vertex-p vertex)
      (integerp distance))
     (implies
      (and
       (dsp-minimum-p minimum queue map)
       (dsp-path-p source vertex distance)
       (< distance
          (dsp-map-get map minimum)))
      (member-equal
       vertex
       (dsp-to-fset visited))))))

;; Final branch when the queue is empty.

(defun-sk dsp-final-visited-shortest-p
    (source visited map)
  (forall (vertex)
    (implies
     (dsp-vertex-p vertex)
     (implies
      (member-equal
       vertex
       (dsp-to-fset visited))
      (dsp-shortest-path-p
       source vertex
       (dsp-map-get map vertex))))))

(defun-sk dsp-final-unvisited-unreachable-p
    (source visited)
  (forall (vertex distance)
    (implies
     (and
      (dsp-vertex-p vertex)
      (integerp distance))
     (implies
      (not
       (member-equal
        vertex
        (dsp-to-fset visited)))
      (not
       (dsp-path-p
        source vertex distance))))))

(defun dsp-final-correct-p (source visited map)
  (and
   (dsp-final-visited-shortest-p
    source visited map)
   (dsp-final-unvisited-unreachable-p
    source visited)))

;; One successor-relaxation step. The four alternatives are retained exactly:
;; already visited, no improvement, improvement of an existing queue entry,
;; or insertion of a newly discovered vertex.

(defun dsp-relaxation-premise-p
    (vertex selected visited queue-before map-before queue-after map-after)
  (or
   (and
    (member-equal
     vertex
     (dsp-to-fset visited))
    (equal queue-after queue-before)
    (equal map-after map-before))
   (and
    (member-equal
     vertex
     (dsp-to-fset queue-after))
    (<=
     (dsp-map-get map-after vertex)
     (+
      (dsp-map-get map-after selected)
      (dsp-weight selected vertex)))
    (equal queue-after queue-before)
    (equal map-after map-before))
   (and
    (member-equal
     vertex
     (dsp-to-fset queue-after))
    (<
     (+
      (dsp-map-get map-before selected)
      (dsp-weight selected vertex))
     (dsp-map-get map-before vertex))
    (equal queue-after queue-before)
    (equal
     map-after
     (dsp-map-update
      map-before vertex
      (+
       (dsp-map-get map-before selected)
       (dsp-weight selected vertex)))))
   (and
    (not
     (member-equal
      vertex
      (dsp-to-fset visited)))
    (not
     (member-equal
      vertex
      (dsp-to-fset queue-before)))
    (dsp-fset-equal-p
     (dsp-to-fset queue-after)
     (dsp-fset-insert
      vertex
      (dsp-to-fset queue-before)))
    (equal
     map-after
     (dsp-map-update
      map-before vertex
      (+
       (dsp-map-get map-before selected)
       (dsp-weight selected vertex)))))))

(defun dsp-successor-step-conclusion-p
    (source visited selected successors-before successors-after
     queue-after map-after)
  (and
   (<= 0
       (len (dsp-to-fset successors-before)))
   (<
    (len (dsp-to-fset successors-after))
    (len (dsp-to-fset successors-before)))
   (dsp-fset-subset-p
    (dsp-to-fset successors-after)
    (dsp-successors selected))
   (dsp-inv-p
    source visited queue-after map-after)
   (dsp-inv-succ2-p
    source visited queue-after map-after
    selected successors-after)))

(defun-sk dsp-relaxation-continuation-p
    (source visited selected successors-before successors-after
     queue-before map-before)
  (forall (queue-after map-after)
    (implies
     (and
      (dsp-set-p queue-after)
      (dsp-map-p map-after))
     (implies
      (dsp-relaxation-premise-p
       (dsp-choose successors-before)
       selected visited queue-before map-before
       queue-after map-after)
      (dsp-successor-step-conclusion-p
       source visited selected
       successors-before successors-after
       queue-after map-after)))))

(defun-sk dsp-successor-removal-continuation-p
    (source visited selected successors-before queue-before map-before)
  (forall (successors-after)
    (implies
     (dsp-set-p successors-after)
     (implies
      (and
       (member-equal
        (dsp-choose successors-before)
        (dsp-to-fset successors-before))
       (dsp-fset-equal-p
        (dsp-to-fset successors-after)
        (dsp-fset-remove
         (dsp-choose successors-before)
         (dsp-to-fset successors-before))))
      (dsp-relaxation-continuation-p
       source visited selected
       successors-before successors-after
       queue-before map-before)))))

;; Completion of the inner successor loop restores inv_succ and strictly
;; decreases the outer finite-vertex measure.

(defun dsp-successor-loop-finished-p
    (source visited-before visited-after queue map)
  (and
   (<= 0
       (-
        (len (dsp-vertices))
        (len (dsp-to-fset visited-before))))
   (<
    (-
     (len (dsp-vertices))
     (len (dsp-to-fset visited-after)))
    (-
     (len (dsp-vertices))
     (len (dsp-to-fset visited-before))))
   (dsp-inv-p
    source visited-after queue map)
   (dsp-inv-succ-p
    source visited-after queue map)
   (dsp-below-minimum-visited-p
    source visited-after queue map)))

(defun dsp-successor-loop-branch-p
    (source visited-before visited-after selected
     successors-before queue map)
  (if (not
       (equal
        (dsp-to-fset successors-before)
        nil))
      (and
       (not
        (equal
         (dsp-to-fset successors-before)
         nil))
       (dsp-successor-removal-continuation-p
        source visited-after selected
        successors-before queue map))
    (dsp-successor-loop-finished-p
     source visited-before visited-after
     queue map)))

(defun-sk dsp-successor-loop-continuation-p
    (source visited-before visited-after selected)
  (forall (successors-before queue map)
    (implies
     (and
      (dsp-set-p successors-before)
      (dsp-set-p queue)
      (dsp-map-p map))
     (implies
      (and
       (dsp-fset-subset-p
        (dsp-to-fset successors-before)
        (dsp-successors selected))
       (dsp-inv-p
        source visited-after queue map)
       (dsp-inv-succ2-p
        source visited-after queue map
        selected successors-before))
      (dsp-successor-loop-branch-p
       source visited-before visited-after selected
       successors-before queue map)))))

;; The first conjuncts after choosing the successor set use the current map
;; and queue, so this non-quantified wrapper keeps those values explicit.

(defun dsp-successor-set-body-p
    (source visited-before visited-after queue map selected successors)
  (and
   (dsp-fset-subset-p
    (dsp-to-fset successors)
    (dsp-successors selected))
   (dsp-inv-p
    source visited-after queue map)
   (dsp-inv-succ2-p
    source visited-after queue map
    selected successors)
   (dsp-successor-loop-continuation-p
    source visited-before visited-after selected)))

(defun-sk dsp-successor-set-continuation-p
    (source visited-before visited-after queue map selected)
  (forall (successors)
    (implies
     (dsp-set-p successors)
     (implies
      (dsp-fset-equal-p
       (dsp-to-fset successors)
       (dsp-successors selected))
      (dsp-successor-set-body-p
       source visited-before visited-after
       queue map selected successors)))))

;; Removing the selected minimum and adding it to visited.

(defun dsp-visited-cardinality-condition-p
    (visited-before visited-after selected)
  (if
      (member-equal
       selected
       (dsp-to-fset visited-before))
      (equal
       (len (dsp-to-fset visited-after))
       (len (dsp-to-fset visited-before)))
    (equal
     (len (dsp-to-fset visited-after))
     (+
      (len (dsp-to-fset visited-before))
      1))))

(defun-sk dsp-visited-update-continuation-p
    (source visited-before queue map selected)
  (forall (visited-after)
    (implies
     (dsp-set-p visited-after)
     (implies
      (and
       (dsp-fset-equal-p
        (dsp-to-fset visited-after)
        (dsp-fset-insert
         selected
         (dsp-to-fset visited-before)))
       (dsp-visited-cardinality-condition-p
        visited-before visited-after selected))
      (dsp-successor-set-continuation-p
       source visited-before visited-after
       queue map selected)))))

(defun-sk dsp-queue-removal-continuation-p
    (source visited queue-before map)
  (forall (queue-after selected)
    (implies
     (and
      (dsp-set-p queue-after)
      (dsp-vertex-p selected))
     (implies
      (and
       (dsp-minimum-p
        selected queue-before map)
       (dsp-fset-equal-p
        (dsp-to-fset queue-after)
        (dsp-fset-remove
         selected
         (dsp-to-fset queue-before))))
      (dsp-visited-update-continuation-p
       source visited queue-after map selected)))))

(defun dsp-outer-loop-branch-p
    (source visited queue map)
  (if (not
       (equal
        (dsp-to-fset queue)
        nil))
      (and
       (not
        (equal
         (dsp-to-fset queue)
         nil))
       (dsp-queue-removal-continuation-p
        source visited queue map))
    (dsp-final-correct-p
     source visited map)))

(defun-sk dsp-outer-loop-continuation-p (source)
  (forall (queue map visited)
    (implies
     (and
      (dsp-set-p queue)
      (dsp-map-p map)
      (dsp-set-p visited))
     (implies
      (and
       (dsp-inv-p
        source visited queue map)
       (dsp-inv-succ-p
        source visited queue map)
       (dsp-below-minimum-visited-p
        source visited queue map))
      (dsp-outer-loop-branch-p
       source visited queue map)))))

(defun dsp-main-conclusion-p
    (source visited queue map)
  (let ((initialized-map
         (dsp-map-update map source 0)))
    (and
     (dsp-inv-p
      source visited queue initialized-map)
     (dsp-inv-succ-p
      source visited queue initialized-map)
     (dsp-below-minimum-visited-p
      source visited queue initialized-map)
     (dsp-outer-loop-continuation-p
      source))))

(defun-sk
  ntp4vc-pearl-dijkstra-dijkstrashortestpath-shortest-path-codeqtvc-statement
  ()
  (forall (source destination visited queue map)
    (implies
     (and
      (dsp-background-p)
      (dsp-vertex-p source)
      (dsp-vertex-p destination)
      (dsp-set-p visited)
      (dsp-set-p queue)
      (dsp-map-p map)
      (member-equal
       source
       (dsp-vertices))
      (member-equal
       destination
       (dsp-vertices))
      (dsp-fset-equal-p
       (dsp-to-fset visited)
       nil)
      (dsp-fset-equal-p
       (dsp-to-fset queue)
       (list source)))
     (dsp-main-conclusion-p
      source visited queue map))))

(value-triple :itpeval-statement-checked)
:q
