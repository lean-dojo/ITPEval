;; Statement-only formalization of thousand-theorems corpus artifact Q1047749,
;; "Turán's theorem": a finite simple graph is r-Turán-maximal exactly when it
;; is isomorphic to the complete r-partite graph whose part sizes differ by at
;; most one, for positive r. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A duplicate-free list is an enumeration of the finite vertex type. An edge
;; is an unordered pair of distinct enumerated vertices. Thus valid edge lists
;; represent exactly the finite simple graphs in the source, independently of
;; the chosen carrier order or the orientation used to write each pair.

(defun q1047749-carrier-p (vertices)
  (and (true-listp vertices)
       (no-duplicatesp-equal vertices)))

(defun q1047749-edge-record-p (edge vertices)
  (and (true-listp edge)
       (equal (len edge) 2)
       (member-equal (nth 0 edge) vertices)
       (member-equal (nth 1 edge) vertices)
       (not (equal (nth 0 edge) (nth 1 edge)))))

(defun q1047749-same-undirected-edge-p (left right)
  (or (and (equal (nth 0 left) (nth 0 right))
           (equal (nth 1 left) (nth 1 right)))
      (and (equal (nth 0 left) (nth 1 right))
           (equal (nth 1 left) (nth 0 right)))))

(defun q1047749-edge-distinct-from-list-p (edge remaining)
  (if (consp remaining)
      (and (not (q1047749-same-undirected-edge-p
                 edge (car remaining)))
           (q1047749-edge-distinct-from-list-p
            edge (cdr remaining)))
    t))

(defun q1047749-edge-list-p (edges vertices)
  (if (consp edges)
      (and (q1047749-edge-record-p (car edges) vertices)
           (q1047749-edge-distinct-from-list-p
            (car edges) (cdr edges))
           (q1047749-edge-list-p (cdr edges) vertices))
    (equal edges nil)))

(defun q1047749-simple-graph-p (vertices edges)
  (and (q1047749-carrier-p vertices)
       (q1047749-edge-list-p edges vertices)))

(defun q1047749-adjacent-p (edges u v)
  (if (or (member-equal (list u v) edges)
          (member-equal (list v u) edges))
      t
    nil))

;; The recursive search below detects a clique of the requested cardinality.
;; Since VERTICES has no duplicates, selecting N vertices produces a genuine
;; N-element set, matching SimpleGraph.CliqueFree.

(defun q1047749-adjacent-to-all-p (vertex chosen edges)
  (if (consp chosen)
      (and (q1047749-adjacent-p
            edges vertex (car chosen))
           (q1047749-adjacent-to-all-p
            vertex (cdr chosen) edges))
    t))

(defun q1047749-has-clique-from-p
    (remaining edges needed chosen)
  (declare (xargs :measure (len remaining)))
  (cond
   ((zp needed) t)
   ((not (consp remaining)) nil)
   (t
    (or
     (and
      (q1047749-adjacent-to-all-p
       (car remaining) chosen edges)
      (q1047749-has-clique-from-p
       (cdr remaining)
       edges
       (- needed 1)
       (cons (car remaining) chosen)))
     (q1047749-has-clique-from-p
      (cdr remaining) edges needed chosen)))))

(defun q1047749-clique-free-p (vertices edges clique-size)
  (not (q1047749-has-clique-from-p
        vertices edges clique-size nil)))

;; Every finite simple graph on VERTICES is a subset of this list of all
;; unordered pairs. Exhausting all subsets therefore preserves the universal
;; quantifier over competing graphs in IsTuranMaximal.

(defun q1047749-pairs-with (vertex remaining)
  (if (consp remaining)
      (cons (list vertex (car remaining))
            (q1047749-pairs-with
             vertex (cdr remaining)))
    nil))

(defun q1047749-potential-edges (vertices)
  (if (consp vertices)
      (append
       (q1047749-pairs-with
        (car vertices) (cdr vertices))
       (q1047749-potential-edges (cdr vertices)))
    nil))

(defun q1047749-all-clique-free-subsets-bounded-p
    (remaining-potential selected vertices clique-size bound)
  (declare (xargs :measure (len remaining-potential)))
  (if (consp remaining-potential)
      (and
       (q1047749-all-clique-free-subsets-bounded-p
        (cdr remaining-potential)
        (cons (car remaining-potential) selected)
        vertices
        clique-size
        bound)
       (q1047749-all-clique-free-subsets-bounded-p
        (cdr remaining-potential)
        selected
        vertices
        clique-size
        bound))
    (or
     (not (q1047749-clique-free-p
           vertices selected clique-size))
     (<= (len selected) bound))))

(defun q1047749-is-turan-maximal-p (vertices edges r)
  (let ((clique-size (+ r 1)))
    (and
     (q1047749-clique-free-p
      vertices edges clique-size)
     (q1047749-all-clique-free-subsets-bounded-p
      (q1047749-potential-edges vertices)
      nil
      vertices
      clique-size
      (len edges)))))

;; INSERT-AT-SPLITS and PERMUTATIONS enumerate every bijection from the
;; canonical positions 0,...,|V|-1 to V. A labeling is an isomorphism to the
;; source Turán graph exactly when adjacency agrees at every vertex pair with
;; inequality of the position residues modulo r.

(defun q1047749-insert-at-splits (vertex prefix suffix)
  (declare (xargs :measure (len suffix)))
  (if (consp suffix)
      (cons
       (append prefix (cons vertex suffix))
       (q1047749-insert-at-splits
        vertex
        (append prefix (list (car suffix)))
        (cdr suffix)))
    (list (append prefix (list vertex)))))

(defun q1047749-insert-into-permutations
    (vertex permutations)
  (if (consp permutations)
      (append
       (q1047749-insert-at-splits
        vertex nil (car permutations))
       (q1047749-insert-into-permutations
        vertex (cdr permutations)))
    nil))

(defun q1047749-permutations (vertices)
  (if (consp vertices)
      (q1047749-insert-into-permutations
       (car vertices)
       (q1047749-permutations (cdr vertices)))
    (list nil)))

(defun q1047749-turan-row-p
    (vertex remaining edges r left-index right-index)
  (if (consp remaining)
      (and
       (equal
        (q1047749-adjacent-p
         edges vertex (car remaining))
        (not
         (equal
          (mod left-index r)
          (mod right-index r))))
       (q1047749-turan-row-p
        vertex
        (cdr remaining)
        edges
        r
        left-index
        (+ right-index 1)))
    t))

(defun q1047749-turan-labeling-p
    (labeling edges r index)
  (if (consp labeling)
      (and
       (q1047749-turan-row-p
        (car labeling)
        (cdr labeling)
        edges
        r
        index
        (+ index 1))
       (q1047749-turan-labeling-p
        (cdr labeling)
        edges
        r
        (+ index 1)))
    t))

(defun q1047749-some-turan-labeling-p
    (labelings edges r)
  (if (consp labelings)
      (or
       (q1047749-turan-labeling-p
        (car labelings) edges r 0)
       (q1047749-some-turan-labeling-p
        (cdr labelings) edges r))
    nil))

(defun q1047749-nonempty-iso-turan-graph-p
    (vertices edges r)
  (q1047749-some-turan-labeling-p
   (q1047749-permutations vertices)
   edges
   r))

(defun thousand-theorems-q1047749-turans-theorem-statement
    (vertices edges r)
  (implies
   (and
    (natp r)
    (< 0 r)
    (q1047749-simple-graph-p vertices edges))
   (equal
    (q1047749-is-turan-maximal-p
     vertices edges r)
    (q1047749-nonempty-iso-turan-graph-p
     vertices edges r))))

(value-triple :itpeval-statement-checked)
:q
