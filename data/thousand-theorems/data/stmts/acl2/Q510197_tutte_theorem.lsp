;; Statement-only formalization of thousand-theorems corpus artifact Q510197,
;; "Tutte theorem": a finite simple graph has a perfect matching if and only
;; if deleting any vertex subset leaves at most that subset's cardinality many
;; connected components of odd cardinality. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A duplicate-free true list enumerates the finite vertex type. Each edge is
;; an unordered pair of distinct enumerated vertices, and no undirected edge
;; occurs twice. These valid lists represent exactly finite simple graphs,
;; independently of carrier order and edge orientation.

(defun q510197-carrier-p (vertices)
  (and (true-listp vertices)
       (no-duplicatesp-equal vertices)))

(defun q510197-edge-record-p (edge vertices)
  (and (true-listp edge)
       (equal (len edge) 2)
       (member-equal (nth 0 edge) vertices)
       (member-equal (nth 1 edge) vertices)
       (not (equal (nth 0 edge) (nth 1 edge)))))

(defun q510197-same-undirected-edge-p (left right)
  (or (and (equal (nth 0 left) (nth 0 right))
           (equal (nth 1 left) (nth 1 right)))
      (and (equal (nth 0 left) (nth 1 right))
           (equal (nth 1 left) (nth 0 right)))))

(defun q510197-edge-distinct-from-list-p (edge remaining)
  (if (consp remaining)
      (and (not (q510197-same-undirected-edge-p
                 edge (car remaining)))
           (q510197-edge-distinct-from-list-p
            edge (cdr remaining)))
    t))

(defun q510197-edge-list-p (edges vertices)
  (if (consp edges)
      (and (q510197-edge-record-p (car edges) vertices)
           (q510197-edge-distinct-from-list-p
            (car edges) (cdr edges))
           (q510197-edge-list-p (cdr edges) vertices))
    (equal edges nil)))

(defun q510197-simple-graph-p (vertices edges)
  (and (q510197-carrier-p vertices)
       (q510197-edge-list-p edges vertices)))

(defun q510197-adjacent-p (edges u v)
  (if (or (member-equal (list u v) edges)
          (member-equal (list v u) edges))
      t
    nil))

;; A matching is an edge subset whose edges have pairwise disjoint endpoints.
;; Exhausting inclusion and exclusion of every graph edge keeps the perfect
;; matching witness existentially quantified inside the statement predicate.

(defun q510197-vertex-incident-p (vertex matching)
  (if (consp matching)
      (or (equal vertex (nth 0 (car matching)))
          (equal vertex (nth 1 (car matching)))
          (q510197-vertex-incident-p vertex (cdr matching)))
    nil))

(defun q510197-matching-p (matching)
  (if (consp matching)
      (and (not (q510197-vertex-incident-p
                 (nth 0 (car matching)) (cdr matching)))
           (not (q510197-vertex-incident-p
                 (nth 1 (car matching)) (cdr matching)))
           (q510197-matching-p (cdr matching)))
    (equal matching nil)))

(defun q510197-all-vertices-covered-p (vertices matching)
  (if (consp vertices)
      (and (q510197-vertex-incident-p
            (car vertices) matching)
           (q510197-all-vertices-covered-p
            (cdr vertices) matching))
    t))

(defun q510197-perfect-matching-p (vertices matching)
  (and (q510197-matching-p matching)
       (q510197-all-vertices-covered-p vertices matching)))

(defun q510197-has-perfect-matching-from-p
    (remaining-edges selected vertices)
  (declare (xargs :measure (len remaining-edges)))
  (if (consp remaining-edges)
      (or
       (q510197-has-perfect-matching-from-p
        (cdr remaining-edges)
        (cons (car remaining-edges) selected)
        vertices)
       (q510197-has-perfect-matching-from-p
        (cdr remaining-edges)
        selected
        vertices))
    (q510197-perfect-matching-p vertices selected)))

(defun q510197-has-perfect-matching-p (vertices edges)
  (q510197-has-perfect-matching-from-p edges nil vertices))

;; Repeated synchronous neighborhood expansion computes the connected
;; component of SEED in the subgraph induced by ALLOWED. A simple path in an
;; n-vertex graph has length below n, so n expansions give the exact component.

(defun q510197-adjacent-to-any-p (vertex reached edges)
  (if (consp reached)
      (or (q510197-adjacent-p edges vertex (car reached))
          (q510197-adjacent-to-any-p
           vertex (cdr reached) edges))
    nil))

(defun q510197-expand-reached (candidates reached edges)
  (if (consp candidates)
      (if (or (member-equal (car candidates) reached)
              (q510197-adjacent-to-any-p
               (car candidates) reached edges))
          (cons (car candidates)
                (q510197-expand-reached
                 (cdr candidates) reached edges))
        (q510197-expand-reached
         (cdr candidates) reached edges))
    nil))

(defun q510197-reach-closure (fuel allowed reached edges)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      reached
    (q510197-reach-closure
     (- fuel 1)
     allowed
     (q510197-expand-reached allowed reached edges)
     edges)))

(defun q510197-component-of (seed allowed edges)
  (q510197-reach-closure
   (len allowed) allowed (list seed) edges))

(defun q510197-remove-members (vertices removed)
  (if (consp vertices)
      (if (member-equal (car vertices) removed)
          (q510197-remove-members (cdr vertices) removed)
        (cons (car vertices)
              (q510197-remove-members
               (cdr vertices) removed)))
    nil))

(defun q510197-some-member-p (left right)
  (if (consp left)
      (or (member-equal (car left) right)
          (q510197-some-member-p (cdr left) right))
    nil))

;; Scanning the induced carrier in its enumeration order counts each connected
;; component only at its first vertex. Its closure cardinality then determines
;; whether that component is odd.

(defun q510197-odd-components-count-aux
    (remaining earlier allowed edges)
  (declare (xargs :measure (len remaining)))
  (if (consp remaining)
      (let* ((component
              (q510197-component-of
               (car remaining) allowed edges))
             (first-in-component
              (not (q510197-some-member-p component earlier)))
             (odd-component
              (and first-in-component
                   (equal (mod (len component) 2) 1))))
        (+ (if odd-component 1 0)
           (q510197-odd-components-count-aux
            (cdr remaining)
            (cons (car remaining) earlier)
            allowed
            edges)))
    0))

(defun q510197-odd-components-after-deletion
    (vertices edges removed)
  (let ((allowed
         (q510197-remove-members vertices removed)))
    (q510197-odd-components-count-aux
     allowed nil allowed edges)))

;; Inclusion and exclusion recursively enumerate every vertex subset U. The
;; leaf condition is the negation of IsTutteViolator:
;; oddComponents(G - U) <= |U|.

(defun q510197-all-subsets-satisfy-tutte-p
    (remaining selected vertices edges)
  (declare (xargs :measure (len remaining)))
  (if (consp remaining)
      (and
       (q510197-all-subsets-satisfy-tutte-p
        (cdr remaining)
        (cons (car remaining) selected)
        vertices
        edges)
       (q510197-all-subsets-satisfy-tutte-p
        (cdr remaining)
        selected
        vertices
        edges))
    (<=
     (q510197-odd-components-after-deletion
      vertices edges selected)
     (len selected))))

(defun q510197-tutte-condition-p (vertices edges)
  (q510197-all-subsets-satisfy-tutte-p
   vertices nil vertices edges))

(defun thousand-theorems-q510197-tutte-theorem-statement
    (vertices edges)
  (implies
   (q510197-simple-graph-p vertices edges)
   (equal
    (q510197-has-perfect-matching-p vertices edges)
    (q510197-tutte-condition-p vertices edges))))

(value-triple :itpeval-statement-checked)
:q
