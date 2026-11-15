;; Statement-only formalization of thousand-theorems corpus artifact Q5504427,
;; "Friendship theorem": every nonempty finite simple undirected graph in which
;; each distinct pair of vertices has exactly one common neighbor has a vertex
;; adjacent to every other vertex. This file contains no proof.

(in-package "ACL2")

;; A duplicate-free true list enumerates the finite vertex type. Each edge is
;; an unordered pair of distinct enumerated vertices, and no undirected edge
;; occurs twice. Thus valid lists represent exactly the finite simple graphs
;; in the source, independently of carrier order and edge orientation.

(defun q5504427-carrier-p (vertices)
  (and
   (true-listp vertices)
   (no-duplicatesp-equal vertices)))

(defun q5504427-edge-record-p (edge vertices)
  (and
   (true-listp edge)
   (equal (len edge) 2)
   (member-equal (nth 0 edge) vertices)
   (member-equal (nth 1 edge) vertices)
   (not (equal (nth 0 edge) (nth 1 edge)))))

(defun q5504427-same-undirected-edge-p (left right)
  (or
   (and
    (equal (nth 0 left) (nth 0 right))
    (equal (nth 1 left) (nth 1 right)))
   (and
    (equal (nth 0 left) (nth 1 right))
    (equal (nth 1 left) (nth 0 right)))))

(defun q5504427-edge-distinct-from-list-p (edge remaining)
  (if (consp remaining)
      (and
       (not
        (q5504427-same-undirected-edge-p
         edge (car remaining)))
       (q5504427-edge-distinct-from-list-p
        edge (cdr remaining)))
    t))

(defun q5504427-edge-list-p (edges vertices)
  (if (consp edges)
      (and
       (q5504427-edge-record-p (car edges) vertices)
       (q5504427-edge-distinct-from-list-p
        (car edges) (cdr edges))
       (q5504427-edge-list-p (cdr edges) vertices))
    (equal edges nil)))

(defun q5504427-simple-graph-p (vertices edges)
  (and
   (q5504427-carrier-p vertices)
   (q5504427-edge-list-p edges vertices)))

(defun q5504427-adjacent-p (edges left right)
  (if (or
       (member-equal (list left right) edges)
       (member-equal (list right left) edges))
      t
    nil))

(defun q5504427-common-neighbor-count
    (left right candidates edges)
  (if (consp candidates)
      (+
       (if (and
            (q5504427-adjacent-p
             edges left (car candidates))
            (q5504427-adjacent-p
             edges right (car candidates)))
           1
         0)
       (q5504427-common-neighbor-count
        left right (cdr candidates) edges))
    0))

(defun q5504427-friendship-row-p
    (left remaining vertices edges)
  (if (consp remaining)
      (and
       (or
        (equal left (car remaining))
        (equal
         (q5504427-common-neighbor-count
          left (car remaining) vertices edges)
         1))
       (q5504427-friendship-row-p
        left (cdr remaining) vertices edges))
    t))

(defun q5504427-friendship-p
    (remaining vertices edges)
  (if (consp remaining)
      (and
       (q5504427-friendship-row-p
        (car remaining) vertices vertices edges)
       (q5504427-friendship-p
        (cdr remaining) vertices edges))
    t))

(defun q5504427-politician-p
    (candidate vertices edges)
  (if (consp vertices)
      (and
       (or
        (equal candidate (car vertices))
        (q5504427-adjacent-p
         edges candidate (car vertices)))
       (q5504427-politician-p
        candidate (cdr vertices) edges))
    t))

(defun q5504427-politician-in-list-p
    (remaining vertices edges)
  (if (consp remaining)
      (or
       (q5504427-politician-p
        (car remaining) vertices edges)
       (q5504427-politician-in-list-p
        (cdr remaining) vertices edges))
    nil))

(defun q5504427-politician-exists-p (vertices edges)
  (q5504427-politician-in-list-p
   vertices vertices edges))

(defun thousand-theorems-q5504427-friendship-theorem-statement
    (vertices edges)
  (implies
   (and
    (consp vertices)
    (q5504427-simple-graph-p vertices edges)
    (q5504427-friendship-p
     vertices vertices edges))
   (q5504427-politician-exists-p vertices edges)))

(value-triple :itpeval-statement-checked)
:q
