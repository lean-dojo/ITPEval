;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__083, "The Friendship Theorem": every finite simple
;; undirected graph in which each pair of distinct vertices has exactly one
;; common neighbor has a vertex adjacent to every other vertex. This file
;; contains no proof.

(in-package "ACL2")

;; The duplicate-free list VERTICES is the finite carrier.  Each member
;; (u v) of EDGES denotes the ordered adjacency pair from u to v.

(defun ht083-carrier-p (vertices)
  (and (true-listp vertices)
       (no-duplicatesp-equal vertices)))

(defun ht083-edge-recordp (edge vertices)
  (and (true-listp edge)
       (equal (len edge) 2)
       (member-equal (nth 0 edge) vertices)
       (member-equal (nth 1 edge) vertices)))

(defun ht083-edge-listp (edges vertices)
  (if (consp edges)
      (and (ht083-edge-recordp (car edges) vertices)
           (ht083-edge-listp (cdr edges) vertices))
    (equal edges nil)))

(defun ht083-adjacent-p (edges u v)
  (if (member-equal (list u v) edges)
      t
    nil))

(defun ht083-symmetric-p (remaining-edges edges)
  (if (consp remaining-edges)
      (let ((edge (car remaining-edges)))
        (and
         (ht083-adjacent-p
          edges
          (nth 1 edge)
          (nth 0 edge))
         (ht083-symmetric-p (cdr remaining-edges) edges)))
    t))

(defun ht083-irreflexive-p (vertices edges)
  (if (consp vertices)
      (and
       (not (ht083-adjacent-p edges (car vertices) (car vertices)))
       (ht083-irreflexive-p (cdr vertices) edges))
    t))

(defun ht083-common-neighbor-count (u v candidates edges)
  (if (consp candidates)
      (+
       (if (and (ht083-adjacent-p edges u (car candidates))
                (ht083-adjacent-p edges v (car candidates)))
           1
         0)
       (ht083-common-neighbor-count u v (cdr candidates) edges))
    0))

(defun ht083-friendship-row-p (u remaining vertices edges)
  (if (consp remaining)
      (and
       (or
        (equal u (car remaining))
        (equal
         (ht083-common-neighbor-count
          u (car remaining) vertices edges)
         1))
       (ht083-friendship-row-p
        u (cdr remaining) vertices edges))
    t))

(defun ht083-friendship-p (remaining vertices edges)
  (if (consp remaining)
      (and
       (ht083-friendship-row-p
        (car remaining) vertices vertices edges)
       (ht083-friendship-p (cdr remaining) vertices edges))
    t))

(defun ht083-finite-friendship-graph-p (vertices edges)
  (and
   (ht083-carrier-p vertices)
   (ht083-edge-listp edges vertices)
   (ht083-symmetric-p edges edges)
   (ht083-irreflexive-p vertices edges)
   (ht083-friendship-p vertices vertices edges)))

(defun ht083-politician-p (candidate vertices edges)
  (if (consp vertices)
      (and
       (or
        (equal candidate (car vertices))
        (ht083-adjacent-p edges candidate (car vertices)))
       (ht083-politician-p candidate (cdr vertices) edges))
    t))

(defun ht083-politician-in-list-p
    (remaining vertices edges)
  (if (consp remaining)
      (or
       (ht083-politician-p (car remaining) vertices edges)
       (ht083-politician-in-list-p
        (cdr remaining) vertices edges))
    nil))

(defun ht083-has-politician-p (vertices edges)
  (ht083-politician-in-list-p vertices vertices edges))

(defun hundred-theorems-083-the-friendship-theorem-statement
    (vertices edges)
  (implies
   (and
    (consp vertices)
    (ht083-finite-friendship-graph-p vertices edges))
   (ht083-has-politician-p vertices edges)))

(value-triple :itpeval-statement-checked)
:q
