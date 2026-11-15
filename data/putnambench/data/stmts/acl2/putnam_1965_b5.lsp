;; Statement-only formalization of PutnamBench artifact putnam_1965_b5:
;; if 4E <= V^2, a finite simple undirected graph on V vertices exists with
;; exactly E edges and no triangle. This file contains no proof.

(in-package "ACL2")

;; The canonical vertex carrier is {0,...,V-1}. Every finite type of
;; cardinality V is bijective with this carrier, and transporting adjacency
;; along such a bijection preserves edge count and triangles.

(defun putnam-1965-b5-naturals-below-aux (remaining next)
  (if (zp remaining)
      nil
    (cons next
          (putnam-1965-b5-naturals-below-aux
           (- remaining 1)
           (+ next 1)))))

(defun putnam-1965-b5-naturals-below (v)
  (putnam-1965-b5-naturals-below-aux v 0))

;; Each pair (u v) below has u before v in VERTICES, so subsets of ALL-PAIRS
;; are in bijection with simple undirected graphs on the carrier.

(defun putnam-1965-b5-pairs-with-first (first remaining)
  (if (consp remaining)
      (cons (list first (car remaining))
            (putnam-1965-b5-pairs-with-first
             first (cdr remaining)))
    nil))

(defun putnam-1965-b5-all-pairs (vertices)
  (if (consp vertices)
      (append
       (putnam-1965-b5-pairs-with-first
        (car vertices) (cdr vertices))
       (putnam-1965-b5-all-pairs (cdr vertices)))
    nil))

(defun putnam-1965-b5-adjacent-p (edges left right)
  (or (member-equal (list left right) edges)
      (member-equal (list right left) edges)))

(defun putnam-1965-b5-triangle-third-p
    (first second candidates edges)
  (if (consp candidates)
      (or
       (and
        (putnam-1965-b5-adjacent-p edges first second)
        (putnam-1965-b5-adjacent-p
         edges first (car candidates))
        (putnam-1965-b5-adjacent-p
         edges second (car candidates)))
       (putnam-1965-b5-triangle-third-p
        first second (cdr candidates) edges))
    nil))

(defun putnam-1965-b5-triangle-second-p
    (first candidates vertices edges)
  (if (consp candidates)
      (or
       (putnam-1965-b5-triangle-third-p
        first (car candidates) vertices edges)
       (putnam-1965-b5-triangle-second-p
        first (cdr candidates) vertices edges))
    nil))

(defun putnam-1965-b5-triangle-p
    (candidates vertices edges)
  (if (consp candidates)
      (or
       (putnam-1965-b5-triangle-second-p
        (car candidates) vertices vertices edges)
       (putnam-1965-b5-triangle-p
        (cdr candidates) vertices edges))
    nil))

;; This finite branching search is the source's internal existential
;; quantifier over graphs. It considers every subset of the complete graph;
;; no graph witness is supplied as an external parameter.

(defun putnam-1965-b5-graph-exists-from-p
    (remaining-pairs selected vertices edge-count)
  (declare (xargs :measure (len remaining-pairs)))
  (if (consp remaining-pairs)
      (or
       (putnam-1965-b5-graph-exists-from-p
        (cdr remaining-pairs)
        (cons (car remaining-pairs) selected)
        vertices
        edge-count)
       (putnam-1965-b5-graph-exists-from-p
        (cdr remaining-pairs)
        selected
        vertices
        edge-count))
    (and
     (equal (len selected) edge-count)
     (not
      (putnam-1965-b5-triangle-p
       vertices vertices selected)))))

(defun putnam-1965-b5-graph-exists-p (v edge-count)
  (let ((vertices (putnam-1965-b5-naturals-below v)))
    (putnam-1965-b5-graph-exists-from-p
     (putnam-1965-b5-all-pairs vertices)
     nil
     vertices
     edge-count)))

(defun putnambench-putnam-1965-b5-statement (v e)
  (implies
   (and
    (natp v)
    (natp e)
    (<= (* 4 e) (* v v)))
   (putnam-1965-b5-graph-exists-p v e)))

(value-triple :itpeval-statement-checked)
:q
