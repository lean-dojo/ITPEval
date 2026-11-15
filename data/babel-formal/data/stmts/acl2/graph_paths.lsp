;; Statement-only formalization of Babel-formal artifact graph_paths:
;; reflexive-transitive paths in arbitrary directed relations, path
;; concatenation, edge reversal, and reversal for undirected relations. This
;; file contains no proof.

(in-package "ACL2")

;; CARRIER and EDGE are ACL2 function objects evaluated by APPLY$.  They
;; represent an arbitrary vertex-domain predicate and binary edge relation,
;; without enumerating either one as a finite table.

(defun graph-paths-vertexp (carrier vertex)
  (if (apply$ carrier (list vertex))
      t
    nil))

(defun graph-paths-edgep (edge u v)
  (if (apply$ edge (list u v))
      t
    nil))

(defun graph-paths-oriented-edgep (edge orientation u v)
  (cond ((equal orientation :reverse)
         (graph-paths-edgep edge v u))
        ((equal orientation :symmetric)
         (or (graph-paths-edgep edge u v)
             (graph-paths-edgep edge v u)))
        (t
         (graph-paths-edgep edge u v))))

(defun graph-paths-edges-alongp (edge orientation vertices)
  (if (and (consp vertices)
           (consp (cdr vertices)))
      (and (graph-paths-oriented-edgep
            edge orientation (car vertices) (cadr vertices))
           (graph-paths-edges-alongp
            edge orientation (cdr vertices)))
    t))

(defun graph-paths-vertices-in-carrierp (carrier vertices)
  (if (consp vertices)
      (and (graph-paths-vertexp carrier (car vertices))
           (graph-paths-vertices-in-carrierp carrier (cdr vertices)))
    (equal vertices nil)))

(defun graph-paths-last-vertex (vertices)
  (if (and (consp vertices)
           (consp (cdr vertices)))
      (graph-paths-last-vertex (cdr vertices))
    (if (consp vertices)
        (car vertices)
      nil)))

;; A nonempty vertex list is constructor evidence for the inductive Path
;; relation: a singleton is Pnil, and each additional vertex is a Pstep.

(defun graph-paths-pathp (carrier edge orientation u v vertices)
  (and (true-listp vertices)
       (consp vertices)
       (graph-paths-vertices-in-carrierp carrier vertices)
       (equal (car vertices) u)
       (equal (graph-paths-last-vertex vertices) v)
       (graph-paths-edges-alongp edge orientation vertices)))

(defun graph-paths-snoc (vertices vertex)
  (if (consp vertices)
      (cons (car vertices)
            (graph-paths-snoc (cdr vertices) vertex))
    (list vertex)))

(defun graph-paths-append-paths (left right)
  (if (and (consp left)
           (consp (cdr left)))
      (cons (car left)
            (graph-paths-append-paths (cdr left) right))
    right))

(defun graph-paths-reverse-onto (vertices accumulator)
  (if (consp vertices)
      (graph-paths-reverse-onto
       (cdr vertices)
       (cons (car vertices) accumulator))
    accumulator))

(defun graph-paths-reverse-path (vertices)
  (graph-paths-reverse-onto vertices nil))

(defun graph-paths-refl-statement (carrier edge v)
  (implies (graph-paths-vertexp carrier v)
           (graph-paths-pathp
            carrier edge :forward v v (list v))))

(defun graph-paths-trans-statement
  (carrier edge u v w path-uv path-vw)
  (implies (and (graph-paths-pathp
                 carrier edge :forward u v path-uv)
                (graph-paths-pathp
                 carrier edge :forward v w path-vw))
           (graph-paths-pathp
            carrier edge :forward u w
            (graph-paths-append-paths path-uv path-vw))))

;; Every undirected relation E is extensionally equal to the symmetrization of
;; E itself.  Conversely, symmetrizing any relation always gives an
;; undirected relation.  Quantifying EDGE here therefore ranges over exactly
;; all undirected relations without restricting the vertex domain.

(defun graph-paths-reverse-path-statement
  (carrier edge u v path-uv)
  (implies (graph-paths-pathp
            carrier edge :symmetric u v path-uv)
           (graph-paths-pathp
            carrier edge :symmetric v u
            (graph-paths-reverse-path path-uv))))

(defun graph-paths-concat-edge-right-statement
  (carrier edge u v w path-uv)
  (implies (and (graph-paths-pathp
                 carrier edge :forward u v path-uv)
                (graph-paths-vertexp carrier w)
                (graph-paths-edgep edge v w))
           (graph-paths-pathp
            carrier edge :forward u w
            (graph-paths-snoc path-uv w))))

(defun graph-paths-concat-statement
  (carrier edge u v w path-uv path-vw)
  (implies (and (graph-paths-pathp
                 carrier edge :forward u v path-uv)
                (graph-paths-pathp
                 carrier edge :forward v w path-vw))
           (graph-paths-pathp
            carrier edge :forward u w
            (graph-paths-append-paths path-uv path-vw))))

(defun graph-paths-edge-path-statement (carrier edge u v)
  (implies (and (graph-paths-vertexp carrier u)
                (graph-paths-vertexp carrier v)
                (graph-paths-edgep edge u v))
           (graph-paths-pathp
            carrier edge :forward u v (list u v))))

(defun graph-paths-concat-edge-left-statement
  (carrier edge u v w path-vw)
  (implies (and (graph-paths-vertexp carrier u)
                (graph-paths-edgep edge u v)
                (graph-paths-pathp
                 carrier edge :forward v w path-vw))
           (graph-paths-pathp
            carrier edge :forward u w (cons u path-vw))))

(defun graph-paths-concat3-statement
  (carrier edge u v w terminal path-uv path-vw path-wt)
  (implies (and (graph-paths-pathp
                 carrier edge :forward u v path-uv)
                (graph-paths-pathp
                 carrier edge :forward v w path-vw)
                (graph-paths-pathp
                 carrier edge :forward w terminal path-wt))
           (graph-paths-pathp
            carrier edge :forward u terminal
            (graph-paths-append-paths
             (graph-paths-append-paths path-uv path-vw)
             path-wt))))

(defun graph-paths-reverse-in-erev-statement
  (carrier edge u v path-uv)
  (implies (graph-paths-pathp
            carrier edge :forward u v path-uv)
           (graph-paths-pathp
            carrier edge :reverse v u
            (graph-paths-reverse-path path-uv))))

(defun graph-paths-cycle-refl-statement
  (carrier edge v w path-vw path-wv)
  (implies (and (graph-paths-pathp
                 carrier edge :forward v w path-vw)
                (graph-paths-pathp
                 carrier edge :forward w v path-wv))
           (graph-paths-pathp
            carrier edge :forward v v
            (graph-paths-append-paths path-vw path-wv))))

(value-triple :itpeval-statement-checked)
:q
