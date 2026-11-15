;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/bellman_ford_BellmanFord_relaxqtvc: the Bellman-Ford edge-relaxation
;; verification condition preserving the path-based distance invariant.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces retain the arbitrary source vertex and distance-map
;; carriers.  Their typing and specification laws are explicit hypotheses of
;; the final statement predicate.

(defstub bfr-vertex-p (x) t)
(defstub bfr-vertices () t)
(defstub bfr-edges () t)
(defstub bfr-source () t)
(defstub bfr-weight (left right) t)

(defstub bfr-map-p (x) t)
(defstub bfr-contents (map vertex) t)
(defstub bfr-map-read (map vertex) t)
(defstub bfr-map-update (map vertex value) t)

;; Ordered pairs use an injective tagged representation.

(defun bfr-edge (left right)
  (list :edge left right))

(defun bfr-edge-pair-p (edge)
  (and
   (true-listp edge)
   (equal (len edge) 3)
   (equal (car edge) :edge)
   (bfr-vertex-p (cadr edge))
   (bfr-vertex-p (caddr edge))))

(defun bfr-edge-left (edge)
  (cadr edge))

(defun bfr-edge-right (edge)
  (caddr edge))

;; Finsets are duplicate-free true lists.  This represents every finite set;
;; membership and insertion below ignore list order.

(defun bfr-vertex-fset-p (set)
  (if (endp set)
      (equal set nil)
    (and
     (bfr-vertex-p (car set))
     (not (member-equal (car set) (cdr set)))
     (bfr-vertex-fset-p (cdr set)))))

(defun bfr-edge-fset-p (set)
  (if (endp set)
      (equal set nil)
    (and
     (bfr-edge-pair-p (car set))
     (not (member-equal (car set) (cdr set)))
     (bfr-edge-fset-p (cdr set)))))

(defun bfr-edge-insert (edge set)
  (if (member-equal edge set)
      set
    (cons edge set)))

(defun bfr-vertex-list-p (path)
  (if (endp path)
      (equal path nil)
    (and
     (bfr-vertex-p (car path))
     (bfr-vertex-list-p (cdr path)))))

;; The source IntInf datatype and its addition and strict order.

(defun bfr-finite (value)
  (list :finite value))

(defun bfr-finite-p (value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (equal (car value) :finite)
   (integerp (cadr value))))

(defun bfr-intinf-p (value)
  (or
   (equal value :infinite)
   (bfr-finite-p value)))

(defun bfr-intinf-add (left right)
  (if (equal left :infinite)
      :infinite
    (if (equal right :infinite)
        :infinite
      (bfr-finite
       (+ (cadr left) (cadr right))))))

(defun bfr-intinf-lt-p (left right)
  (if (equal left :infinite)
      nil
    (if (equal right :infinite)
        t
      (< (cadr left) (cadr right)))))

;; Executable presentations of the source inductive path relation and
;; recursive path-weight definition.

(defun bfr-edge-rel-p (left right)
  (member-equal
   (bfr-edge left right)
   (bfr-edges)))

(defun bfr-path-p (source path destination)
  (declare (xargs :measure (acl2-count path)))
  (and
   (bfr-vertex-p source)
   (bfr-vertex-p destination)
   (bfr-vertex-list-p path)
   (if (endp path)
       (equal source destination)
     (and
      (equal (car path) source)
      (if (endp (cdr path))
          (bfr-edge-rel-p source destination)
        (and
         (bfr-edge-rel-p source (cadr path))
         (bfr-path-p
          (cadr path)
          (cdr path)
          destination)))))))

(defun bfr-path-weight (path destination)
  (declare (xargs :measure (acl2-count path)))
  (if (endp path)
      0
    (if (endp (cdr path))
        (bfr-weight (car path) destination)
      (+ (bfr-weight (car path) (cadr path))
         (bfr-path-weight (cdr path) destination)))))

;; Explicit source-context laws.

(defun-sk bfr-vertex-inhabited-p ()
  (exists (vertex)
    (bfr-vertex-p vertex)))

(defun-sk bfr-map-inhabited-p ()
  (exists (map)
    (bfr-map-p map)))

(defun-sk bfr-edge-endpoints-law-p ()
  (forall (edge)
    (implies
     (member-equal edge (bfr-edges))
     (and
      (member-equal
       (bfr-edge-left edge)
       (bfr-vertices))
      (member-equal
       (bfr-edge-right edge)
       (bfr-vertices))))))

(defun-sk bfr-weight-type-law-p ()
  (forall (left right)
    (implies
     (and
      (bfr-vertex-p left)
      (bfr-vertex-p right))
     (integerp
      (bfr-weight left right)))))

(defun-sk bfr-contents-type-law-p ()
  (forall (map vertex)
    (implies
     (and
      (bfr-map-p map)
      (bfr-vertex-p vertex))
     (bfr-intinf-p
      (bfr-contents map vertex)))))

(defun-sk bfr-map-read-law-p ()
  (forall (map vertex)
    (implies
     (and
      (bfr-map-p map)
      (bfr-vertex-p vertex))
     (equal
      (bfr-map-read map vertex)
      (bfr-contents map vertex)))))

(defun-sk bfr-map-update-laws-p ()
  (forall (map key value vertex)
    (implies
     (and
      (bfr-map-p map)
      (bfr-vertex-p key)
      (bfr-intinf-p value)
      (bfr-vertex-p vertex))
     (and
      (bfr-map-p
       (bfr-map-update map key value))
      (equal
       (bfr-contents
        (bfr-map-update map key value)
        vertex)
       (if (equal vertex key)
           value
         (bfr-contents map vertex)))))))

(defun bfr-background-p ()
  (and
   (bfr-vertex-inhabited-p)
   (bfr-map-inhabited-p)
   (bfr-vertex-fset-p
    (bfr-vertices))
   (bfr-edge-fset-p
    (bfr-edges))
   (bfr-edge-endpoints-law-p)
   (bfr-vertex-p
    (bfr-source))
   (member-equal
    (bfr-source)
    (bfr-vertices))
   (bfr-weight-type-law-p)
   (bfr-contents-type-law-p)
   (bfr-map-read-law-p)
   (bfr-map-update-laws-p)))

;; The path-based Bellman-Ford invariant inv1.

(defun-sk bfr-finite-path-exists-p (vertex value)
  (exists (path)
    (and
     (bfr-vertex-list-p path)
     (bfr-path-p
      (bfr-source)
      path
      vertex)
     (equal
      (bfr-path-weight path vertex)
      value))))

(defun-sk bfr-finite-short-path-lower-bound-p
  (vertex value pass)
  (forall (path)
    (implies
     (bfr-vertex-list-p path)
     (implies
      (bfr-path-p
       (bfr-source)
       path
       vertex)
      (implies
       (< (len path) pass)
       (<= value
           (bfr-path-weight path vertex)))))))

(defun-sk bfr-finite-via-lower-bound-p
  (vertex value pass via)
  (forall (predecessor path)
    (implies
     (and
      (bfr-vertex-p predecessor)
      (bfr-vertex-list-p path))
     (implies
      (bfr-path-p
       (bfr-source)
       path
       predecessor)
      (implies
       (< (len path) pass)
       (implies
        (member-equal
         (bfr-edge predecessor vertex)
         via)
        (<= value
            (+ (bfr-path-weight
                path predecessor)
               (bfr-weight
                predecessor vertex)))))))))

(defun-sk bfr-infinite-path-length-p (vertex pass)
  (forall (path)
    (implies
     (bfr-vertex-list-p path)
     (implies
      (bfr-path-p
       (bfr-source)
       path
       vertex)
      (<= pass (len path))))))

(defun-sk bfr-infinite-via-length-p (vertex pass via)
  (forall (predecessor path)
    (implies
     (and
      (bfr-vertex-p predecessor)
      (bfr-vertex-list-p path))
     (implies
      (member-equal
       (bfr-edge predecessor vertex)
       via)
      (implies
       (bfr-path-p
        (bfr-source)
        path
        predecessor)
       (<= pass (len path)))))))

(defun bfr-inv1-at-vertex-p (map pass via vertex)
  (let ((distance
         (bfr-map-read map vertex)))
    (if (bfr-finite-p distance)
        (let ((value (cadr distance)))
          (and
           (bfr-finite-path-exists-p
            vertex value)
           (bfr-finite-short-path-lower-bound-p
            vertex value pass)
           (bfr-finite-via-lower-bound-p
            vertex value pass via)))
      (and
       (bfr-infinite-path-length-p
        vertex pass)
       (bfr-infinite-via-length-p
        vertex pass via)))))

(defun-sk bfr-inv1-p (map pass via)
  (forall (vertex)
    (implies
     (bfr-vertex-p vertex)
     (implies
      (member-equal
       vertex
       (bfr-vertices))
      (bfr-inv1-at-vertex-p
       map pass via vertex)))))

;; The nested implications retain the two source let-bound accessor equations.

(defun ntp4vc-pearl-bellman-ford-bellman-ford-relaxqtvc-statement
    (pass u v via map)
  (implies
   (bfr-background-p)
   (implies
    (and
     (integerp pass)
     (bfr-vertex-p u)
     (bfr-vertex-p v)
     (bfr-edge-fset-p via)
     (bfr-map-p map)
     (<= 1 pass)
     (member-equal
      (bfr-edge u v)
      (bfr-edges))
     (not
      (member-equal
       (bfr-edge u v)
       via))
     (bfr-inv1-p map pass via))
    (let* ((o1 (bfr-map-read map u)))
      (implies
       (equal o1 (bfr-contents map u))
       (let* ((n
               (bfr-intinf-add
                o1
                (bfr-finite
                 (bfr-weight u v))))
              (o2
               (bfr-map-read map v)))
         (implies
          (equal o2 (bfr-contents map v))
          (if (bfr-intinf-lt-p n o2)
              (bfr-inv1-p
               (bfr-map-update map v n)
               pass
               (bfr-edge-insert
                (bfr-edge u v)
                via))
            (bfr-inv1-p
             map
             pass
             (bfr-edge-insert
              (bfr-edge u v)
              via))))))))))

(value-triple :itpeval-statement-checked)
:q
