;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/bellman_ford_BellmanFord_bellman_fordqtvc: the Bellman-Ford
;; verification condition for loop invariants, shortest-path certificates,
;; and detection of a reachable negative cycle.  This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces retain the arbitrary source vertex, map, and set
;; carriers.  Their typing and specification laws are hypotheses of the final
;; statement predicate.

(defstub bfvc-vertex-p (x) t)
(defstub bfvc-vertices () t)
(defstub bfvc-edges () t)
(defstub bfvc-source () t)
(defstub bfvc-weight (left right) t)

(defstub bfvc-map-p (x) t)
(defstub bfvc-contents (map vertex) t)
(defstub bfvc-create (value) t)
(defstub bfvc-map-update (map vertex value) t)

(defstub bfvc-set-p (x) t)
(defstub bfvc-to-fset (set) t)
(defstub bfvc-choose (set) t)

;; Ordered pairs use an injective tagged representation.

(defun bfvc-edge (left right)
  (list :edge left right))

(defun bfvc-edge-pair-p (edge)
  (and
   (true-listp edge)
   (equal (len edge) 3)
   (equal (car edge) :edge)
   (bfvc-vertex-p (cadr edge))
   (bfvc-vertex-p (caddr edge))))

(defun bfvc-edge-left (edge)
  (cadr edge))

(defun bfvc-edge-right (edge)
  (caddr edge))

;; Finsets are duplicate-free true lists.  This represents every finite set,
;; while list order is ignored by all set operations below.

(defun bfvc-vertex-fset-p (set)
  (if (endp set)
      (equal set nil)
    (and
     (bfvc-vertex-p (car set))
     (not (member-equal (car set) (cdr set)))
     (bfvc-vertex-fset-p (cdr set)))))

(defun bfvc-edge-fset-p (set)
  (if (endp set)
      (equal set nil)
    (and
     (bfvc-edge-pair-p (car set))
     (not (member-equal (car set) (cdr set)))
     (bfvc-edge-fset-p (cdr set)))))

(defun bfvc-edge-subset-p (left right)
  (if (endp left)
      (equal left nil)
    (and
     (member-equal (car left) right)
     (bfvc-edge-subset-p (cdr left) right))))

(defun bfvc-edge-set-equal-p (left right)
  (and
   (bfvc-edge-subset-p left right)
   (bfvc-edge-subset-p right left)))

(defun bfvc-edge-remove (edge set)
  (if (endp set)
      nil
    (if (equal edge (car set))
        (cdr set)
      (cons
       (car set)
       (bfvc-edge-remove edge (cdr set))))))

(defun bfvc-edge-difference (left right)
  (if (endp left)
      nil
    (if (member-equal (car left) right)
        (bfvc-edge-difference (cdr left) right)
      (cons
       (car left)
       (bfvc-edge-difference (cdr left) right)))))

(defun bfvc-edge-insert (edge set)
  (if (member-equal edge set)
      set
    (cons edge set)))

(defun bfvc-vertex-list-p (path)
  (if (endp path)
      (equal path nil)
    (and
     (bfvc-vertex-p (car path))
     (bfvc-vertex-list-p (cdr path)))))

;; The source IntInf datatype and its operations.

(defun bfvc-finite (value)
  (list :finite value))

(defun bfvc-finite-p (value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (equal (car value) :finite)
   (integerp (cadr value))))

(defun bfvc-intinf-p (value)
  (or
   (equal value :infinite)
   (bfvc-finite-p value)))

(defun bfvc-intinf-add (left right)
  (if (equal left :infinite)
      :infinite
    (if (equal right :infinite)
        :infinite
      (bfvc-finite
       (+ (cadr left) (cadr right))))))

(defun bfvc-intinf-eq-p (left right)
  (if (equal left :infinite)
      (equal right :infinite)
    (and
     (bfvc-finite-p right)
     (equal (cadr left) (cadr right)))))

(defun bfvc-intinf-lt-p (left right)
  (if (equal left :infinite)
      nil
    (if (equal right :infinite)
        t
      (< (cadr left) (cadr right)))))

(defun bfvc-intinf-le-p (left right)
  (or
   (bfvc-intinf-lt-p left right)
   (bfvc-intinf-eq-p left right)))

;; Direct executable presentations of the source inductive path relation and
;; recursive path weight.

(defun bfvc-edge-rel-p (left right)
  (member-equal
   (bfvc-edge left right)
   (bfvc-edges)))

(defun bfvc-path-p (source path destination)
  (declare (xargs :measure (acl2-count path)))
  (and
   (bfvc-vertex-p source)
   (bfvc-vertex-p destination)
   (bfvc-vertex-list-p path)
   (if (endp path)
       (equal source destination)
     (and
      (equal (car path) source)
      (if (endp (cdr path))
          (bfvc-edge-rel-p source destination)
        (and
         (bfvc-edge-rel-p source (cadr path))
         (bfvc-path-p
          (cadr path)
          (cdr path)
          destination)))))))

(defun bfvc-path-weight (path destination)
  (declare (xargs :measure (acl2-count path)))
  (if (endp path)
      0
    (if (endp (cdr path))
        (bfvc-weight (car path) destination)
      (+ (bfvc-weight (car path) (cadr path))
         (bfvc-path-weight (cdr path) destination)))))

(defun-sk bfvc-negative-cycle-p (vertex)
  (exists (prefix cycle)
    (and
     (bfvc-vertex-list-p prefix)
     (bfvc-vertex-list-p cycle)
     (member-equal vertex (bfvc-vertices))
     (bfvc-path-p (bfvc-source) prefix vertex)
     (bfvc-path-p vertex cycle vertex)
     (< (bfvc-path-weight cycle vertex) 0))))

;; Explicit source-context laws.

(defun-sk bfvc-vertex-inhabited-p ()
  (exists (vertex)
    (bfvc-vertex-p vertex)))

(defun-sk bfvc-map-inhabited-p ()
  (exists (map)
    (bfvc-map-p map)))

(defun-sk bfvc-set-inhabited-p ()
  (exists (set)
    (bfvc-set-p set)))

(defun-sk bfvc-edge-endpoints-law-p ()
  (forall (edge)
    (implies
     (member-equal edge (bfvc-edges))
     (and
      (member-equal
       (bfvc-edge-left edge)
       (bfvc-vertices))
      (member-equal
       (bfvc-edge-right edge)
       (bfvc-vertices))))))

(defun-sk bfvc-weight-type-law-p ()
  (forall (left right)
    (implies
     (and
      (bfvc-vertex-p left)
      (bfvc-vertex-p right))
     (integerp
      (bfvc-weight left right)))))

(defun-sk bfvc-set-function-laws-p ()
  (forall (set)
    (implies
     (bfvc-set-p set)
     (and
      (bfvc-edge-fset-p
       (bfvc-to-fset set))
      (bfvc-edge-pair-p
       (bfvc-choose set))
      (implies
       (not (equal (bfvc-to-fset set) nil))
       (member-equal
        (bfvc-choose set)
        (bfvc-to-fset set)))))))

(defun-sk bfvc-contents-type-law-p ()
  (forall (map vertex)
    (implies
     (and
      (bfvc-map-p map)
      (bfvc-vertex-p vertex))
     (bfvc-intinf-p
      (bfvc-contents map vertex)))))

(defun-sk bfvc-create-laws-p ()
  (forall (value vertex)
    (implies
     (and
      (bfvc-intinf-p value)
      (bfvc-vertex-p vertex))
     (and
      (bfvc-map-p
       (bfvc-create value))
      (equal
       (bfvc-contents
        (bfvc-create value)
        vertex)
       value)))))

(defun-sk bfvc-map-update-laws-p ()
  (forall (map key value vertex)
    (implies
     (and
      (bfvc-map-p map)
      (bfvc-vertex-p key)
      (bfvc-intinf-p value)
      (bfvc-vertex-p vertex))
     (and
      (bfvc-map-p
       (bfvc-map-update map key value))
      (equal
       (bfvc-contents
        (bfvc-map-update map key value)
        vertex)
       (if (equal vertex key)
           value
         (bfvc-contents map vertex)))))))

(defun bfvc-background-p ()
  (and
   (bfvc-vertex-inhabited-p)
   (bfvc-map-inhabited-p)
   (bfvc-set-inhabited-p)
   (bfvc-vertex-fset-p
    (bfvc-vertices))
   (bfvc-edge-fset-p
    (bfvc-edges))
   (bfvc-edge-endpoints-law-p)
   (bfvc-vertex-p
    (bfvc-source))
   (member-equal
    (bfvc-source)
    (bfvc-vertices))
   (bfvc-weight-type-law-p)
   (bfvc-set-function-laws-p)
   (bfvc-contents-type-law-p)
   (bfvc-create-laws-p)
   (bfvc-map-update-laws-p)))

;; Bellman-Ford invariants.

(defun-sk bfvc-finite-path-exists-p (vertex value)
  (exists (path)
    (and
     (bfvc-vertex-list-p path)
     (bfvc-path-p
      (bfvc-source)
      path
      vertex)
     (equal
      (bfvc-path-weight path vertex)
      value))))

(defun-sk bfvc-finite-short-path-lower-bound-p
  (vertex value pass)
  (forall (path)
    (implies
     (bfvc-vertex-list-p path)
     (implies
      (bfvc-path-p
       (bfvc-source)
       path
       vertex)
      (implies
       (< (len path) pass)
       (<= value
           (bfvc-path-weight path vertex)))))))

(defun-sk bfvc-finite-via-lower-bound-p
  (vertex value pass via)
  (forall (predecessor path)
    (implies
     (and
      (bfvc-vertex-p predecessor)
      (bfvc-vertex-list-p path))
     (implies
      (bfvc-path-p
       (bfvc-source)
       path
       predecessor)
      (implies
       (< (len path) pass)
       (implies
        (member-equal
         (bfvc-edge predecessor vertex)
         via)
        (<= value
            (+ (bfvc-path-weight
                path predecessor)
               (bfvc-weight
                predecessor vertex)))))))))

(defun-sk bfvc-infinite-path-length-p (vertex pass)
  (forall (path)
    (implies
     (bfvc-vertex-list-p path)
     (implies
      (bfvc-path-p
       (bfvc-source)
       path
       vertex)
      (<= pass (len path))))))

(defun-sk bfvc-infinite-via-length-p (vertex pass via)
  (forall (predecessor path)
    (implies
     (and
      (bfvc-vertex-p predecessor)
      (bfvc-vertex-list-p path))
     (implies
      (member-equal
       (bfvc-edge predecessor vertex)
       via)
      (implies
       (bfvc-path-p
        (bfvc-source)
        path
        predecessor)
       (<= pass (len path)))))))

(defun bfvc-inv1-at-vertex-p (map pass via vertex)
  (let ((distance
         (bfvc-contents map vertex)))
    (if (bfvc-finite-p distance)
        (let ((value (cadr distance)))
          (and
           (bfvc-finite-path-exists-p
            vertex value)
           (bfvc-finite-short-path-lower-bound-p
            vertex value pass)
           (bfvc-finite-via-lower-bound-p
            vertex value pass via)))
      (and
       (bfvc-infinite-path-length-p
        vertex pass)
       (bfvc-infinite-via-length-p
        vertex pass via)))))

(defun-sk bfvc-inv1-p (map pass via)
  (forall (vertex)
    (implies
     (bfvc-vertex-p vertex)
     (implies
      (member-equal
       vertex
       (bfvc-vertices))
      (bfvc-inv1-at-vertex-p
       map pass via vertex)))))

(defun-sk bfvc-inv2-p (map via)
  (forall (left right)
    (implies
     (and
      (bfvc-vertex-p left)
      (bfvc-vertex-p right))
     (implies
      (member-equal
       (bfvc-edge left right)
       via)
      (bfvc-intinf-le-p
       (bfvc-contents map right)
       (bfvc-intinf-add
        (bfvc-contents map left)
        (bfvc-finite
         (bfvc-weight left right))))))))

;; The pass-invariant continuation for processing one nonempty edge set.

(defun-sk bfvc-pass-updated-map-continuation-p
  (index es1 es2 via edge)
  (forall (map3)
    (implies
     (bfvc-map-p map3)
     (implies
      (bfvc-inv1-p
       map3
       index
       (bfvc-edge-insert edge via))
      (and
       (<= 0 (len (bfvc-to-fset es1)))
       (< (len (bfvc-to-fset es2))
          (len (bfvc-to-fset es1)))
       (bfvc-edge-subset-p
        (bfvc-to-fset es2)
        (bfvc-edges))
       (bfvc-inv1-p
        map3
        index
        (bfvc-edge-difference
         (bfvc-edges)
         (bfvc-to-fset es2))))))))

(defun bfvc-pass-edge-conclusion-p
  (map2 index es1 es2 via)
  (let ((edge (bfvc-choose es1)))
    (and
     (and
      (<= 1 index)
      (member-equal edge (bfvc-edges))
      (not (member-equal edge via)))
     (bfvc-inv1-p map2 index via)
     (bfvc-pass-updated-map-continuation-p
      index es1 es2 via edge))))

(defun-sk bfvc-pass-nonempty-continuation-p
  (map2 index es1 via)
  (forall (es2)
    (implies
     (bfvc-set-p es2)
     (implies
      (and
       (member-equal
        (bfvc-choose es1)
        (bfvc-to-fset es1))
       (bfvc-edge-set-equal-p
        (bfvc-to-fset es2)
        (bfvc-edge-remove
         (bfvc-choose es1)
         (bfvc-to-fset es1))))
      (bfvc-pass-edge-conclusion-p
       map2 index es1 es2 via)))))

(defun bfvc-pass-es1-conclusion-p
  (map2 index es1)
  (if (not (equal (bfvc-to-fset es1) nil))
      (let ((via
             (bfvc-edge-difference
              (bfvc-edges)
              (bfvc-to-fset es1))))
        (and
         (not (equal (bfvc-to-fset es1) nil))
         (bfvc-pass-nonempty-continuation-p
          map2 index es1 via)))
    (bfvc-inv1-p map2 (+ index 1) nil)))

(defun-sk bfvc-pass-es1-continuation-p (index)
  (forall (es1 map2)
    (implies
     (and
      (bfvc-set-p es1)
      (bfvc-map-p map2))
     (implies
      (and
       (bfvc-edge-subset-p
        (bfvc-to-fset es1)
        (bfvc-edges))
       (bfvc-inv1-p
        map2
        index
        (bfvc-edge-difference
         (bfvc-edges)
         (bfvc-to-fset es1))))
      (bfvc-pass-es1-conclusion-p
       map2 index es1)))))

(defun bfvc-pass-es-conclusion-p (map1 index es)
  (and
   (bfvc-edge-subset-p
    (bfvc-to-fset es)
    (bfvc-edges))
   (bfvc-inv1-p
    map1
    index
    (bfvc-edge-difference
     (bfvc-edges)
     (bfvc-to-fset es)))
   (bfvc-pass-es1-continuation-p index)))

(defun-sk bfvc-pass-es-continuation-p (map1 index)
  (forall (es)
    (implies
     (bfvc-set-p es)
     (implies
      (bfvc-edge-set-equal-p
       (bfvc-to-fset es)
       (bfvc-edges))
      (bfvc-pass-es-conclusion-p
       map1 index es)))))

(defun-sk bfvc-pass-index-continuation-p (map1 upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (and
        (<= 1 index)
        (<= index upper))
       (bfvc-inv1-p map1 index nil))
      (bfvc-pass-es-continuation-p
       map1 index)))))

;; The final edge scan either exposes a reachable negative cycle or preserves
;; inv2 while strictly decreasing the remaining finite edge set.

(defun-sk bfvc-negative-cycle-exists-p ()
  (exists (vertex)
    (and
     (bfvc-vertex-p vertex)
     (bfvc-negative-cycle-p vertex))))

(defun bfvc-final-edge-conclusion-p
  (map es1 es2)
  (let* ((edge (bfvc-choose es1))
         (left (bfvc-edge-left edge))
         (right (bfvc-edge-right edge))
         (right-distance
          (bfvc-contents map right))
         (left-distance
          (bfvc-contents map left)))
    (implies
     (equal right-distance
            (bfvc-contents map right))
     (implies
      (equal left-distance
             (bfvc-contents map left))
      (if
       (bfvc-intinf-lt-p
        (bfvc-intinf-add
         left-distance
         (bfvc-finite
          (bfvc-weight left right)))
        right-distance)
       (bfvc-negative-cycle-exists-p)
       (and
        (<= 0 (len (bfvc-to-fset es1)))
        (< (len (bfvc-to-fset es2))
           (len (bfvc-to-fset es1)))
        (bfvc-edge-subset-p
         (bfvc-to-fset es2)
         (bfvc-edges))
        (bfvc-inv2-p
         map
         (bfvc-edge-difference
          (bfvc-edges)
          (bfvc-to-fset es2)))))))))

(defun-sk bfvc-final-nonempty-continuation-p (map es1)
  (forall (es2)
    (implies
     (bfvc-set-p es2)
     (implies
      (and
       (member-equal
        (bfvc-choose es1)
        (bfvc-to-fset es1))
       (bfvc-edge-set-equal-p
        (bfvc-to-fset es2)
        (bfvc-edge-remove
         (bfvc-choose es1)
         (bfvc-to-fset es1))))
      (bfvc-final-edge-conclusion-p
       map es1 es2)))))

(defun-sk bfvc-final-finite-certificate-p
  (vertex value)
  (exists (path)
    (and
     (bfvc-vertex-list-p path)
     (bfvc-path-p
      (bfvc-source)
      path
      vertex)
     (equal
      (bfvc-path-weight path vertex)
      value))))

(defun-sk bfvc-final-finite-minimal-p
  (vertex value)
  (forall (path)
    (implies
     (bfvc-vertex-list-p path)
     (implies
      (bfvc-path-p
       (bfvc-source)
       path
       vertex)
      (<= value
          (bfvc-path-weight
           path vertex))))))

(defun-sk bfvc-final-infinite-unreachable-p (vertex)
  (forall (path)
    (implies
     (bfvc-vertex-list-p path)
     (not
      (bfvc-path-p
       (bfvc-source)
       path
       vertex)))))

(defun bfvc-final-vertex-conclusion-p (map vertex)
  (let ((distance
         (bfvc-contents map vertex)))
    (if (bfvc-finite-p distance)
        (let ((value (cadr distance)))
          (and
           (bfvc-final-finite-certificate-p
            vertex value)
           (bfvc-final-finite-minimal-p
            vertex value)))
      (bfvc-final-infinite-unreachable-p
       vertex))))

(defun-sk bfvc-final-distance-correct-p (map)
  (forall (vertex)
    (implies
     (bfvc-vertex-p vertex)
     (implies
      (member-equal
       vertex
       (bfvc-vertices))
      (bfvc-final-vertex-conclusion-p
       map vertex)))))

(defun bfvc-final-es1-conclusion-p (map es1)
  (if (not (equal (bfvc-to-fset es1) nil))
      (and
       (not (equal (bfvc-to-fset es1) nil))
       (bfvc-final-nonempty-continuation-p
        map es1))
    (bfvc-final-distance-correct-p map)))

(defun-sk bfvc-final-es1-continuation-p (map)
  (forall (es1)
    (implies
     (bfvc-set-p es1)
     (implies
      (and
       (bfvc-edge-subset-p
        (bfvc-to-fset es1)
        (bfvc-edges))
       (bfvc-inv2-p
        map
        (bfvc-edge-difference
         (bfvc-edges)
         (bfvc-to-fset es1))))
      (bfvc-final-es1-conclusion-p
       map es1)))))

(defun bfvc-final-es-conclusion-p (map es)
  (and
   (bfvc-edge-subset-p
    (bfvc-to-fset es)
    (bfvc-edges))
   (bfvc-inv2-p
    map
    (bfvc-edge-difference
     (bfvc-edges)
     (bfvc-to-fset es)))
   (bfvc-final-es1-continuation-p map)))

(defun-sk bfvc-final-es-continuation-p (map)
  (forall (es)
    (implies
     (bfvc-set-p es)
     (implies
      (bfvc-edge-set-equal-p
       (bfvc-to-fset es)
       (bfvc-edges))
      (bfvc-final-es-conclusion-p
       map es)))))

(defun bfvc-map1-conclusion-p (map1 upper)
  (and
   (bfvc-pass-index-continuation-p
    map1 upper)
   (implies
    (bfvc-inv1-p
     map1
     (+ upper 1)
     nil)
    (bfvc-final-es-continuation-p
     map1))))

(defun-sk bfvc-map1-continuation-p (upper)
  (forall (map1)
    (implies
     (bfvc-map-p map1)
     (bfvc-map1-conclusion-p
      map1 upper))))

(defun bfvc-main-vc-p ()
  (let* ((map
          (bfvc-map-update
           (bfvc-create :infinite)
           (bfvc-source)
           (bfvc-finite 0)))
         (upper
          (- (len (bfvc-vertices)) 1)))
    (and
     (implies
      (<= 1 (+ upper 1))
      (and
       (bfvc-inv1-p map 1 nil)
       (bfvc-map1-continuation-p upper)))
     (implies
      (< (+ upper 1) 1)
      (bfvc-final-es-continuation-p
       map)))))

(defun ntp4vc-pearl-bellman-ford-bellman-fordqtvc-statement ()
  (implies
   (bfvc-background-p)
   (bfvc-main-vc-p)))

(value-triple :itpeval-statement-checked)
:q
