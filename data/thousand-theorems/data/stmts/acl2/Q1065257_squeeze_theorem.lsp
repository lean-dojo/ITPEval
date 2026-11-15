;; Statement-only formalization of thousand-theorems corpus artifact Q1065257,
;; "Squeeze theorem": in an arbitrary preordered space with its order topology,
;; two functions converging along a filter to the same point squeeze any
;; eventually intermediate function to that point. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The stubs are conservative evaluators for arbitrary carrier predicates,
;; preorder relations, maps, and filter membership. Sets needed by the
;; statement are represented by symbolic expressions whose membership is
;; defined below. They include the full set, finite intersections, strict
;; order preimages, and pointwise non-strict order bounds.
;;
;; Restricting a source filter to these expressions preserves every predicate
;; occurring in the theorem. Conversely, the upward closure of the represented
;; large sets is a filter on the full powerset and agrees with the represented
;; filter on every expression. Thus this is a bidirectionally equivalent
;; definitional presentation, not a finite or executable approximation.
;;
;; Convergence is expressed using all strict lower and upper order intervals.
;; For a preorder equipped with its order topology, this is equivalent to
;; Tendsto into the neighborhood filter.

(defstub q1065257-domain-p (domain x) t)
(defstub q1065257-codomain-p (codomain x) t)
(defstub q1065257-le (codomain order left right) t)
(defstub q1065257-map-value
  (domain codomain map x)
  t)
(defstub q1065257-large-p
  (domain codomain order filter set-expression)
  t)

(defun q1065257-lt-p
    (codomain order left right)
  (and
   (q1065257-le codomain order left right)
   (not
    (q1065257-le codomain order right left))))

(defun-sk q1065257-preorder-p (codomain order)
  (forall (x y z)
    (and
     (implies
      (q1065257-codomain-p codomain x)
      (q1065257-le codomain order x x))
     (implies
      (and
       (q1065257-codomain-p codomain x)
       (q1065257-codomain-p codomain y)
       (q1065257-codomain-p codomain z)
       (q1065257-le codomain order x y)
       (q1065257-le codomain order y z))
      (q1065257-le codomain order x z)))))

(defun-sk q1065257-map-typed-p
    (domain codomain map)
  (forall (x)
    (implies
     (q1065257-domain-p domain x)
     (q1065257-codomain-p
      codomain
      (q1065257-map-value
       domain codomain map x)))))

;; Symbolic sets over the source carrier.

(defun q1065257-full-set ()
  (list 'q1065257-full-set))

(defun q1065257-intersection-set (left right)
  (list 'q1065257-intersection-set left right))

(defun q1065257-lower-set (map bound)
  (list 'q1065257-lower-set map bound))

(defun q1065257-upper-set (map bound)
  (list 'q1065257-upper-set map bound))

(defun q1065257-pointwise-le-set (left-map right-map)
  (list
   'q1065257-pointwise-le-set
   left-map
   right-map))

(defun q1065257-set-expression-p (set-expression)
  (declare (xargs :measure (acl2-count set-expression)))
  (cond
   ((and
     (true-listp set-expression)
     (equal (len set-expression) 1)
     (equal
      (car set-expression)
      'q1065257-full-set))
    t)
   ((and
     (true-listp set-expression)
     (equal (len set-expression) 3)
     (equal
      (car set-expression)
      'q1065257-intersection-set))
    (and
     (q1065257-set-expression-p
      (cadr set-expression))
     (q1065257-set-expression-p
      (caddr set-expression))))
   ((and
     (true-listp set-expression)
     (equal (len set-expression) 3)
     (equal
      (car set-expression)
      'q1065257-lower-set))
    t)
   ((and
     (true-listp set-expression)
     (equal (len set-expression) 3)
     (equal
      (car set-expression)
      'q1065257-upper-set))
    t)
   ((and
     (true-listp set-expression)
     (equal (len set-expression) 3)
     (equal
      (car set-expression)
      'q1065257-pointwise-le-set))
    t)
   (t nil)))

(defun q1065257-set-member-p
    (domain codomain order set-expression x)
  (declare (xargs :measure (acl2-count set-expression)))
  (if (not (q1065257-domain-p domain x))
      nil
    (cond
     ((and
       (true-listp set-expression)
       (equal (len set-expression) 1)
       (equal
        (car set-expression)
        'q1065257-full-set))
      t)
     ((and
       (true-listp set-expression)
       (equal (len set-expression) 3)
       (equal
        (car set-expression)
        'q1065257-intersection-set))
      (and
       (q1065257-set-member-p
        domain codomain order
        (cadr set-expression) x)
       (q1065257-set-member-p
        domain codomain order
        (caddr set-expression) x)))
     ((and
       (true-listp set-expression)
       (equal (len set-expression) 3)
       (equal
        (car set-expression)
        'q1065257-lower-set))
      (let ((map (cadr set-expression))
            (bound (caddr set-expression)))
        (and
         (q1065257-codomain-p codomain bound)
         (q1065257-lt-p
          codomain order bound
          (q1065257-map-value
           domain codomain map x)))))
     ((and
       (true-listp set-expression)
       (equal (len set-expression) 3)
       (equal
        (car set-expression)
        'q1065257-upper-set))
      (let ((map (cadr set-expression))
            (bound (caddr set-expression)))
        (and
         (q1065257-codomain-p codomain bound)
         (q1065257-lt-p
          codomain order
          (q1065257-map-value
           domain codomain map x)
          bound))))
     ((and
       (true-listp set-expression)
       (equal (len set-expression) 3)
       (equal
        (car set-expression)
        'q1065257-pointwise-le-set))
      (q1065257-le
       codomain order
       (q1065257-map-value
        domain codomain
        (cadr set-expression) x)
       (q1065257-map-value
        domain codomain
        (caddr set-expression) x)))
     (t nil))))

(defun-sk q1065257-subset-p
    (domain codomain order left right)
  (forall (x)
    (implies
     (q1065257-set-member-p
      domain codomain order left x)
     (q1065257-set-member-p
      domain codomain order right x))))

(defun-sk q1065257-filter-intersection-closed-p
    (domain codomain order filter)
  (forall (left right)
    (implies
     (and
      (q1065257-set-expression-p left)
      (q1065257-set-expression-p right)
      (q1065257-large-p
       domain codomain order filter left)
      (q1065257-large-p
       domain codomain order filter right))
     (q1065257-large-p
      domain codomain order filter
      (q1065257-intersection-set left right)))))

(defun-sk q1065257-filter-upward-closed-p
    (domain codomain order filter)
  (forall (left right)
    (implies
     (and
      (q1065257-set-expression-p left)
      (q1065257-set-expression-p right)
      (q1065257-large-p
       domain codomain order filter left)
      (q1065257-subset-p
       domain codomain order left right))
     (q1065257-large-p
      domain codomain order filter right))))

(defun q1065257-filter-p
    (domain codomain order filter)
  (and
   (q1065257-large-p
    domain codomain order filter
    (q1065257-full-set))
   (q1065257-filter-intersection-closed-p
    domain codomain order filter)
   (q1065257-filter-upward-closed-p
    domain codomain order filter)))

(defun-sk q1065257-tendsto-order-p
    (domain codomain order filter map limit)
  (forall (bound)
    (and
     (implies
      (and
       (q1065257-codomain-p codomain bound)
       (q1065257-lt-p
        codomain order bound limit))
      (q1065257-large-p
       domain codomain order filter
       (q1065257-lower-set map bound)))
     (implies
      (and
       (q1065257-codomain-p codomain bound)
       (q1065257-lt-p
        codomain order limit bound))
      (q1065257-large-p
       domain codomain order filter
       (q1065257-upper-set map bound))))))

(defun thousand-theorems-q1065257-squeeze-theorem-statement
    (domain codomain order filter f g h limit)
  (implies
   (and
    (q1065257-preorder-p codomain order)
    (q1065257-filter-p
     domain codomain order filter)
    (q1065257-map-typed-p domain codomain f)
    (q1065257-map-typed-p domain codomain g)
    (q1065257-map-typed-p domain codomain h)
    (q1065257-codomain-p codomain limit)
    (q1065257-tendsto-order-p
     domain codomain order filter g limit)
    (q1065257-tendsto-order-p
     domain codomain order filter h limit)
    (q1065257-large-p
     domain codomain order filter
     (q1065257-pointwise-le-set g f))
    (q1065257-large-p
     domain codomain order filter
     (q1065257-pointwise-le-set f h)))
   (q1065257-tendsto-order-p
    domain codomain order filter f limit)))

(value-triple :itpeval-statement-checked)
:q
