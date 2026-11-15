;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/binomial_heap_BinomialHeap_get_minqtvc: the get-min verification
;; condition for a nonempty heap-ordered forest, propagating a recursively
;; selected minimum to a minimum of the whole forest.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source element type is represented by ACL2's full object universe.
;; This conservative interface supplies its arbitrary order relation; the
;; preorder laws remain explicit assumptions of the statement.

(defstub bhgm-le-op (left right) t)

(defun bhgm-le-p (left right)
  (if (bhgm-le-op left right) t nil))

(defun-sk bhgm-reflexive-p ()
  (forall (x)
    (bhgm-le-p x x)))

(defun-sk bhgm-transitive-p ()
  (forall (x y z)
    (implies
     (and
      (bhgm-le-p x y)
      (bhgm-le-p y z))
     (bhgm-le-p x z))))

(defun-sk bhgm-total-p ()
  (forall (x y)
    (or
     (bhgm-le-p x y)
     (bhgm-le-p y x))))

(defun bhgm-order-laws-p ()
  (and
   (bhgm-reflexive-p)
   (bhgm-transitive-p)
   (bhgm-total-p)))

;; A source tree is encoded as (element children rank), and a forest is a
;; proper list of such trees.  The mutually nested recognizer preserves the
;; finite inductive tree/forest domain and the integer-valued rank field.

(defun bhgm-well-formed-p (kind object)
  (declare (xargs :measure (acl2-count object)))
  (cond
   ((eq kind :tree)
    (and
     (consp object)
     (consp (cdr object))
     (consp (cddr object))
     (equal (cdddr object) nil)
     (bhgm-well-formed-p :forest (cadr object))
     (integerp (caddr object))))
   ((eq kind :forest)
    (if (consp object)
        (and
         (bhgm-well-formed-p :tree (car object))
         (bhgm-well-formed-p :forest (cdr object)))
      (equal object nil)))
   (t nil)))

(defun bhgm-forest-p (forest)
  (bhgm-well-formed-p :forest forest))

(defun bhgm-elem (tree)
  (car tree))

(defun bhgm-children (tree)
  (cadr tree))

(defun bhgm-le-roots-p (element forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      t
    (and
     (bhgm-le-p element
                (bhgm-elem (car forest)))
     (bhgm-le-roots-p element (cdr forest)))))

(defun bhgm-heaps-p (forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      t
    (let* ((tree (car forest))
           (children (bhgm-children tree)))
      (and
       (bhgm-le-roots-p (bhgm-elem tree) children)
       (bhgm-heaps-p children)
       (bhgm-heaps-p (cdr forest))))))

(defun bhgm-occ (element forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      0
    (let* ((tree (car forest))
           (children (bhgm-children tree)))
      (+
       (if (equal element (bhgm-elem tree)) 1 0)
       (bhgm-occ element children)
       (bhgm-occ element (cdr forest))))))

(defun bhgm-mem-p (element forest)
  (< 0 (bhgm-occ element forest)))

(defun-sk bhgm-lower-bound-p (minimum forest)
  (forall (element)
    (implies
     (bhgm-mem-p element forest)
     (bhgm-le-p minimum element))))

;; This is the conditional equality used by both nonempty recursive branches.

(defun bhgm-selected-p (selected root minimum)
  (if (bhgm-le-p root minimum)
      (equal selected root)
    (equal selected minimum)))

;; For an empty recursive forest the source match is True.  For a nonempty
;; forest, the inner match identifies its tail with itself definitionally and
;; the remaining obligation is that this tail is heap ordered.

(defun-sk bhgm-recursive-head-case-p (minimum forest)
  (forall (selected)
    (implies
     (consp forest)
     (implies
      (bhgm-selected-p
       selected
       (bhgm-elem (car forest))
       minimum)
      (and
       (equal (cdr forest) (cdr forest))
       (bhgm-heaps-p (cdr forest)))))))

;; The selected element remains an existential witness inside the nonempty
;; recursive-result antecedent, exactly as in the source statement.

(defun-sk bhgm-nonempty-result-antecedent-p
    (minimum forest result)
  (exists (selected)
    (and
     (bhgm-selected-p
      selected
      (bhgm-elem (car forest))
      minimum)
     (or
      (equal result selected)
      (bhgm-mem-p result (cdr forest)))
     (bhgm-le-p result selected)
     (bhgm-lower-bound-p result (cdr forest)))))

(defun bhgm-recursive-result-antecedent-p
    (minimum forest result)
  (if (endp forest)
      (equal result minimum)
    (bhgm-nonempty-result-antecedent-p
     minimum forest result)))

(defun-sk bhgm-all-recursive-results-p (minimum forest)
  (forall (result)
    (implies
     (bhgm-recursive-result-antecedent-p
      minimum forest result)
     (and
      (or
       (equal result minimum)
       (bhgm-mem-p result forest))
      (bhgm-le-p result minimum)
      (bhgm-lower-bound-p result forest)))))

;; This universal predicate is the recursive-call verification condition.
;; Its forest restriction is the target rendering of the source type of l1.

(defun-sk bhgm-recursive-call-vc-p (original-tail)
  (forall (minimum forest)
    (implies
     (bhgm-forest-p forest)
     (implies
      (bhgm-heaps-p forest)
      (and
       (bhgm-recursive-head-case-p minimum forest)
       (bhgm-all-recursive-results-p minimum forest)
       (bhgm-heaps-p original-tail))))))

(defun bhgm-final-result-antecedent-p (forest result)
  (if (endp forest)
      nil
    (let* ((tree (car forest))
           (tail (cdr forest))
           (root (bhgm-elem tree)))
      (and
       (or
        (equal result root)
        (bhgm-mem-p result tail))
       (bhgm-le-p result root)
       (bhgm-lower-bound-p result tail)))))

(defun-sk bhgm-all-final-results-p (forest)
  (forall (result)
    (implies
     (bhgm-final-result-antecedent-p forest result)
     (and
      (bhgm-mem-p result forest)
      (bhgm-lower-bound-p result forest)))))

;; This conditional is the theorem's outer match on the input forest.

(defun bhgm-get-min-vc-p (forest)
  (if (endp forest)
      nil
    (and
     (bhgm-recursive-call-vc-p (cdr forest))
     (bhgm-all-final-results-p forest))))

(defun-sk
  ntp4vc-pearl-binomial-heap-binomialheap-get-minqtvc-statement
  ()
  (forall (forest)
    (implies
     (and
      (bhgm-order-laws-p)
      (bhgm-forest-p forest)
      (bhgm-heaps-p forest)
      (not (equal forest nil)))
     (bhgm-get-min-vc-p forest))))

(value-triple :itpeval-statement-checked)
:q
