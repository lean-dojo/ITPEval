;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/binomial_heap_BinomialHeap_extract_minqtvc: the extraction
;; verification condition for a minimum element of a nonempty binomial heap,
;; preserving heap, rank-order, and occurrence invariants.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source element type is represented by ACL2's full object universe.
;; This conservative interface is its arbitrary total preorder relation.

(defstub bhem-le-op (left right) t)

(defun bhem-le-p (left right)
  (if (bhem-le-op left right) t nil))

(defun-sk bhem-order-laws-p ()
  (forall (x y z)
    (and
     (bhem-le-p x x)
     (implies
      (and
       (bhem-le-p x y)
       (bhem-le-p y z))
      (bhem-le-p x z))
     (or
      (bhem-le-p x y)
      (bhem-le-p y x)))))

;; A source tree is encoded as (element children rank), and a forest is a
;; proper list of such trees.  This recognizer preserves the mutually nested
;; finite tree and forest domains and requires every rank to be an integer.

(defun bhem-well-formed-p (kind object)
  (declare (xargs :measure (acl2-count object)))
  (cond
   ((eq kind :tree)
    (and
     (consp object)
     (consp (cdr object))
     (consp (cddr object))
     (equal (cdddr object) nil)
     (bhem-well-formed-p :forest (cadr object))
     (integerp (caddr object))))
   ((eq kind :forest)
    (if (consp object)
        (and
         (bhem-well-formed-p :tree (car object))
         (bhem-well-formed-p :forest (cdr object)))
      (equal object nil)))
   (t nil)))

(defun bhem-tree-p (tree)
  (bhem-well-formed-p :tree tree))

(defun bhem-forest-p (forest)
  (bhem-well-formed-p :forest forest))

(defun bhem-elem (tree)
  (car tree))

(defun bhem-children (tree)
  (cadr tree))

(defun bhem-rank (tree)
  (caddr tree))

(defun bhem-le-roots-p (element forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      t
    (and
     (bhem-le-p element
                (bhem-elem (car forest)))
     (bhem-le-roots-p element (cdr forest)))))

(defun bhem-heaps-p (forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      t
    (let* ((tree (car forest))
           (children (bhem-children tree)))
      (and
       (bhem-le-roots-p (bhem-elem tree) children)
       (bhem-heaps-p children)
       (bhem-heaps-p (cdr forest))))))

(defun bhem-occ (element forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      0
    (let* ((tree (car forest))
           (children (bhem-children tree)))
      (+
       (if (equal element (bhem-elem tree)) 1 0)
       (bhem-occ element children)
       (bhem-occ element (cdr forest))))))

(defun bhem-has-order-p (rank forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      (equal rank 0)
    (let* ((tree (car forest))
           (next-rank (- rank 1)))
      (and
       (equal (bhem-rank tree) next-rank)
       (bhem-has-order-p next-rank
                         (bhem-children tree))
       (bhem-has-order-p next-rank
                         (cdr forest))))))

(defun bhem-binomial-tree-p (tree)
  (and
   (equal (bhem-rank tree)
          (len (bhem-children tree)))
   (bhem-has-order-p
    (bhem-rank tree)
    (bhem-children tree))))

(defun bhem-inv-p (minimum-rank forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      t
    (let* ((tree (car forest))
           (rank (bhem-rank tree)))
      (and
       (<= minimum-rank rank)
       (bhem-binomial-tree-p tree)
       (bhem-inv-p (+ rank 1)
                   (cdr forest))))))

(defun bhem-reverse (forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      nil
    (append
     (bhem-reverse (cdr forest))
     (list (car forest)))))

;; These predicates preserve the source's elementwise occurrence equalities
;; over the entire arbitrary element domain.

(defun-sk bhem-extraction-occurrences-p
    (forest selected remainder)
  (forall (element)
    (equal
     (bhem-occ element forest)
     (+
      (bhem-occ element (list selected))
      (bhem-occ element remainder)))))

(defun-sk bhem-merge-occurrences-p
    (merged selected remainder)
  (forall (element)
    (equal
     (bhem-occ element merged)
     (+
      (bhem-occ element
                (bhem-reverse
                 (bhem-children selected)))
      (bhem-occ element remainder)))))

(defun-sk bhem-other-occurrences-preserved-p
    (merged original selected)
  (forall (element)
    (implies
     (not (equal element
                 (bhem-elem selected)))
     (equal
      (bhem-occ element merged)
      (bhem-occ element original)))))

(defun bhem-merged-postcondition-p
    (original selected merged)
  (and
   (bhem-heaps-p merged)
   (bhem-inv-p 0 merged)
   (equal
    (bhem-occ (bhem-elem selected) merged)
    (- (bhem-occ (bhem-elem selected) original)
       1))
   (bhem-other-occurrences-preserved-p
    merged original selected)))

(defun-sk bhem-all-merges-p
    (original selected remainder)
  (forall (merged)
    (implies
     (and
      (bhem-forest-p merged)
      (bhem-heaps-p merged)
      (bhem-inv-p 0 merged)
      (bhem-merge-occurrences-p
       merged selected remainder))
     (bhem-merged-postcondition-p
      original selected merged))))

(defun bhem-extraction-postcondition-p
    (original selected remainder)
  (let ((children-reversed
         (bhem-reverse
          (bhem-children selected))))
    (and
     (bhem-heaps-p children-reversed)
     (bhem-inv-p 0 children-reversed)
     (bhem-heaps-p remainder)
     (bhem-inv-p 0 remainder)
     (bhem-all-merges-p
      original selected remainder))))

(defun-sk bhem-all-extractions-p (forest)
  (forall (selected remainder)
    (implies
     (and
      (bhem-tree-p selected)
      (bhem-forest-p remainder)
      (bhem-heaps-p (list selected))
      (bhem-heaps-p remainder)
      (bhem-inv-p 0 remainder)
      (bhem-le-roots-p
       (bhem-elem selected) forest)
      (bhem-binomial-tree-p selected)
      (bhem-extraction-occurrences-p
       forest selected remainder))
     (bhem-extraction-postcondition-p
      forest selected remainder))))

(defun-sk
  ntp4vc-pearl-binomial-heap-binomialheap-extract-minqtvc-statement
  ()
  (forall (forest)
    (implies
     (and
      (bhem-order-laws-p)
      (bhem-forest-p forest)
      (bhem-heaps-p forest)
      (bhem-inv-p 0 forest)
      (not (equal forest nil)))
     (and
      (bhem-heaps-p forest)
      (bhem-inv-p 0 forest)
      (not (equal forest nil))
      (bhem-all-extractions-p forest)))))

(value-triple :itpeval-statement-checked)
:q
