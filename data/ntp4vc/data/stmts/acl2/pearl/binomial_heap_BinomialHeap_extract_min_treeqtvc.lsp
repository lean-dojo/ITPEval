;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/binomial_heap_BinomialHeap_extract_min_treeqtvc: the extraction
;; condition for a minimum-root binomial tree from a nonempty ordered forest,
;; preserving heap, rank-order, root-order, and occurrence invariants.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source element type is represented by ACL2's full object universe.
;; This conservative interface is its arbitrary total preorder relation.

(defstub bhemt-le-op (left right) t)

(defun bhemt-le-p (left right)
  (if (bhemt-le-op left right) t nil))

(defun-sk bhemt-order-laws-p ()
  (forall (x y z)
    (and
     (bhemt-le-p x x)
     (implies
      (and
       (bhemt-le-p x y)
       (bhemt-le-p y z))
      (bhemt-le-p x z))
     (or
      (bhemt-le-p x y)
      (bhemt-le-p y x)))))

;; A source tree is encoded as (element children rank), and a forest is a
;; proper list of such trees.  The single recognizer follows both inductive
;; sorts and therefore admits exactly finite source trees and forests.

(defun bhemt-well-formed-p (kind object)
  (declare (xargs :measure (acl2-count object)))
  (cond
   ((eq kind :tree)
    (and
     (consp object)
     (consp (cdr object))
     (consp (cddr object))
     (equal (cdddr object) nil)
     (bhemt-well-formed-p :forest (cadr object))
     (integerp (caddr object))))
   ((eq kind :forest)
    (if (consp object)
        (and
         (bhemt-well-formed-p :tree (car object))
         (bhemt-well-formed-p :forest (cdr object)))
      (equal object nil)))
   (t nil)))

(defun bhemt-tree-p (tree)
  (bhemt-well-formed-p :tree tree))

(defun bhemt-forest-p (forest)
  (bhemt-well-formed-p :forest forest))

(defun bhemt-elem (tree)
  (car tree))

(defun bhemt-children (tree)
  (cadr tree))

(defun bhemt-rank (tree)
  (caddr tree))

(defun bhemt-le-roots-p (element forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      t
    (and
     (bhemt-le-p element
                 (bhemt-elem (car forest)))
     (bhemt-le-roots-p element (cdr forest)))))

(defun bhemt-heaps-p (forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      t
    (let* ((tree (car forest))
           (children (bhemt-children tree)))
      (and
       (bhemt-le-roots-p (bhemt-elem tree) children)
       (bhemt-heaps-p children)
       (bhemt-heaps-p (cdr forest))))))

(defun bhemt-occ (element forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      0
    (let* ((tree (car forest))
           (children (bhemt-children tree)))
      (+
       (if (equal element (bhemt-elem tree)) 1 0)
       (bhemt-occ element children)
       (bhemt-occ element (cdr forest))))))

(defun bhemt-has-order-p (rank forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      (equal rank 0)
    (let* ((tree (car forest))
           (next-rank (- rank 1)))
      (and
       (equal (bhemt-rank tree) next-rank)
       (bhemt-has-order-p next-rank
                          (bhemt-children tree))
       (bhemt-has-order-p next-rank
                          (cdr forest))))))

(defun bhemt-binomial-tree-p (tree)
  (and
   (equal (bhemt-rank tree)
          (len (bhemt-children tree)))
   (bhemt-has-order-p
    (bhemt-rank tree)
    (bhemt-children tree))))

(defun bhemt-inv-p (minimum-rank forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      t
    (let* ((tree (car forest))
           (rank (bhemt-rank tree)))
      (and
       (<= minimum-rank rank)
       (bhemt-binomial-tree-p tree)
       (bhemt-inv-p (+ rank 1)
                    (cdr forest))))))

;; These quantified predicates preserve the source's elementwise occurrence
;; equalities without replacing the arbitrary element domain by a finite list.

(defun-sk bhemt-tail-occurrence-split-p (tail selected remainder)
  (forall (element)
    (equal
     (bhemt-occ element tail)
     (+
      (bhemt-occ element (list selected))
      (bhemt-occ element remainder)))))

(defun-sk bhemt-output-occurrence-split-p (forest selected remainder)
  (forall (element)
    (equal
     (bhemt-occ element forest)
     (+
      (bhemt-occ element (list selected))
      (bhemt-occ element remainder)))))

;; In the multiple-tree branch the recursively extracted tree and remainder
;; remain existential witnesses internal to the branch antecedent.

(defun-sk bhemt-multiple-branch-p
    (first tail selected remainder)
  (exists (recursive-selected recursive-remainder)
    (and
     (bhemt-tree-p recursive-selected)
     (bhemt-forest-p recursive-remainder)
     (bhemt-heaps-p (list recursive-selected))
     (bhemt-heaps-p recursive-remainder)
     (bhemt-inv-p
      (+ (bhemt-rank first) 1)
      recursive-remainder)
     (bhemt-le-roots-p
      (bhemt-elem recursive-selected)
      tail)
     (bhemt-binomial-tree-p recursive-selected)
     (bhemt-tail-occurrence-split-p
      tail recursive-selected recursive-remainder)
     (if (bhemt-le-p
          (bhemt-elem first)
          (bhemt-elem recursive-selected))
         (and
          (equal selected first)
          (equal remainder tail))
       (and
        (equal selected recursive-selected)
        (equal remainder
               (cons first recursive-remainder)))))))

(defun bhemt-extraction-antecedent-p (forest selected remainder)
  (cond
   ((endp forest) nil)
   ((endp (cdr forest))
    (and
     (equal selected (car forest))
     (equal remainder nil)))
   (t
    (bhemt-multiple-branch-p
     (car forest)
     (cdr forest)
     selected
     remainder))))

(defun bhemt-extraction-postcondition-p
    (forest minimum-rank selected remainder)
  (and
   (bhemt-heaps-p (list selected))
   (bhemt-heaps-p remainder)
   (bhemt-inv-p minimum-rank remainder)
   (bhemt-le-roots-p (bhemt-elem selected) forest)
   (bhemt-binomial-tree-p selected)
   (bhemt-output-occurrence-split-p
    forest selected remainder)))

(defun-sk bhemt-all-extractions-p (forest minimum-rank)
  (forall (selected remainder)
    (implies
     (and
      (bhemt-tree-p selected)
      (bhemt-forest-p remainder)
      (bhemt-extraction-antecedent-p
       forest selected remainder))
     (bhemt-extraction-postcondition-p
      forest minimum-rank selected remainder))))

;; This is the source's first match expression.  In the multiple-tree branch,
;; the inner match equality identifies the tail with itself definitionally.

(defun bhemt-head-case-p (forest)
  (cond
   ((endp forest) nil)
   ((endp (cdr forest)) t)
   (t
    (let ((tree (car forest))
          (tail (cdr forest)))
      (and
       (equal (cdr forest) tail)
       (bhemt-heaps-p tail)
       (bhemt-inv-p
        (+ (bhemt-rank tree) 1)
        tail)
       (not (equal tail nil)))))))

(defun-sk
  ntp4vc-pearl-binomial-heap-binomialheap-extract-min-treeqtvc-statement
  ()
  (forall (forest minimum-rank)
    (implies
     (and
      (bhemt-order-laws-p)
      (bhemt-forest-p forest)
      (integerp minimum-rank)
      (bhemt-heaps-p forest)
      (bhemt-inv-p minimum-rank forest)
      (not (equal forest nil)))
     (and
      (bhemt-head-case-p forest)
      (bhemt-all-extractions-p forest minimum-rank)))))

(value-triple :itpeval-statement-checked)
:q
