;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/binomial_heap_BinomialHeap_mergeqtvc: the merge verification
;; condition for two rank-ordered binomial-heap forests, preserving heap,
;; rank-order, and element-occurrence invariants.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source element type is represented by ACL2's full object universe.
;; This conservative interface supplies its arbitrary order relation; its
;; reflexivity, transitivity, and totality remain explicit statement premises.

(defstub bhm-le-op (left right) t)

(defun bhm-le-p (left right)
  (if (bhm-le-op left right) t nil))

(defun-sk bhm-reflexive-p ()
  (forall (x)
    (bhm-le-p x x)))

(defun-sk bhm-transitive-p ()
  (forall (x y z)
    (implies
     (and
      (bhm-le-p x y)
      (bhm-le-p y z))
     (bhm-le-p x z))))

(defun-sk bhm-total-p ()
  (forall (x y)
    (or
     (bhm-le-p x y)
     (bhm-le-p y x))))

(defun bhm-order-laws-p ()
  (and
   (bhm-reflexive-p)
   (bhm-transitive-p)
   (bhm-total-p)))

;; A source tree is encoded as the exact triple (element children rank), and a
;; forest is a proper list of such trees.  The mutually nested recognizer
;; preserves the finite inductive tree/forest domain and integer-valued ranks.

(defun bhm-well-formed-p (kind object)
  (declare (xargs :measure (acl2-count object)))
  (cond
   ((eq kind :tree)
    (and
     (consp object)
     (consp (cdr object))
     (consp (cddr object))
     (equal (cdddr object) nil)
     (bhm-well-formed-p :forest (cadr object))
     (integerp (caddr object))))
   ((eq kind :forest)
    (if (consp object)
        (and
         (bhm-well-formed-p :tree (car object))
         (bhm-well-formed-p :forest (cdr object)))
      (equal object nil)))
   (t nil)))

(defun bhm-forest-p (forest)
  (bhm-well-formed-p :forest forest))

(defun bhm-elem (tree)
  (car tree))

(defun bhm-children (tree)
  (cadr tree))

(defun bhm-rank (tree)
  (caddr tree))

(defun bhm-make-tree (element children rank)
  (list element children rank))

(defun bhm-le-roots-p (element forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      t
    (and
     (bhm-le-p element
               (bhm-elem (car forest)))
     (bhm-le-roots-p element (cdr forest)))))

(defun bhm-heaps-p (forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      t
    (let* ((tree (car forest))
           (children (bhm-children tree)))
      (and
       (bhm-le-roots-p (bhm-elem tree) children)
       (bhm-heaps-p children)
       (bhm-heaps-p (cdr forest))))))

(defun bhm-occ (element forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      0
    (let* ((tree (car forest))
           (children (bhm-children tree)))
      (+
       (if (equal element (bhm-elem tree)) 1 0)
       (bhm-occ element children)
       (bhm-occ element (cdr forest))))))

(defun bhm-has-order-p (rank forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      (equal rank 0)
    (let* ((tree (car forest))
           (next-rank (- rank 1)))
      (and
       (equal (bhm-rank tree) next-rank)
       (bhm-has-order-p next-rank
                        (bhm-children tree))
       (bhm-has-order-p next-rank
                        (cdr forest))))))

(defun bhm-binomial-tree-p (tree)
  (and
   (equal (bhm-rank tree)
          (len (bhm-children tree)))
   (bhm-has-order-p
    (bhm-rank tree)
    (bhm-children tree))))

(defun bhm-inv-p (minimum-rank forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (endp forest)
      t
    (let* ((tree (car forest))
           (rank (bhm-rank tree)))
      (and
       (<= minimum-rank rank)
       (bhm-binomial-tree-p tree)
       (bhm-inv-p (+ rank 1)
                  (cdr forest))))))

(defun bhm-link (tree1 tree2)
  (if (bhm-le-p (bhm-elem tree1)
                (bhm-elem tree2))
      (bhm-make-tree
       (bhm-elem tree1)
       (cons tree2 (bhm-children tree1))
       (+ (bhm-rank tree1) 1))
    (bhm-make-tree
     (bhm-elem tree2)
     (cons tree1 (bhm-children tree2))
     (+ (bhm-rank tree2) 1))))

;; This preserves each source equality quantified over the entire arbitrary
;; element domain.

(defun-sk bhm-occ-sum-p (target left right)
  (forall (element)
    (equal
     (bhm-occ element target)
     (+
      (bhm-occ element left)
      (bhm-occ element right)))))

;; In the equal-rank head branch, the recursively merged forest remains under
;; the source universal quantifier.

(defun-sk bhm-equal-rank-recursive-vc-p
    (tree1 tree2 tail1 tail2 next-rank)
  (forall (merged-tail)
    (implies
     (and
      (bhm-forest-p merged-tail)
      (bhm-heaps-p merged-tail)
      (bhm-inv-p next-rank merged-tail)
      (bhm-occ-sum-p merged-tail tail1 tail2))
     (let ((linked (bhm-link tree1 tree2)))
       (and
        (bhm-heaps-p (list linked))
        (bhm-binomial-tree-p linked)
        (bhm-heaps-p merged-tail)
        (bhm-inv-p
         (bhm-rank linked)
         merged-tail))))))

;; This is the theorem's first match expression, including the source's
;; definitionally true tail equalities.

(defun bhm-head-case-p (forest1 forest2)
  (if (endp forest2)
      t
    (let ((tree2 (car forest2))
          (tail2 (cdr forest2)))
      (if (endp forest1)
          t
        (let* ((tree1 (car forest1))
               (tail1 (cdr forest1))
               (rank1 (bhm-rank tree1))
               (rank2 (bhm-rank tree2)))
          (cond
           ((< rank1 rank2)
            (let ((next-rank (+ rank1 1)))
              (and
               (equal (cdr forest1) tail1)
               (bhm-heaps-p tail1)
               (bhm-inv-p next-rank tail1)
               (bhm-heaps-p forest2)
               (bhm-inv-p next-rank forest2))))
           ((< rank2 rank1)
            (let ((next-rank (+ rank2 1)))
              (and
               (equal (cdr forest2) tail2)
               (bhm-heaps-p forest1)
               (bhm-inv-p next-rank forest1)
               (bhm-heaps-p tail2)
               (bhm-inv-p next-rank tail2))))
           (t
            (let ((next-rank (+ rank1 1)))
              (and
               (or
                (equal (cdr forest1) tail1)
                (and
                 (equal forest1 tail1)
                 (equal (cdr forest2) tail2)))
               (bhm-heaps-p tail1)
               (bhm-inv-p next-rank tail1)
               (bhm-heaps-p tail2)
               (bhm-inv-p next-rank tail2)
               (bhm-equal-rank-recursive-vc-p
                tree1 tree2 tail1 tail2 next-rank))))))))))

;; Each branch below retains the recursive output forest as an internal
;; existential witness, with its source-typed forest restriction explicit.

(defun-sk bhm-left-rank-result-p
    (tree1 tail1 forest2 result)
  (exists (merged-tail)
    (and
     (bhm-forest-p merged-tail)
     (bhm-heaps-p merged-tail)
     (bhm-inv-p
      (+ (bhm-rank tree1) 1)
      merged-tail)
     (bhm-occ-sum-p merged-tail tail1 forest2)
     (equal result
            (cons tree1 merged-tail)))))

(defun-sk bhm-right-rank-result-p
    (forest1 tree2 tail2 result)
  (exists (merged-tail)
    (and
     (bhm-forest-p merged-tail)
     (bhm-heaps-p merged-tail)
     (bhm-inv-p
      (+ (bhm-rank tree2) 1)
      merged-tail)
     (bhm-occ-sum-p merged-tail forest1 tail2)
     (equal result
            (cons tree2 merged-tail)))))

(defun-sk bhm-equal-rank-result-p
    (tree1 tail1 tree2 tail2 result)
  (exists (merged-tail)
    (and
     (bhm-forest-p merged-tail)
     (bhm-heaps-p merged-tail)
     (bhm-inv-p
      (+ (bhm-rank tree1) 1)
      merged-tail)
     (bhm-occ-sum-p merged-tail tail1 tail2)
     (let ((linked (bhm-link tree1 tree2)))
       (and
        (bhm-heaps-p result)
        (bhm-inv-p (bhm-rank linked) result)
        (bhm-occ-sum-p
         result
         (list linked)
         merged-tail))))))

(defun bhm-result-premise-p (forest1 forest2 result)
  (if (endp forest2)
      (if (endp forest1)
          (equal result forest2)
        (equal result forest1))
    (let ((tree2 (car forest2))
          (tail2 (cdr forest2)))
      (if (endp forest1)
          (equal result forest2)
        (let* ((tree1 (car forest1))
               (tail1 (cdr forest1))
               (rank1 (bhm-rank tree1))
               (rank2 (bhm-rank tree2)))
          (cond
           ((< rank1 rank2)
            (bhm-left-rank-result-p
             tree1 tail1 forest2 result))
           ((< rank2 rank1)
            (bhm-right-rank-result-p
             forest1 tree2 tail2 result))
           (t
            (bhm-equal-rank-result-p
             tree1 tail1 tree2 tail2 result))))))))

(defun bhm-result-postcondition-p
    (forest1 minimum-rank forest2 result)
  (and
   (bhm-heaps-p result)
   (bhm-inv-p minimum-rank result)
   (bhm-occ-sum-p result forest1 forest2)))

(defun-sk bhm-all-results-p
    (forest1 minimum-rank forest2)
  (forall (result)
    (implies
     (and
      (bhm-forest-p result)
      (bhm-result-premise-p
       forest1 forest2 result))
     (bhm-result-postcondition-p
      forest1 minimum-rank forest2 result))))

(defun-sk
  ntp4vc-pearl-binomial-heap-binomialheap-mergeqtvc-statement
  ()
  (forall (forest1 minimum-rank forest2)
    (implies
     (and
      (bhm-order-laws-p)
      (bhm-forest-p forest1)
      (integerp minimum-rank)
      (bhm-forest-p forest2)
      (bhm-heaps-p forest1)
      (bhm-inv-p minimum-rank forest1)
      (bhm-heaps-p forest2)
      (bhm-inv-p minimum-rank forest2))
     (and
      (bhm-head-case-p forest1 forest2)
      (bhm-all-results-p
       forest1 minimum-rank forest2)))))

(value-triple :itpeval-statement-checked)
:q
