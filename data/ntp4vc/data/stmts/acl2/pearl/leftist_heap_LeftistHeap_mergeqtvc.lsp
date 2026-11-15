;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/leftist_heap_LeftistHeap_mergeqtvc: the merge verification condition
;; for ranked leftist heaps over an arbitrary total preorder, preserving size,
;; element multiplicities, and the leftist-heap invariant. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source element type is represented by an arbitrary, potentially
;; infinite carrier. The relation and minimum operation are conservative
;; interfaces; their source typing and laws are explicit statement assumptions.

(defstub lhm-element-p (x) t)
(defstub lhm-le (x y) t)
(defstub lhm-minimum (tree) t)

(defun-sk lhm-element-inhabited-p ()
  (exists (x)
    (lhm-element-p x)))

;; E is NIL. N s l x r is the injective term (s l x . r), with the recursive
;; recognizer enforcing the source's integer rank and element/tree field types.

(defun lhm-node (stored-rank left root right)
  (cons stored-rank
        (cons left
              (cons root right))))

(defun lhm-stored-rank (tree)
  (car tree))

(defun lhm-left (tree)
  (cadr tree))

(defun lhm-root (tree)
  (caddr tree))

(defun lhm-right (tree)
  (cdddr tree))

(defun lhm-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (consp tree)
      (and
       (integerp (lhm-stored-rank tree))
       (consp (cdr tree))
       (consp (cddr tree))
       (lhm-tree-p (lhm-left tree))
       (lhm-element-p (lhm-root tree))
       (lhm-tree-p (lhm-right tree)))
    (equal tree nil)))

(defun lhm-tree-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (consp tree)
      (+ 1
         (lhm-tree-size (lhm-left tree))
         (lhm-tree-size (lhm-right tree)))
    0))

(defun lhm-occ (element tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (consp tree)
      (+ (if (equal element (lhm-root tree)) 1 0)
         (lhm-occ element (lhm-left tree))
         (lhm-occ element (lhm-right tree)))
    0))

(defun lhm-le-root-p (element tree)
  (if (consp tree)
      (lhm-le element (lhm-root tree))
    t))

(defun lhm-is-heap-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (consp tree)
      (and
       (lhm-le-root-p (lhm-root tree) (lhm-left tree))
       (lhm-is-heap-p (lhm-left tree))
       (lhm-le-root-p (lhm-root tree) (lhm-right tree))
       (lhm-is-heap-p (lhm-right tree)))
    t))

(defun lhm-int-min (left right)
  (if (<= left right) left right))

(defun lhm-rank (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (consp tree)
      (+ 1
         (lhm-int-min
          (lhm-rank (lhm-left tree))
          (lhm-rank (lhm-right tree))))
    0))

(defun lhm-leftist-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (consp tree)
      (and
       (equal (lhm-stored-rank tree)
              (lhm-rank tree))
       (lhm-leftist-p (lhm-left tree))
       (lhm-leftist-p (lhm-right tree))
       (<= (lhm-rank (lhm-right tree))
           (lhm-rank (lhm-left tree))))
    t))

(defun lhm-leftist-heap-p (tree)
  (and
   (lhm-is-heap-p tree)
   (lhm-leftist-p tree)))

;; Explicit universal closures of the source's carrier, preorder, and minimum
;; assumptions.

(defun-sk lhm-minimum-typing-p ()
  (forall (tree)
    (implies
     (lhm-tree-p tree)
     (lhm-element-p (lhm-minimum tree)))))

(defun-sk lhm-minimum-definition-p ()
  (forall (stored-rank left root right)
    (implies
     (and
      (integerp stored-rank)
      (lhm-tree-p left)
      (lhm-element-p root)
      (lhm-tree-p right))
     (equal
      (lhm-minimum
       (lhm-node stored-rank left root right))
      root))))

(defun-sk lhm-le-reflexive-p ()
  (forall (x)
    (implies
     (lhm-element-p x)
     (lhm-le x x))))

(defun-sk lhm-le-transitive-p ()
  (forall (x y z)
    (implies
     (and
      (lhm-element-p x)
      (lhm-element-p y)
      (lhm-element-p z)
      (lhm-le x y)
      (lhm-le y z))
     (lhm-le x z))))

(defun-sk lhm-le-total-p ()
  (forall (x y)
    (implies
     (and
      (lhm-element-p x)
      (lhm-element-p y))
     (or
      (lhm-le x y)
      (lhm-le y x)))))

(defun lhm-structure-assumptions-p ()
  (and
   (lhm-element-inhabited-p)
   (lhm-minimum-typing-p)
   (lhm-minimum-definition-p)
   (lhm-le-reflexive-p)
   (lhm-le-transitive-p)
   (lhm-le-total-p)))

;; Universal element-multiplicity equality used throughout the VC.

(defun-sk lhm-occ-sum-p (output left right)
  (forall (element)
    (implies
     (lhm-element-p element)
     (equal
      (lhm-occ element output)
      (+ (lhm-occ element left)
         (lhm-occ element right))))))

;; These predicates preserve the two universally quantified recursive-call
;; obligations in the first conjunct of the source verification condition.

(defun-sk lhm-left-recursive-obligation-p
    (heap2 left1 root1 right1)
  (forall (output1)
    (implies
     (and
      (lhm-tree-p output1)
      (equal
       (lhm-tree-size output1)
       (+ (lhm-tree-size right1)
          (lhm-tree-size heap2)))
      (lhm-occ-sum-p output1 right1 heap2)
      (lhm-leftist-heap-p output1))
     (and
      (lhm-leftist-heap-p output1)
      (lhm-leftist-heap-p left1)
      (lhm-le-root-p root1 left1)
      (lhm-le-root-p root1 output1)))))

(defun-sk lhm-right-recursive-obligation-p
    (heap1 left2 root2 right2)
  (forall (output1)
    (implies
     (and
      (lhm-tree-p output1)
      (equal
       (lhm-tree-size output1)
       (+ (lhm-tree-size heap1)
          (lhm-tree-size right2)))
      (lhm-occ-sum-p output1 heap1 right2)
      (lhm-leftist-heap-p output1))
     (and
      (lhm-leftist-heap-p output1)
      (lhm-leftist-heap-p left2)
      (lhm-le-root-p root2 left2)
      (lhm-le-root-p root2 output1)))))

(defun lhm-recursive-obligations-p (heap1 heap2)
  (if (equal heap2 nil)
      t
    (if (equal heap1 nil)
        t
      (let ((left1 (lhm-left heap1))
            (root1 (lhm-root heap1))
            (right1 (lhm-right heap1))
            (left2 (lhm-left heap2))
            (root2 (lhm-root heap2))
            (right2 (lhm-right heap2)))
        (if (lhm-le root1 root2)
            (and
             (<= 0
                 (+ (lhm-tree-size heap1)
                    (lhm-tree-size heap2)))
             (< (+ (lhm-tree-size right1)
                   (lhm-tree-size heap2))
                (+ (lhm-tree-size heap1)
                   (lhm-tree-size heap2)))
             (lhm-leftist-heap-p right1)
             (lhm-leftist-heap-p heap2)
             (lhm-left-recursive-obligation-p
              heap2 left1 root1 right1))
          (and
           (<= 0
               (+ (lhm-tree-size heap1)
                  (lhm-tree-size heap2)))
           (< (+ (lhm-tree-size heap1)
                 (lhm-tree-size right2))
              (+ (lhm-tree-size heap1)
                 (lhm-tree-size heap2)))
           (lhm-leftist-heap-p heap1)
           (lhm-leftist-heap-p right2)
           (lhm-right-recursive-obligation-p
            heap1 left2 root2 right2)))))))

;; The branch-specific universal clause for elements other than the chosen
;; root remains inside each existential output specification.

(defun-sk lhm-other-occ-sum-p
    (result distinguished left output1)
  (forall (element)
    (implies
     (and
      (lhm-element-p element)
      (not (equal distinguished element)))
     (equal
      (lhm-occ element result)
      (+ (lhm-occ element left)
         (lhm-occ element output1))))))

(defun-sk lhm-left-output-condition-p
    (heap2 left1 root1 right1 result)
  (exists (output1)
    (and
     (lhm-tree-p output1)
     (equal
      (lhm-tree-size output1)
      (+ (lhm-tree-size right1)
         (lhm-tree-size heap2)))
     (lhm-occ-sum-p output1 right1 heap2)
     (lhm-leftist-heap-p output1)
     (lhm-leftist-heap-p result)
     (equal (lhm-minimum result) root1)
     (equal
      (lhm-tree-size result)
      (+ 1
         (lhm-tree-size left1)
         (lhm-tree-size output1)))
     (equal
      (lhm-occ root1 result)
      (+ 1
         (lhm-occ root1 left1)
         (lhm-occ root1 output1)))
     (lhm-other-occ-sum-p
      result root1 left1 output1))))

(defun-sk lhm-right-output-condition-p
    (heap1 left2 root2 right2 result)
  (exists (output1)
    (and
     (lhm-tree-p output1)
     (equal
      (lhm-tree-size output1)
      (+ (lhm-tree-size heap1)
         (lhm-tree-size right2)))
     (lhm-occ-sum-p output1 heap1 right2)
     (lhm-leftist-heap-p output1)
     (lhm-leftist-heap-p result)
     (equal (lhm-minimum result) root2)
     (equal
      (lhm-tree-size result)
      (+ 1
         (lhm-tree-size left2)
         (lhm-tree-size output1)))
     (equal
      (lhm-occ root2 result)
      (+ 1
         (lhm-occ root2 left2)
         (lhm-occ root2 output1)))
     (lhm-other-occ-sum-p
      result root2 left2 output1))))

(defun lhm-output-condition-p (heap1 heap2 result)
  (if (equal heap2 nil)
      (equal result heap1)
    (if (equal heap1 nil)
        (equal result heap2)
      (let ((left1 (lhm-left heap1))
            (root1 (lhm-root heap1))
            (right1 (lhm-right heap1))
            (left2 (lhm-left heap2))
            (root2 (lhm-root heap2))
            (right2 (lhm-right heap2)))
        (if (lhm-le root1 root2)
            (lhm-left-output-condition-p
             heap2 left1 root1 right1 result)
          (lhm-right-output-condition-p
           heap1 left2 root2 right2 result))))))

;; This is the source's universal result implication, including its exact size,
;; multiplicity, and leftist-heap conclusion.

(defun-sk lhm-result-closure-p (heap1 heap2)
  (forall (result)
    (implies
     (lhm-tree-p result)
     (implies
      (lhm-output-condition-p heap1 heap2 result)
      (and
       (equal
        (lhm-tree-size result)
        (+ (lhm-tree-size heap1)
           (lhm-tree-size heap2)))
       (lhm-occ-sum-p result heap1 heap2)
       (lhm-leftist-heap-p result))))))

(defun-sk lhm-all-heap-pairs-vc-p ()
  (forall (heap1 heap2)
    (implies
     (and
      (lhm-tree-p heap1)
      (lhm-tree-p heap2)
      (lhm-leftist-heap-p heap1)
      (lhm-leftist-heap-p heap2))
     (and
      (lhm-recursive-obligations-p heap1 heap2)
      (lhm-result-closure-p heap1 heap2)))))

(defun leftist-heap-merge-vc-statement ()
  (implies
   (lhm-structure-assumptions-p)
   (lhm-all-heap-pairs-vc-p)))

(value-triple :itpeval-statement-checked)
:q
