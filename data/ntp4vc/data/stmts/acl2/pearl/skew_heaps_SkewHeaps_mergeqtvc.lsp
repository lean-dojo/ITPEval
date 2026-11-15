;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/skew_heaps_SkewHeaps_mergeqtvc: the skew-heap merge verification
;; condition over an arbitrary total preorder, including recursive-call
;; termination, heap preservation, size, and element multiplicities.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source element type is represented by ACL2's full object universe.
;; This conservative interface leaves its order arbitrary; the total-preorder
;; laws remain explicit assumptions of the statement.

(defstub shm-le-op (left right) t)

(defun shm-le-p (left right)
  (if (shm-le-op left right) t nil))

(defun-sk shm-le-reflexive-p ()
  (forall (element)
    (shm-le-p element element)))

(defun-sk shm-le-transitive-p ()
  (forall (left middle right)
    (implies
     (and
      (shm-le-p left middle)
      (shm-le-p middle right))
     (shm-le-p left right))))

(defun-sk shm-le-total-p ()
  (forall (left right)
    (or
     (shm-le-p left right)
     (shm-le-p right left))))

(defun shm-order-laws-p ()
  (and
   (shm-le-reflexive-p)
   (shm-le-transitive-p)
   (shm-le-total-p)))

;; Empty trees are NIL. Nodes are exact tagged triples
;; (:SKEW-MERGE-NODE left element right), preserving the finite source
;; binary-tree datatype without bounding the element carrier.

(defun shm-node (left element right)
  (list :skew-merge-node left element right))

(defun shm-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :skew-merge-node)))

(defun shm-tree-left (tree)
  (cadr tree))

(defun shm-tree-element (tree)
  (caddr tree))

(defun shm-tree-right (tree)
  (cadddr tree))

(defun shm-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (shm-node-shape-p tree)
     (shm-tree-p (shm-tree-left tree))
     (shm-tree-p (shm-tree-right tree)))))

(defun shm-tree-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (shm-node-shape-p tree)
        (+
         1
         (shm-tree-size (shm-tree-left tree))
         (shm-tree-size (shm-tree-right tree)))
      0)))

(defun shm-tree-occ (element tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (shm-node-shape-p tree)
        (+
         (if (equal element (shm-tree-element tree)) 1 0)
         (shm-tree-occ element (shm-tree-left tree))
         (shm-tree-occ element (shm-tree-right tree)))
      0)))

(defun shm-le-root-p (element tree)
  (if (equal tree nil)
      t
    (if (shm-node-shape-p tree)
        (shm-le-p element (shm-tree-element tree))
      nil)))

(defun shm-heap-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (if (shm-node-shape-p tree)
        (let ((left (shm-tree-left tree))
              (element (shm-tree-element tree))
              (right (shm-tree-right tree)))
          (and
           (shm-le-root-p element left)
           (shm-heap-p left)
           (shm-le-root-p element right)
           (shm-heap-p right)))
      nil)))

;; Extensional occurrence equality over the complete abstract element domain.

(defun-sk shm-occ-sum-p (output left right)
  (forall (element)
    (equal
     (shm-tree-occ element output)
     (+
      (shm-tree-occ element left)
      (shm-tree-occ element right)))))

;; The first conjunct of the Why3 VC: in a nonempty/nonempty branch, the
;; selected recursive call decreases the size variant and receives heaps.

(defun shm-recursive-obligations-p (tree1 tree2)
  (if (equal tree2 nil)
      t
    (if (equal tree1 nil)
        t
      (let ((root1 (shm-tree-element tree1))
            (right1 (shm-tree-right tree1))
            (right2 (shm-tree-right tree2))
            (root2 (shm-tree-element tree2)))
        (if (shm-le-p root1 root2)
            (and
             (<= 0
                 (+ (shm-tree-size tree1)
                    (shm-tree-size tree2)))
             (< (+ (shm-tree-size right1)
                   (shm-tree-size tree2))
                (+ (shm-tree-size tree1)
                   (shm-tree-size tree2)))
             (shm-heap-p right1)
             (shm-heap-p tree2))
          (and
           (<= 0
               (+ (shm-tree-size tree1)
                  (shm-tree-size tree2)))
           (< (+ (shm-tree-size right2)
                 (shm-tree-size tree1))
              (+ (shm-tree-size tree1)
                 (shm-tree-size tree2)))
           (shm-heap-p right2)
           (shm-heap-p tree1)))))))

;; The recursive merge output remains internally existential, exactly as in
;; each nonempty branch of the source result premise.

(defun-sk shm-left-result-premise-p
    (left1 root1 right1 tree2 result)
  (exists (recursive-result)
    (and
     (shm-tree-p recursive-result)
     (shm-heap-p recursive-result)
     (shm-occ-sum-p recursive-result right1 tree2)
     (equal
      (shm-tree-size recursive-result)
      (+ (shm-tree-size right1)
         (shm-tree-size tree2)))
     (equal
      result
      (shm-node recursive-result root1 left1)))))

(defun-sk shm-right-result-premise-p
    (tree1 left2 root2 right2 result)
  (exists (recursive-result)
    (and
     (shm-tree-p recursive-result)
     (shm-heap-p recursive-result)
     (shm-occ-sum-p recursive-result right2 tree1)
     (equal
      (shm-tree-size recursive-result)
      (+ (shm-tree-size right2)
         (shm-tree-size tree1)))
     (equal
      result
      (shm-node recursive-result root2 left2)))))

(defun shm-result-premise-p (tree1 tree2 result)
  (if (equal tree2 nil)
      (if (equal tree1 nil)
          (equal result tree2)
        (equal result tree1))
    (if (equal tree1 nil)
        (equal result tree2)
      (let ((left1 (shm-tree-left tree1))
            (root1 (shm-tree-element tree1))
            (right1 (shm-tree-right tree1))
            (left2 (shm-tree-left tree2))
            (root2 (shm-tree-element tree2))
            (right2 (shm-tree-right tree2)))
        (if (shm-le-p root1 root2)
            (shm-left-result-premise-p
             left1 root1 right1 tree2 result)
          (shm-right-result-premise-p
           tree1 left2 root2 right2 result))))))

;; The second conjunct preserves the source universal quantifier over every
;; typed result satisfying the branch-specific merge relation.

(defun-sk shm-result-closure-p (tree1 tree2)
  (forall (result)
    (implies
     (shm-tree-p result)
     (implies
      (shm-result-premise-p tree1 tree2 result)
      (and
       (shm-heap-p result)
       (shm-occ-sum-p result tree1 tree2)
       (equal
        (shm-tree-size result)
        (+ (shm-tree-size tree1)
           (shm-tree-size tree2))))))))

(defun-sk shm-all-heap-pairs-vc-p ()
  (forall (tree1 tree2)
    (implies
     (and
      (shm-tree-p tree1)
      (shm-tree-p tree2)
      (shm-heap-p tree1)
      (shm-heap-p tree2))
     (and
      (shm-recursive-obligations-p tree1 tree2)
      (shm-result-closure-p tree1 tree2)))))

(defun ntp4vc-pearl-skew-heaps-skewheaps-mergeqtvc-statement ()
  (implies
   (shm-order-laws-p)
   (shm-all-heap-pairs-vc-p)))

(value-triple :itpeval-statement-checked)
:q
