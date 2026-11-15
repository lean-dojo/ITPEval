;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/foveoos11_challenge2_MaximumTree_maximumqtvc: the verification
;; condition for recursively computing the maximum integer in a nonempty
;; binary tree, including recursive-call and result obligations.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Empty trees are NIL. Nodes are exact records
;; (:MAXIMUM-TREE-NODE left value right), where VALUE is an integer. This
;; preserves the source's finite inductive binary-tree domain over integers.

(defun fmt-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :maximum-tree-node)
   (integerp (caddr tree))))

(defun fmt-tree-left (tree)
  (cadr tree))

(defun fmt-tree-value (tree)
  (caddr tree))

(defun fmt-tree-right (tree)
  (cadddr tree))

(defun fmt-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (fmt-node-shape-p tree)
     (fmt-tree-p (fmt-tree-left tree))
     (fmt-tree-p (fmt-tree-right tree)))))

(defun fmt-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (fmt-node-shape-p tree)
        (+
         1
         (fmt-size (fmt-tree-left tree))
         (fmt-size (fmt-tree-right tree)))
      0)))

(defun fmt-member-p (value tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      nil
    (if (fmt-node-shape-p tree)
        (or
         (fmt-member-p value (fmt-tree-left tree))
         (equal value (fmt-tree-value tree))
         (fmt-member-p value (fmt-tree-right tree)))
      nil)))

(defun fmt-integer-max (left right)
  (if (<= left right)
      right
    left))

;; CANDIDATE is an upper bound for every integer occurring in TREE.

(defun-sk fmt-upper-bound-p (candidate tree)
  (forall (value)
    (implies
     (integerp value)
     (implies
      (fmt-member-p value tree)
      (<= value candidate)))))

(defun fmt-maximum-element-p (candidate tree)
  (and
   (integerp candidate)
   (fmt-member-p candidate tree)
   (fmt-upper-bound-p candidate tree)))

;; This is the source termination/nonemptiness obligation for a recursive
;; call on SUBTREE.

(defun fmt-recursive-call-obligation-p (tree subtree)
  (and
   (and
    (<= 0 (fmt-size tree))
    (< (fmt-size subtree) (fmt-size tree)))
   (not (equal subtree nil))))

;; In the two-nonempty-child branch, the left recursive-call obligation is
;; conditional on every possible maximum returned from the right subtree.

(defun-sk fmt-left-call-obligation-p (tree left right)
  (forall (o1)
    (implies
     (integerp o1)
     (implies
      (fmt-maximum-element-p o1 right)
      (fmt-recursive-call-obligation-p tree left)))))

;; This reproduces the theorem's first ordered match on TREE.

(defun fmt-structural-obligations-p (tree)
  (if (equal tree nil)
      nil
    (let ((left (fmt-tree-left tree))
          (right (fmt-tree-right tree)))
      (if (equal left nil)
          (if (equal right nil)
              t
            (fmt-recursive-call-obligation-p tree right))
        (if (equal right nil)
            (fmt-recursive-call-obligation-p tree left)
          (and
           (fmt-recursive-call-obligation-p tree right)
           (fmt-left-call-obligation-p
            tree left right)))))))

;; The existential maximum witness remains internal to each one-subtree
;; result branch.

(defun-sk fmt-one-subtree-result-premise-p
    (subtree root-value result)
  (exists (o1)
    (and
     (fmt-maximum-element-p o1 subtree)
     (equal
      result
      (fmt-integer-max o1 root-value)))))

;; The source's nested right-then-left existential witnesses are equivalently
;; represented by a joint existential pair with the same dependent body.

(defun-sk fmt-two-subtree-result-premise-p
    (left root-value right result)
  (exists (o1 o2)
    (and
     (fmt-maximum-element-p o1 right)
     (fmt-maximum-element-p o2 left)
     (equal
      result
      (fmt-integer-max
       o2
       (fmt-integer-max root-value o1))))))

;; This reproduces the theorem's second ordered match on TREE.

(defun fmt-result-premise-p (tree result)
  (if (equal tree nil)
      nil
    (let ((left (fmt-tree-left tree))
          (root-value (fmt-tree-value tree))
          (right (fmt-tree-right tree)))
      (if (equal left nil)
          (if (equal right nil)
              (equal result root-value)
            (fmt-one-subtree-result-premise-p
             right root-value result))
        (if (equal right nil)
            (fmt-one-subtree-result-premise-p
             left root-value result)
          (fmt-two-subtree-result-premise-p
           left root-value right result))))))

;; RESULT and the elements compared with it retain their source universal
;; quantifiers over all mathematical integers.

(defun-sk fmt-all-results-correct-p (tree)
  (forall (result)
    (implies
     (integerp result)
     (implies
      (fmt-result-premise-p tree result)
      (and
       (fmt-member-p result tree)
       (fmt-upper-bound-p result tree))))))

(defun-sk
  ntp4vc-pearl-foveoos11-challenge2-maximumtree-maximumqtvc-statement
  ()
  (forall (tree)
    (implies
     (and
      (fmt-tree-p tree)
      (not (equal tree nil)))
     (and
      (fmt-structural-obligations-p tree)
      (fmt-all-results-correct-p tree)))))

(value-triple :itpeval-statement-checked)
:q
