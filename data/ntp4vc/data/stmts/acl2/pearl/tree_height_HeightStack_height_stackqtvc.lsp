;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/tree_height_HeightStack_height_stackqtvc: the verification condition
;; for recursive tree-height computation with an explicit stack, including
;; its lexicographic decrease obligations and universal result equation.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Empty trees are NIL. Nodes are exact records
;; (:TREE-HEIGHT-NODE left element right). The element field ranges over
;; ACL2's full object universe, preserving the source's arbitrary labels.

(defun ths-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :tree-height-node)))

(defun ths-tree-left (tree)
  (cadr tree))

(defun ths-tree-right (tree)
  (cadddr tree))

(defun ths-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (ths-node-shape-p tree)
     (ths-tree-p (ths-tree-left tree))
     (ths-tree-p (ths-tree-right tree)))))

(defun ths-tree-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (ths-node-shape-p tree)
        (+
         1
         (ths-tree-size (ths-tree-left tree))
         (ths-tree-size (ths-tree-right tree)))
      0)))

(defun ths-int-max (left right)
  (if (<= left right)
      right
    left))

(defun ths-tree-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (ths-node-shape-p tree)
        (+
         1
         (ths-int-max
          (ths-tree-height (ths-tree-left tree))
          (ths-tree-height (ths-tree-right tree))))
      0)))

;; A source pair (h,t) is represented by the exact record
;; (:TREE-HEIGHT-FRAME h t), and a stack is a proper list of such records.

(defun ths-frame (height tree)
  (list :tree-height-frame height tree))

(defun ths-frame-shape-p (frame)
  (and
   (true-listp frame)
   (equal (len frame) 3)
   (equal (car frame) :tree-height-frame)))

(defun ths-frame-height (frame)
  (cadr frame))

(defun ths-frame-tree (frame)
  (caddr frame))

(defun ths-stack-p (stack)
  (declare (xargs :measure (acl2-count stack)))
  (if (consp stack)
      (and
       (ths-frame-shape-p (car stack))
       (integerp (ths-frame-height (car stack)))
       (ths-tree-p (ths-frame-tree (car stack)))
       (ths-stack-p (cdr stack)))
    (equal stack nil)))

(defun ths-heights (stack)
  (declare (xargs :measure (acl2-count stack)))
  (if (consp stack)
      (let ((frame (car stack)))
        (ths-int-max
         (+
          (ths-frame-height frame)
          (ths-tree-height (ths-frame-tree frame)))
         (ths-heights (cdr stack))))
    0))

(defun ths-sizes (stack)
  (declare (xargs :measure (acl2-count stack)))
  (if (consp stack)
      (+
       (ths-tree-size (ths-frame-tree (car stack)))
       (ths-sizes (cdr stack)))
    0))

;; This is the source lexicographic variant comparison
;; (SIZES STACK, STACK) > (SIZES NEXT, NEXT).

(defun ths-source-tail-equals-p (stack target)
  (if (consp stack)
      (equal (cdr stack) target)
    nil))

(defun ths-variant-decreases-p (stack next)
  (or
   (and
    (<= 0 (ths-sizes stack))
    (< (ths-sizes next)
       (ths-sizes stack)))
   (and
    (equal (ths-sizes stack)
           (ths-sizes next))
    (ths-source-tail-equals-p stack next))))

;; This preserves the complete first case expression of the verification
;; condition, including both recursive-call decrease and nonnegativity
;; obligations.

(defun ths-call-obligations-p (m stack)
  (if (consp stack)
      (let* ((frame (car stack))
             (h (ths-frame-height frame))
             (tree (ths-frame-tree frame))
             (rest (cdr stack)))
        (if (equal tree nil)
            (and
             (ths-variant-decreases-p stack rest)
             (<= 0 (ths-int-max m h)))
          (let ((next
                 (cons
                  (ths-frame
                   (+ h 1)
                   (ths-tree-left tree))
                  (cons
                   (ths-frame
                    (+ h 1)
                    (ths-tree-right tree))
                   rest))))
            (and
             (ths-variant-decreases-p stack next)
             (<= 0 m)))))
    t))

;; This is the branch-specific premise that identifies a recursive call's
;; returned integer.

(defun ths-result-premise-p (m stack result)
  (if (consp stack)
      (let* ((frame (car stack))
             (h (ths-frame-height frame))
             (tree (ths-frame-tree frame))
             (rest (cdr stack)))
        (if (equal tree nil)
            (equal
             result
             (ths-int-max
              (ths-int-max m h)
              (ths-heights rest)))
          (let ((next
                 (cons
                  (ths-frame
                   (+ h 1)
                   (ths-tree-left tree))
                  (cons
                   (ths-frame
                    (+ h 1)
                    (ths-tree-right tree))
                   rest))))
            (equal
             result
             (ths-int-max m (ths-heights next))))))
    (equal result m)))

;; RESULT retains its source universal quantifier over all mathematical
;; integers inside the verification condition.

(defun-sk ths-all-results-p (m stack)
  (forall (result)
    (implies
     (and
      (integerp result)
      (ths-result-premise-p m stack result))
     (equal
      result
      (ths-int-max m (ths-heights stack))))))

;; The outer universal quantifiers retain every integer accumulator and every
;; finite stack of integer/tree pairs. The sole hypothesis is the source
;; precondition 0 <= M.

(defun-sk
  ntp4vc-pearl-tree-height-heightstack-height-stackqtvc-statement
  ()
  (forall (m stack)
    (implies
     (and
      (integerp m)
      (ths-stack-p stack)
      (<= 0 m))
     (and
      (ths-call-obligations-p m stack)
      (ths-all-results-p m stack)))))

(value-triple :itpeval-statement-checked)
:q
