;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/tree_height_Iteration_height1qtvc: the verification condition for
;; iterative binary-tree height computation with explicit continuations,
;; including loop-invariant, variant-decrease, and final-result obligations.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Empty trees are NIL. Nodes are exact records
;; (:THI-NODE left element right). The element field ranges over ACL2's full
;; object universe, preserving the source's arbitrary tree labels.

(defun thi-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :thi-node)))

(defun thi-tree-left (tree)
  (cadr tree))

(defun thi-tree-right (tree)
  (cadddr tree))

(defun thi-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (thi-node-shape-p tree)
     (thi-tree-p (thi-tree-left tree))
     (thi-tree-p (thi-tree-right tree)))))

(defun thi-tree-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (thi-node-shape-p tree)
        (+
         1
         (thi-tree-size (thi-tree-left tree))
         (thi-tree-size (thi-tree-right tree)))
      0)))

(defun thi-int-max (left right)
  (if (<= left right)
      right
    left))

(defun thi-tree-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (thi-node-shape-p tree)
        (+
         1
         (thi-int-max
          (thi-tree-height (thi-tree-left tree))
          (thi-tree-height (thi-tree-right tree))))
      0)))

;; The source continuation constructors are represented by :THI-ID and exact
;; records (:THI-KLEFT tree continuation) and
;; (:THI-KRIGHT integer continuation).

(defun thi-kleft (tree continuation)
  (list :thi-kleft tree continuation))

(defun thi-kright (value continuation)
  (list :thi-kright value continuation))

(defun thi-kleft-shape-p (continuation)
  (and
   (true-listp continuation)
   (equal (len continuation) 3)
   (equal (car continuation) :thi-kleft)))

(defun thi-kright-shape-p (continuation)
  (and
   (true-listp continuation)
   (equal (len continuation) 3)
   (equal (car continuation) :thi-kright)))

(defun thi-cont-value (continuation)
  (cadr continuation))

(defun thi-cont-tail (continuation)
  (caddr continuation))

(defun thi-cont-p (continuation)
  (declare (xargs :measure (acl2-count continuation)))
  (cond
   ((equal continuation :thi-id)
    t)
   ((thi-kleft-shape-p continuation)
    (and
     (thi-tree-p (thi-cont-value continuation))
     (thi-cont-p (thi-cont-tail continuation))))
   ((thi-kright-shape-p continuation)
    (and
     (integerp (thi-cont-value continuation))
     (thi-cont-p (thi-cont-tail continuation))))
   (t nil)))

;; Work states are exact records (:THI-ARGUMENT tree) or
;; (:THI-RESULT integer).

(defun thi-argument (tree)
  (list :thi-argument tree))

(defun thi-result (value)
  (list :thi-result value))

(defun thi-argument-shape-p (work)
  (and
   (true-listp work)
   (equal (len work) 2)
   (equal (car work) :thi-argument)))

(defun thi-result-shape-p (work)
  (and
   (true-listp work)
   (equal (len work) 2)
   (equal (car work) :thi-result)))

(defun thi-work-value (work)
  (cadr work))

(defun thi-what-p (work)
  (cond
   ((thi-argument-shape-p work)
    (thi-tree-p (thi-work-value work)))
   ((thi-result-shape-p work)
    (integerp (thi-work-value work)))
   (t nil)))

(defun thi-is-id-p (continuation)
  (equal continuation :thi-id))

(defun thi-is-result-p (work)
  (thi-result-shape-p work))

(defun thi-evalk (continuation result)
  (declare (xargs :measure (acl2-count continuation)))
  (cond
   ((equal continuation :thi-id)
    result)
   ((thi-kleft-shape-p continuation)
    (thi-evalk
     (thi-cont-tail continuation)
     (+
      1
      (thi-int-max
       (thi-tree-height (thi-cont-value continuation))
       result))))
   ((thi-kright-shape-p continuation)
    (thi-evalk
     (thi-cont-tail continuation)
     (+
      1
      (thi-int-max
       (thi-cont-value continuation)
       result))))
   (t 0)))

(defun thi-evalw (work)
  (cond
   ((thi-argument-shape-p work)
    (thi-tree-height (thi-work-value work)))
   ((thi-result-shape-p work)
    (thi-work-value work))
   (t 0)))

(defun thi-sizek (continuation)
  (declare (xargs :measure (acl2-count continuation)))
  (cond
   ((equal continuation :thi-id)
    0)
   ((thi-kleft-shape-p continuation)
    (+
     3
     (* 4 (thi-tree-size (thi-cont-value continuation)))
     (thi-sizek (thi-cont-tail continuation))))
   ((thi-kright-shape-p continuation)
    (+ 1 (thi-sizek (thi-cont-tail continuation))))
   (t 0)))

(defun thi-sizew (work)
  (if (thi-argument-shape-p work)
      (+ 1 (* 4 (thi-tree-size (thi-work-value work))))
    0))

(defun thi-measure (continuation work)
  (+ (thi-sizek continuation)
     (thi-sizew work)))

;; This is the branch shared by every continuation when the current work is
;; an Argument. It preserves the source's nonnegativity, strict variant
;; decrease, and loop-invariant obligations.

(defun thi-argument-step-p (continuation work original-tree)
  (let ((tree (thi-work-value work)))
    (if (equal tree nil)
        (and
         (<= 0 (thi-measure continuation work))
         (<
          (thi-measure continuation (thi-result 0))
          (thi-measure continuation work))
         (equal
          (thi-evalk continuation (thi-evalw (thi-result 0)))
          (thi-tree-height original-tree)))
      (let ((next-continuation
             (thi-kleft (thi-tree-right tree) continuation))
            (next-work
             (thi-argument (thi-tree-left tree))))
        (and
         (<= 0 (thi-measure continuation work))
         (<
          (thi-measure next-continuation next-work)
          (thi-measure continuation work))
         (equal
          (thi-evalk next-continuation (thi-evalw next-work))
          (thi-tree-height original-tree)))))))

(defun thi-nonterminal-branch-p (continuation work original-tree)
  (cond
   ((thi-is-id-p continuation)
    (if (thi-argument-shape-p work)
        (thi-argument-step-p continuation work original-tree)
      nil))
   ((thi-kleft-shape-p continuation)
    (if (thi-argument-shape-p work)
        (thi-argument-step-p continuation work original-tree)
      (let ((next-continuation
             (thi-kright
              (thi-work-value work)
              (thi-cont-tail continuation)))
            (next-work
             (thi-argument (thi-cont-value continuation))))
        (and
         (<= 0 (thi-measure continuation work))
         (<
          (thi-measure next-continuation next-work)
          (thi-measure continuation work))
         (equal
          (thi-evalk next-continuation (thi-evalw next-work))
          (thi-tree-height original-tree))))))
   ((thi-kright-shape-p continuation)
    (if (thi-argument-shape-p work)
        (thi-argument-step-p continuation work original-tree)
      (let ((next-continuation (thi-cont-tail continuation))
            (next-work
             (thi-result
              (+
               1
               (thi-int-max
                (thi-cont-value continuation)
                (thi-work-value work))))))
        (and
         (<= 0 (thi-measure continuation work))
         (<
          (thi-measure next-continuation next-work)
          (thi-measure continuation work))
         (equal
          (thi-evalk next-continuation (thi-evalw next-work))
          (thi-tree-height original-tree))))))
   (t nil)))

(defun thi-final-result-premise-p (work result)
  (if (thi-result-shape-p work)
      (equal result (thi-work-value work))
    nil))

;; RESULT retains its source universal quantifier over all mathematical
;; integers inside the loop-exit branch.

(defun-sk thi-all-final-results-p (work original-tree)
  (forall (result)
    (implies
     (and
      (integerp result)
      (thi-final-result-premise-p work result))
     (equal result (thi-tree-height original-tree)))))

(defun thi-terminal-branch-p (work original-tree)
  (and
   (thi-is-result-p work)
   (thi-all-final-results-p work original-tree)))

;; O1 is the source Boolean introduced by the compiled loop guard. The
;; binding premise and both branches are retained without simplification.

(defun thi-guard-binding-p (continuation work o1)
  (if (thi-is-id-p continuation)
      (equal o1
             (if (thi-is-result-p work) t nil))
    (equal o1 nil)))

(defun-sk thi-all-guard-values-p (continuation work original-tree)
  (forall (o1)
    (implies
     (and
      (booleanp o1)
      (thi-guard-binding-p continuation work o1))
     (if (not (equal o1 t))
         (thi-nonterminal-branch-p
          continuation work original-tree)
       (thi-terminal-branch-p work original-tree)))))

;; CONTINUATION and WORK retain the source universal quantifiers. Their sole
;; premise is the loop invariant evalk k (evalw w) = height t.

(defun-sk thi-all-loop-states-p (original-tree)
  (forall (continuation work)
    (implies
     (and
      (thi-cont-p continuation)
      (thi-what-p work)
      (equal
       (thi-evalk continuation (thi-evalw work))
       (thi-tree-height original-tree)))
     (thi-all-guard-values-p
      continuation work original-tree))))

(defun-sk
  ntp4vc-pearl-tree-height-iteration-height1qtvc-statement
  ()
  (forall (tree)
    (implies
     (thi-tree-p tree)
     (and
      (equal
       (thi-evalk :thi-id (thi-evalw (thi-argument tree)))
       (thi-tree-height tree))
      (thi-all-loop-states-p tree)))))

(value-triple :itpeval-statement-checked)
:q
