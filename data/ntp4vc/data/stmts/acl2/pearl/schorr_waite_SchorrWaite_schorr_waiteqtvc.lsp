;; Statement-only formalization of the ntp4vc corpus artifact
;; pearl/schorr_waite_SchorrWaite_schorr_waiteqtvc: the Schorr-Waite graph
;; marking loop verification condition, including finite graph state, stack and
;; path invariants, functional heap updates, loop branches, and variants.  This
;; file contains no proof.

(in-package "ACL2")

; The source type loc is arbitrary and inhabited.
(defstub sw-loc-p (*) => *)
(defstub sw-null () => *)
(defstub sw-default-loc () => *)

; Initial heap and ghost maps.
(defstub sw-left1 (*) => *)
(defstub sw-right1 (*) => *)
(defstub sw-m (*) => *)
(defstub sw-c (*) => *)
(defstub sw-path-from-root (*) => *)

; Universally arbitrary loop-state maps.  ACL2 is first order, so the source
; quantification over function values is represented by these generic,
; conservatively introduced interfaces; all subsequent updates are explicit.
(defstub sw-left2 (*) => *)
(defstub sw-right2 (*) => *)
(defstub sw-m1 (*) => *)
(defstub sw-c1 (*) => *)
(defstub sw-path-from-root1 (*) => *)

(defun sw-loc-list-p (xs)
  (if (consp xs)
      (and (sw-loc-p (car xs))
           (sw-loc-list-p (cdr xs)))
    (equal xs nil)))

; Finite source sets are represented extensionally by duplicate-free lists.
(defun sw-fset-p (xs)
  (if (consp xs)
      (and (sw-loc-p (car xs))
           (not (member-equal (car xs) (cdr xs)))
           (sw-fset-p (cdr xs)))
    (equal xs nil)))

(defun sw-fset-remove (x xs)
  (if (consp xs)
      (if (equal x (car xs))
          (cdr xs)
        (cons (car xs) (sw-fset-remove x (cdr xs))))
    nil))

(defun sw-fset-insert (x xs)
  (if (member-equal x xs)
      xs
    (cons x xs)))

(defun sw-int-to-nat (i)
  (if (and (integerp i) (< i 0))
      0
    (nfix i)))

(defun sw-nth-loc (i xs)
  (if (< (sw-int-to-nat i) (len xs))
      (nth (sw-int-to-nat i) xs)
    (sw-default-loc)))

(defun sw-last-loc (xs)
  (sw-nth-loc (- (len xs) 1) xs))

(defun sw-append-one (xs x)
  (append xs (list x)))

; Selectors faithfully encode the source maps and their single-point updates.
(defun sw-left-at (kind key value x)
  (cond ((equal kind :left1) (sw-left1 x))
        ((equal kind :left2) (sw-left2 x))
        ((equal kind :left2-update)
         (if (equal x key) value (sw-left2 x)))
        (t (sw-default-loc))))

(defun sw-right-at (kind key value x)
  (cond ((equal kind :right1) (sw-right1 x))
        ((equal kind :right2) (sw-right2 x))
        ((equal kind :right2-update)
         (if (equal x key) value (sw-right2 x)))
        (t (sw-default-loc))))

(defun sw-m-at (kind key value x)
  (cond ((equal kind :m) (sw-m x))
        ((equal kind :m1) (sw-m1 x))
        ((equal kind :m1-update)
         (if (equal x key) value (sw-m1 x)))
        (t nil)))

(defun sw-c-at (kind key value x)
  (cond ((equal kind :c) (sw-c x))
        ((equal kind :c1) (sw-c1 x))
        ((equal kind :c1-update)
         (if (equal x key) value (sw-c1 x)))
        (t nil)))

(defun sw-path-at (kind key value x)
  (cond ((equal kind :path) (sw-path-from-root x))
        ((equal kind :path-update)
         (if (equal x key) value (sw-path-from-root x)))
        ((equal kind :path1) (sw-path-from-root1 x))
        ((equal kind :path1-update)
         (if (equal x key) value (sw-path-from-root1 x)))
        (t nil)))

(defun-sk sw-interface-typed-p ()
  (forall (x)
    (implies
     (sw-loc-p x)
     (and (sw-loc-p (sw-left1 x))
          (sw-loc-p (sw-right1 x))
          (booleanp (sw-m x))
          (booleanp (sw-c x))
          (sw-loc-list-p (sw-path-from-root x))
          (sw-loc-p (sw-left2 x))
          (sw-loc-p (sw-right2 x))
          (booleanp (sw-m1 x))
          (booleanp (sw-c1 x))
          (sw-loc-list-p (sw-path-from-root1 x))))))

(defun sw-edge-old-p (x y)
  (and (not (equal x (sw-null)))
       (or (equal y (sw-left1 x))
           (equal y (sw-right1 x)))))

(defun sw-edge-current-p
  (x y left-kind left-key left-value right-kind right-key right-value)
  (and (not (equal x (sw-null)))
       (or (equal y (sw-left-at left-kind left-key left-value x))
           (equal y (sw-right-at right-kind right-key right-value x)))))

; This recursion is definitionally equivalent to the source inductive path:
; [] is a path exactly from x to x, and x::p follows one old edge before p.
(defun sw-path-old-p (x y p)
  (if (consp p)
      (and (equal (car p) x)
           (let ((z (if (consp (cdr p)) (car (cdr p)) y)))
             (and (sw-edge-old-p x z)
                  (sw-path-old-p z y (cdr p)))))
    (and (equal p nil)
         (equal x y))))

(defun-sk sw-reachable-old-p (x y)
  (exists (p)
    (and (sw-loc-list-p p)
         (sw-path-old-p x y p))))

(defun-sk sw-not-in-stack-p (n stack)
  (forall (i)
    (implies
     (and (integerp i)
          (<= 0 i)
          (< i (len stack)))
     (not (equal (sw-nth-loc i stack) n)))))

(defun-sk sw-index-equals-p (n stack)
  (exists (i)
    (and (integerp i)
         (equal (sw-nth-loc i stack) n))))

(defun-sk sw-distinct-p (stack)
  (forall (i j)
    (implies
     (and (integerp i)
          (integerp j)
          (<= 0 i)
          (< i (len stack))
          (<= 0 j)
          (< j (len stack))
          (equal (sw-nth-loc i stack)
                 (sw-nth-loc j stack)))
     (equal i j))))

(defun-sk sw-graph-closed-p (graph)
  (forall (n)
    (implies
     (and (sw-loc-p n)
          (member-equal n graph))
     (and (not (equal n (sw-null)))
          (or (equal (sw-left1 n) (sw-null))
              (member-equal (sw-left1 n) graph))
          (or (equal (sw-right1 n) (sw-null))
              (member-equal (sw-right1 n) graph))))))

(defun-sk sw-initially-unmarked-p (graph)
  (forall (n)
    (implies
     (and (sw-loc-p n)
          (member-equal n graph))
     (equal (sw-m n) nil))))

(defun-sk sw-graph-stack-cover-p (graph stack)
  (forall (n)
    (implies
     (and (sw-loc-p n)
          (member-equal n graph))
     (or (sw-not-in-stack-p n stack)
         (sw-index-equals-p n stack)))))

(defun-sk sw-m-false-in-set-p (graph set m-kind m-key m-value)
  (forall (n)
    (implies
     (and (sw-loc-p n)
          (member-equal n graph)
          (not (equal (sw-m-at m-kind m-key m-value n) t)))
     (member-equal n set))))

(defun-sk sw-c-false-in-set-p (graph set c-kind c-key c-value)
  (forall (n)
    (implies
     (and (sw-loc-p n)
          (member-equal n graph)
          (not (equal (sw-c-at c-kind c-key c-value n) t)))
     (member-equal n set))))

(defun-sk sw-stack-in-graph-p (graph stack)
  (forall (i)
    (implies
     (and (integerp i)
          (<= 0 i)
          (< i (len stack)))
     (member-equal (sw-nth-loc i stack) graph))))

(defun-sk sw-stack-link-shape-p
    (stack left-kind left-key left-value
           right-kind right-key right-value
           c-kind c-key c-value)
  (forall (i)
    (implies
     (and (integerp i)
          (<= 0 i)
          (< i (- (len stack) 1)))
     (let ((p1 (sw-nth-loc i stack))
           (p2 (sw-nth-loc (+ i 1) stack)))
       (if (equal (sw-c-at c-kind c-key c-value p2) t)
           (and (equal (sw-left1 p2)
                       (sw-left-at left-kind left-key left-value p2))
                (equal (sw-right1 p2) p1))
         (and (equal (sw-left1 p2) p1)
              (equal (sw-right1 p2)
                     (sw-right-at right-kind right-key right-value p2))))))))

(defun-sk sw-off-stack-restored-p
    (graph stack left-kind left-key left-value
                 right-kind right-key right-value)
  (forall (n)
    (implies
     (and (sw-loc-p n)
          (member-equal n graph)
          (sw-not-in-stack-p n stack))
     (and (equal (sw-left1 n)
                 (sw-left-at left-kind left-key left-value n))
          (equal (sw-right1 n)
                 (sw-right-at right-kind right-key right-value n))))))

(defun-sk sw-stack-forward-links-p
    (stack left-kind left-key left-value
           right-kind right-key right-value
           c-kind c-key c-value)
  (forall (i)
    (implies
     (and (integerp i)
          (<= 0 i)
          (< i (- (len stack) 1)))
     (let ((p1 (sw-nth-loc i stack))
           (p2 (sw-nth-loc (+ i 1) stack)))
       (if (equal (sw-c-at c-kind c-key c-value p1) t)
           (equal (sw-right-at right-kind right-key right-value p1) p2)
         (equal (sw-left-at left-kind left-key left-value p1) p2))))))

(defun-sk sw-stack-marked-p (stack m-kind m-key m-value)
  (forall (i)
    (implies
     (and (integerp i)
          (<= 0 i)
          (< i (len stack)))
     (equal (sw-m-at m-kind m-key m-value
                     (sw-nth-loc i stack))
            t))))

(defun-sk sw-stack-restored-side-p
    (stack left-kind left-key left-value
           right-kind right-key right-value
           c-kind c-key c-value)
  (forall (i)
    (implies
     (and (integerp i)
          (<= 0 i)
          (< i (len stack)))
     (let ((n (sw-nth-loc i stack)))
       (if (equal (sw-c-at c-kind c-key c-value n) t)
           (equal (sw-left1 n)
                  (sw-left-at left-kind left-key left-value n))
         (equal (sw-right1 n)
                (sw-right-at right-kind right-key right-value n)))))))

(defun-sk sw-stack-old-backlinks-p
    (stack c-kind c-key c-value)
  (forall (k)
    (implies
     (and (integerp k)
          (< 0 k)
          (< k (len stack)))
     (let ((n (sw-nth-loc k stack))
           (parent (sw-nth-loc (- k 1) stack)))
       (if (equal (sw-c-at c-kind c-key c-value n) t)
           (equal (sw-right1 n) parent)
         (equal (sw-left1 n) parent))))))

(defun-sk sw-marked-reachable-p (graph root m-kind m-key m-value)
  (forall (n)
    (implies
     (and (sw-loc-p n)
          (member-equal n graph)
          (equal (sw-m-at m-kind m-key m-value n) t))
     (sw-reachable-old-p root n))))

(defun-sk sw-marked-paths-p
    (graph root m-kind m-key m-value path-kind path-key path-value)
  (forall (n)
    (implies
     (and (sw-loc-p n)
          (member-equal n graph)
          (equal (sw-m-at m-kind m-key m-value n) t))
     (sw-path-old-p
      root n (sw-path-at path-kind path-key path-value n)))))

(defun-sk sw-marked-off-stack-closed-p
    (graph stack left-kind left-key left-value
                 right-kind right-key right-value
                 m-kind m-key m-value)
  (forall (n n1)
    (implies
     (and (sw-loc-p n)
          (sw-loc-p n1)
          (member-equal n graph)
          (sw-not-in-stack-p n stack)
          (equal (sw-m-at m-kind m-key m-value n) t)
          (not (equal n1 (sw-null)))
          (sw-edge-current-p
           n n1 left-kind left-key left-value
           right-kind right-key right-value))
     (equal (sw-m-at m-kind m-key m-value n1) t))))

(defun-sk sw-stack-c-closed-p
    (stack left-kind left-key left-value
           right-kind right-key right-value
           m-kind m-key m-value
           c-kind c-key c-value)
  (forall (i n1)
    (implies
     (and (integerp i)
          (sw-loc-p n1)
          (<= 0 i)
          (< i (len stack))
          (equal
           (sw-c-at c-kind c-key c-value
                    (sw-nth-loc i stack))
           t)
          (not (equal n1 (sw-null)))
          (sw-edge-current-p
           (sw-nth-loc i stack) n1
           left-kind left-key left-value
           right-kind right-key right-value))
     (equal (sw-m-at m-kind m-key m-value n1) t))))

(defun sw-state-invariant-p
    (graph root c-false-nodes unmarked-nodes pth stack p tloc
           left-kind left-key left-value
           right-kind right-key right-value
           m-kind m-key m-value
           c-kind c-key c-value
           path-kind path-key path-value)
  (and
   (sw-graph-stack-cover-p graph stack)
   (sw-not-in-stack-p (sw-null) stack)
   (iff (equal (len stack) 0)
        (equal p (sw-null)))
   (implies (not (equal p (sw-null)))
            (member-equal p graph))
   (implies (not (equal (len stack) 0))
            (equal (sw-nth-loc 0 stack) p))
   (sw-m-false-in-set-p
    graph unmarked-nodes m-kind m-key m-value)
   (sw-c-false-in-set-p
    graph c-false-nodes c-kind c-key c-value)
   (sw-stack-in-graph-p graph stack)
   (sw-stack-link-shape-p
    stack left-kind left-key left-value
    right-kind right-key right-value
    c-kind c-key c-value)
   (equal (sw-path-at path-kind path-key path-value root) nil)
   (sw-off-stack-restored-p
    graph stack left-kind left-key left-value
    right-kind right-key right-value)
   (implies
    (not (equal (len stack) 0))
    (if (equal
         (sw-c-at c-kind c-key c-value (sw-last-loc stack))
         t)
        (equal
         (sw-right-at right-kind right-key right-value
                      (sw-last-loc stack))
         (sw-null))
      (equal
       (sw-left-at left-kind left-key left-value
                   (sw-last-loc stack))
       (sw-null))))
   (implies
    (not (equal (len stack) 0))
    (equal (sw-last-loc stack) root))
   (sw-stack-forward-links-p
    stack left-kind left-key left-value
    right-kind right-key right-value
    c-kind c-key c-value)
   (sw-stack-marked-p stack m-kind m-key m-value)
   (sw-distinct-p stack)
   (sw-stack-restored-side-p
    stack left-kind left-key left-value
    right-kind right-key right-value
    c-kind c-key c-value)
   (implies
    (not (equal p (sw-null)))
    (if (equal (sw-c-at c-kind c-key c-value p) t)
        (equal (sw-right1 p) tloc)
      (equal (sw-left1 p) tloc)))
   (sw-stack-old-backlinks-p stack c-kind c-key c-value)
   (implies
    (not (equal p (sw-null)))
    (sw-path-old-p root p pth))
   (sw-marked-reachable-p graph root m-kind m-key m-value)
   (implies (equal p (sw-null))
            (equal tloc root))
   (sw-marked-paths-p
    graph root m-kind m-key m-value
    path-kind path-key path-value)
   (sw-marked-off-stack-closed-p
    graph stack left-kind left-key left-value
    right-kind right-key right-value
    m-kind m-key m-value)
   (sw-stack-c-closed-p
    stack left-kind left-key left-value
    right-kind right-key right-value
    m-kind m-key m-value
    c-kind c-key c-value)))

(defun-sk sw-drop-preserves-not-in-p (stack dropped)
  (forall (n)
    (implies
     (and (sw-loc-p n)
          (sw-not-in-stack-p n stack))
     (sw-not-in-stack-p n dropped))))

(defun-sk sw-cons-shift-p (tloc stack extended)
  (forall (i)
    (implies
     (and (integerp i)
          (< 0 i)
          (<= i (len stack)))
     (equal (sw-nth-loc i extended)
            (sw-nth-loc (- i 1) stack)))))

(defun sw-pop-variant-p (unmarked-nodes c-false-nodes stack dropped)
  (or
   (and (<= 0 (len unmarked-nodes))
        (< (len unmarked-nodes) (len unmarked-nodes)))
   (and (<= 0 (len c-false-nodes))
        (< (len c-false-nodes) (len c-false-nodes)))
   (and (<= 0 (len stack))
        (< (len dropped) (len stack)))))

(defun sw-swing-variant-p (unmarked-nodes c-false-nodes stack p)
  (let ((new-c-false (sw-fset-remove p c-false-nodes)))
    (or
     (and (<= 0 (len unmarked-nodes))
          (< (len unmarked-nodes) (len unmarked-nodes)))
     (and (<= 0 (len c-false-nodes))
          (< (len new-c-false) (len c-false-nodes)))
     (and (equal (len c-false-nodes) (len new-c-false))
          (<= 0 (len stack))
          (< (len stack) (len stack))))))

(defun sw-push-variant-p
    (unmarked-nodes c-false-nodes stack extended tloc)
  (let ((new-unmarked (sw-fset-remove tloc unmarked-nodes))
        (new-c-false (sw-fset-insert tloc c-false-nodes)))
    (or
     (and (<= 0 (len unmarked-nodes))
          (< (len new-unmarked) (len unmarked-nodes)))
     (and
      (equal (len unmarked-nodes) (len new-unmarked))
      (or
       (and (<= 0 (len c-false-nodes))
            (< (len new-c-false) (len c-false-nodes)))
       (and (equal (len c-false-nodes) (len new-c-false))
            (<= 0 (len stack))
            (< (len extended) (len stack))))))))

(defun sw-pop-state-p
    (graph root c-false-nodes unmarked-nodes stack p tloc dropped)
  (and
   (not (equal p (sw-null)))
   (not (equal p (sw-null)))
   (sw-pop-variant-p
    unmarked-nodes c-false-nodes stack dropped)
   (sw-state-invariant-p
    graph root c-false-nodes unmarked-nodes
    (sw-path-from-root1 (sw-right2 p))
    dropped (sw-right2 p) p
    :left2 nil nil
    :right2-update p tloc
    :m1 nil nil
    :c1 nil nil
    :path1 nil nil)))

(defun sw-pop-branch-p
    (graph root c-false-nodes unmarked-nodes stack p tloc)
  (let ((dropped (cdr stack)))
    (and
     (< 0 (len stack))
     (implies
      (sw-drop-preserves-not-in-p stack dropped)
      (sw-pop-state-p
       graph root c-false-nodes unmarked-nodes
       stack p tloc dropped)))))

(defun sw-swing-branch-p
    (graph root c-false-nodes unmarked-nodes pth stack p tloc)
  (and
   (not (equal p (sw-null)))
   (not (equal p (sw-null)))
   (not (equal p (sw-null)))
   (not (equal p (sw-null)))
   (not (equal p (sw-null)))
   (sw-swing-variant-p
    unmarked-nodes c-false-nodes stack p)
   (sw-state-invariant-p
    graph root
    (sw-fset-remove p c-false-nodes)
    unmarked-nodes
    pth stack p (sw-right2 p)
    :left2-update p tloc
    :right2-update p (sw-left2 p)
    :m1 nil nil
    :c1-update p t
    :path1 nil nil)))

(defun sw-push-state-p
    (graph root c-false-nodes unmarked-nodes stack p tloc
           extended new-pth)
  (and
   (not (equal tloc (sw-null)))
   (not (equal tloc (sw-null)))
   (sw-push-variant-p
    unmarked-nodes c-false-nodes stack extended tloc)
   (sw-state-invariant-p
    graph root
    (sw-fset-insert tloc c-false-nodes)
    (sw-fset-remove tloc unmarked-nodes)
    new-pth extended tloc (sw-left2 tloc)
    :left2-update tloc p
    :right2 nil nil
    :m1-update tloc t
    :c1-update tloc nil
    :path1-update tloc new-pth)))

(defun sw-push-branch-p
    (graph root c-false-nodes unmarked-nodes pth stack p tloc)
  (let ((extended (cons tloc stack)))
    (implies
     (and (equal (len extended) (+ 1 (len stack)))
          (equal (sw-nth-loc 0 extended) tloc)
          (sw-cons-shift-p tloc stack extended))
     (and
      (not (equal tloc (sw-null)))
      (if (not (equal tloc root))
          (sw-push-state-p
           graph root c-false-nodes unmarked-nodes
           stack p tloc extended
           (sw-append-one pth p))
        (sw-push-state-p
         graph root c-false-nodes unmarked-nodes
         stack p tloc extended nil))))))

(defun-sk sw-final-heap-restored-p (graph)
  (forall (n)
    (implies
     (and (sw-loc-p n)
          (member-equal n graph))
     (and (equal (sw-left1 n) (sw-left2 n))
          (equal (sw-right1 n) (sw-right2 n))))))

(defun-sk sw-final-marked-closed-p (graph)
  (forall (n n1)
    (implies
     (and (sw-loc-p n)
          (sw-loc-p n1)
          (member-equal n graph)
          (equal (sw-m1 n) t)
          (not (equal n1 (sw-null)))
          (sw-edge-current-p
           n n1 :left2 nil nil :right2 nil nil))
     (equal (sw-m1 n1) t))))

(defun sw-final-postcondition-p (graph root)
  (and
   (sw-final-heap-restored-p graph)
   (sw-marked-reachable-p graph root :m1 nil nil)
   (equal (sw-m1 root) t)
   (sw-final-marked-closed-p graph)))

(defun sw-o2-condition-p (tloc o2)
  (if (equal tloc (sw-null))
      (equal o2 t)
    (equal o2 (sw-m1 tloc))))

(defun sw-o2-case-p
    (graph root c-false-nodes unmarked-nodes pth stack p tloc o2)
  (implies
   (sw-o2-condition-p tloc o2)
   (if (equal o2 t)
       (and
        (not (equal p (sw-null)))
        (if (equal (sw-c1 p) t)
            (sw-pop-branch-p
             graph root c-false-nodes unmarked-nodes stack p tloc)
          (sw-swing-branch-p
           graph root c-false-nodes unmarked-nodes
           pth stack p tloc)))
     (sw-push-branch-p
      graph root c-false-nodes unmarked-nodes
      pth stack p tloc))))

(defun-sk sw-all-o2-p
    (graph root c-false-nodes unmarked-nodes pth stack p tloc)
  (forall (o2)
    (implies
     (booleanp o2)
     (sw-o2-case-p
      graph root c-false-nodes unmarked-nodes
      pth stack p tloc o2))))

(defun sw-o1-condition-p (p tloc o1)
  (if (not (equal p (sw-null)))
      (equal o1 t)
    (if (not (equal tloc (sw-null)))
        (equal o1
               (if (equal (sw-m1 tloc) t) nil t))
      (equal o1 nil))))

(defun sw-o1-case-p
    (graph root c-false-nodes unmarked-nodes pth stack p tloc o1)
  (implies
   (sw-o1-condition-p p tloc o1)
   (if (equal o1 t)
       (sw-all-o2-p
        graph root c-false-nodes unmarked-nodes
        pth stack p tloc)
     (sw-final-postcondition-p graph root))))

(defun-sk sw-all-o1-p
    (graph root c-false-nodes unmarked-nodes pth stack p tloc)
  (forall (o1)
    (implies
     (booleanp o1)
     (sw-o1-case-p
      graph root c-false-nodes unmarked-nodes
      pth stack p tloc o1))))

(defun sw-loop-state-case-p
    (graph root c-false-nodes unmarked-nodes pth stack p tloc)
  (implies
   (sw-state-invariant-p
    graph root c-false-nodes unmarked-nodes pth stack p tloc
    :left2 nil nil
    :right2 nil nil
    :m1 nil nil
    :c1 nil nil
    :path1 nil nil)
   (sw-all-o1-p
    graph root c-false-nodes unmarked-nodes pth stack p tloc)))

(defun-sk sw-all-loop-states-p (graph root)
  (forall (c-false-nodes unmarked-nodes pth stack p tloc)
    (implies
     (and (sw-fset-p c-false-nodes)
          (sw-fset-p unmarked-nodes)
          (sw-loc-list-p pth)
          (sw-loc-list-p stack)
          (sw-loc-p p)
          (sw-loc-p tloc))
     (sw-loop-state-case-p
      graph root c-false-nodes unmarked-nodes
      pth stack p tloc))))

(defun sw-initial-state-p (graph root)
  (and
   (not (equal root (sw-null)))
   (sw-state-invariant-p
    graph root graph graph nil nil (sw-null) root
    :left1 nil nil
    :right1 nil nil
    :m nil nil
    :c nil nil
    :path-update root nil)))

(defun pearl/schorr_waite_SchorrWaite_schorr_waiteqtvc-statement
    (root graph)
  (implies
   (and
    (sw-loc-p (sw-null))
    (sw-loc-p (sw-default-loc))
    (sw-interface-typed-p)
    (sw-loc-p root)
    (sw-fset-p graph)
    (not (equal root (sw-null)))
    (member-equal root graph)
    (sw-graph-closed-p graph)
    (sw-initially-unmarked-p graph))
   (and
    (sw-initial-state-p graph root)
    (sw-all-loop-states-p graph root))))

(value-triple :itpeval-statement-checked)
:q
