;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/ropes_Balance_insert_leavesqtvc: the verification condition for
;; inserting the leaves of a rope into a queue while preserving rope
;; invariants and the modeled concatenated string. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces for the source's abstract character and immutable
;; string carriers, Fibonacci function, and string-of-array specification.

(defstub ropes-il-char-p (value) t)
(defstub ropes-il-char-string-p (value) t)
(defstub ropes-il-dummy-char () t)
(defstub ropes-il-string-length (string) t)
(defstub ropes-il-string-index (string index) t)
(defstub ropes-il-string-empty () t)
(defstub ropes-il-string-app (left right) t)
(defstub ropes-il-string-sub (string offset length) t)
(defstub ropes-il-fib (index) t)
(defstub ropes-il-max () t)
(defstub ropes-il-string-of-array (queue lower upper) t)

;; Source string equality is extensional equality: equal lengths and equal
;; characters at every integer index in the shared valid range.

(defun-sk ropes-il-strings-agree-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (ropes-il-string-length left)))
      (equal
       (ropes-il-string-index left index)
       (ropes-il-string-index right index))))))

(defun ropes-il-string-equal-p (left right)
  (and
   (ropes-il-char-string-p left)
   (ropes-il-char-string-p right)
   (equal
    (ropes-il-string-length left)
    (ropes-il-string-length right))
   (ropes-il-strings-agree-p left right)))

;; Exact records for the Why3 algebraic datatype:
;;   (:ROPE-EMP)
;;   (:ROPE-STR string offset length)
;;   (:ROPE-APP left right length).

(defun ropes-il-emp ()
  (list :rope-emp))

(defun ropes-il-emp-p (rope)
  (equal rope (ropes-il-emp)))

(defun ropes-il-str-shape-p (rope)
  (and
   (true-listp rope)
   (equal (len rope) 4)
   (equal (car rope) :rope-str)))

(defun ropes-il-str-string (rope)
  (cadr rope))

(defun ropes-il-str-offset (rope)
  (caddr rope))

(defun ropes-il-str-length (rope)
  (cadddr rope))

(defun ropes-il-app-shape-p (rope)
  (and
   (true-listp rope)
   (equal (len rope) 4)
   (equal (car rope) :rope-app)))

(defun ropes-il-app-left (rope)
  (cadr rope))

(defun ropes-il-app-right (rope)
  (caddr rope))

(defun ropes-il-app-length (rope)
  (cadddr rope))

(defun ropes-il-rope-p (rope)
  (declare (xargs :measure (acl2-count rope)))
  (cond
   ((ropes-il-emp-p rope)
    t)
   ((ropes-il-str-shape-p rope)
    (and
     (ropes-il-char-string-p
      (ropes-il-str-string rope))
     (integerp
      (ropes-il-str-offset rope))
     (integerp
      (ropes-il-str-length rope))))
   ((ropes-il-app-shape-p rope)
    (and
     (ropes-il-rope-p
      (ropes-il-app-left rope))
     (ropes-il-rope-p
      (ropes-il-app-right rope))
     (integerp
      (ropes-il-app-length rope))))
   (t nil)))

(defun ropes-il-rope-list-p (queue)
  (declare (xargs :measure (acl2-count queue)))
  (if (consp queue)
      (and
       (ropes-il-rope-p (car queue))
       (ropes-il-rope-list-p (cdr queue)))
    (equal queue nil)))

;; These are the source definitions of Rope.length, Rope.inv, and Rope.string.

(defun ropes-il-rope-length (rope)
  (cond
   ((ropes-il-emp-p rope)
    0)
   ((ropes-il-str-shape-p rope)
    (ropes-il-str-length rope))
   ((ropes-il-app-shape-p rope)
    (ropes-il-app-length rope))
   (t 0)))

(defun ropes-il-rope-inv-p (rope)
  (declare (xargs :measure (acl2-count rope)))
  (cond
   ((ropes-il-emp-p rope)
    t)
   ((ropes-il-str-shape-p rope)
    (let ((string (ropes-il-str-string rope))
          (offset (ropes-il-str-offset rope))
          (length (ropes-il-str-length rope)))
      (and
       (< 0 length)
       (<= 0 offset)
       (< offset
          (ropes-il-string-length string))
       (<= (+ offset length)
           (ropes-il-string-length string)))))
   ((ropes-il-app-shape-p rope)
    (let ((left (ropes-il-app-left rope))
          (right (ropes-il-app-right rope))
          (length (ropes-il-app-length rope)))
      (and
       (< 0 (ropes-il-rope-length left))
       (ropes-il-rope-inv-p left)
       (< 0 (ropes-il-rope-length right))
       (ropes-il-rope-inv-p right)
       (equal
        length
        (+ (ropes-il-rope-length left)
           (ropes-il-rope-length right))))))
   (t nil)))

(defun ropes-il-rope-string (rope)
  (declare (xargs :measure (acl2-count rope)))
  (cond
   ((ropes-il-emp-p rope)
    (ropes-il-string-empty))
   ((ropes-il-str-shape-p rope)
    (ropes-il-string-sub
     (ropes-il-str-string rope)
     (ropes-il-str-offset rope)
     (ropes-il-str-length rope)))
   ((ropes-il-app-shape-p rope)
    (ropes-il-string-app
     (ropes-il-rope-string
      (ropes-il-app-left rope))
     (ropes-il-rope-string
      (ropes-il-app-right rope))))
   (t
    (ropes-il-string-empty))))

;; Proper lists of ropes are exact finite-array values for this VC. All reads
;; occur under translated integer bounds, so NTH with NFIX is precisely the
;; exported Int.toNat/list indexing representation.

(defun ropes-il-array-get (queue index)
  (nth (nfix index) queue))

(defun ropes-il-string-of-queue (queue)
  (ropes-il-string-of-array
   queue
   2
   (len queue)))

;; The complete source typing and axiomatic context remains explicit in the
;; statement instead of being admitted as ACL2 axioms.

(defun-sk ropes-il-string-function-types-p ()
  (forall (string left right index offset length)
    (and
     (implies
      (ropes-il-char-string-p string)
      (integerp
       (ropes-il-string-length string)))
     (implies
      (and
       (ropes-il-char-string-p string)
       (integerp index))
      (ropes-il-char-p
       (ropes-il-string-index string index)))
     (implies
      (and
       (ropes-il-char-string-p left)
       (ropes-il-char-string-p right))
      (ropes-il-char-string-p
       (ropes-il-string-app left right)))
     (implies
      (and
       (ropes-il-char-string-p string)
       (integerp offset)
       (integerp length))
      (ropes-il-char-string-p
       (ropes-il-string-sub
        string offset length))))))

(defun-sk ropes-il-string-length-nonnegative-p ()
  (forall (string)
    (implies
     (ropes-il-char-string-p string)
     (<= 0
         (ropes-il-string-length string)))))

(defun-sk ropes-il-string-extensionality-p ()
  (forall (left right)
    (implies
     (and
      (ropes-il-char-string-p left)
      (ropes-il-char-string-p right)
      (ropes-il-string-equal-p left right))
     (equal left right))))

(defun-sk ropes-il-string-app-length-law-p ()
  (forall (left right)
    (implies
     (and
      (ropes-il-char-string-p left)
      (ropes-il-char-string-p right))
     (equal
      (ropes-il-string-length
       (ropes-il-string-app left right))
      (+ (ropes-il-string-length left)
         (ropes-il-string-length right))))))

(defun-sk ropes-il-string-app-left-law-p ()
  (forall (left right index)
    (implies
     (and
      (ropes-il-char-string-p left)
      (ropes-il-char-string-p right)
      (integerp index)
      (<= 0 index)
      (< index
         (ropes-il-string-length left)))
     (equal
      (ropes-il-string-index
       (ropes-il-string-app left right)
       index)
      (ropes-il-string-index left index)))))

(defun-sk ropes-il-string-app-right-law-p ()
  (forall (left right index)
    (implies
     (and
      (ropes-il-char-string-p left)
      (ropes-il-char-string-p right)
      (integerp index)
      (<= (ropes-il-string-length left)
          index)
      (< index
         (+ (ropes-il-string-length left)
            (ropes-il-string-length right))))
     (equal
      (ropes-il-string-index
       (ropes-il-string-app left right)
       index)
      (ropes-il-string-index
       right
       (- index
          (ropes-il-string-length left)))))))

(defun-sk ropes-il-string-sub-length-law-p ()
  (forall (string offset length)
    (implies
     (and
      (ropes-il-char-string-p string)
      (integerp offset)
      (integerp length)
      (<= 0 length)
      (<= 0 offset)
      (<= offset
          (ropes-il-string-length string))
      (<= (+ offset length)
          (ropes-il-string-length string)))
     (equal
      (ropes-il-string-length
       (ropes-il-string-sub
        string offset length))
      length))))

(defun-sk ropes-il-string-sub-index-law-p ()
  (forall (string offset length index)
    (implies
     (and
      (ropes-il-char-string-p string)
      (integerp offset)
      (integerp length)
      (integerp index)
      (<= 0 length)
      (<= 0 offset)
      (<= offset
          (ropes-il-string-length string))
      (<= (+ offset length)
          (ropes-il-string-length string))
      (<= 0 index)
      (< index length))
     (equal
      (ropes-il-string-index
       (ropes-il-string-sub
        string offset length)
       index)
      (ropes-il-string-index
       string
       (+ offset index))))))

(defun-sk ropes-il-fibonacci-law-p ()
  (forall (index)
    (implies
     (integerp index)
     (and
      (integerp (ropes-il-fib index))
      (implies
       (<= 0 index)
       (equal
        (ropes-il-fib index)
        (if (equal index 0)
            0
          (if (equal index 1)
              1
            (+ (ropes-il-fib (- index 1))
               (ropes-il-fib (- index 2)))))))))))

(defun-sk ropes-il-string-of-array-type-p ()
  (forall (queue lower upper)
    (implies
     (and
      (ropes-il-rope-list-p queue)
      (integerp lower)
      (integerp upper))
     (ropes-il-char-string-p
      (ropes-il-string-of-array
       queue lower upper)))))

(defun-sk ropes-il-string-of-array-empty-law-p ()
  (forall (queue lower)
    (implies
     (and
      (ropes-il-rope-list-p queue)
      (integerp lower)
      (<= 0 lower)
      (<= lower (len queue)))
     (ropes-il-string-equal-p
      (ropes-il-string-of-array
       queue lower lower)
      (ropes-il-string-empty)))))

(defun-sk ropes-il-string-of-array-concat-left-law-p ()
  (forall (queue lower upper)
    (implies
     (and
      (ropes-il-rope-list-p queue)
      (integerp lower)
      (integerp upper)
      (<= 0 lower)
      (< lower upper)
      (<= upper (len queue)))
     (ropes-il-string-equal-p
      (ropes-il-string-of-array
       queue lower upper)
      (ropes-il-string-app
       (ropes-il-string-of-array
        queue (+ lower 1) upper)
       (ropes-il-rope-string
        (ropes-il-array-get queue lower)))))))

(defun ropes-il-background-p ()
  (and
   (ropes-il-char-p
    (ropes-il-dummy-char))
   (ropes-il-char-string-p
    (ropes-il-string-empty))
   (equal
    (ropes-il-string-length
     (ropes-il-string-empty))
    0)
   (ropes-il-string-function-types-p)
   (ropes-il-string-length-nonnegative-p)
   (ropes-il-string-extensionality-p)
   (ropes-il-string-app-length-law-p)
   (ropes-il-string-app-left-law-p)
   (ropes-il-string-app-right-law-p)
   (ropes-il-string-sub-length-law-p)
   (ropes-il-string-sub-index-law-p)
   (ropes-il-fibonacci-law-p)
   (integerp (ropes-il-max))
   (<= 2 (ropes-il-max))
   (ropes-il-string-of-array-type-p)
   (ropes-il-string-of-array-empty-law-p)
   (ropes-il-string-of-array-concat-left-law-p)))

;; Range predicates retain the source universal quantification over all
;; mathematical integers.

(defun-sk ropes-il-all-invariant-p (queue lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (<= index upper))
      (ropes-il-rope-inv-p
       (ropes-il-array-get queue index))))))

(defun-sk ropes-il-prefix-equal-p
    (new-queue old-queue lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (ropes-il-array-get new-queue index)
       (ropes-il-array-get old-queue index))))))

;; This preserves the source match on the original App node. In the App branch,
;; the selected recursive argument must equal one of that node's two children.

(defun ropes-il-app-child-p (source child)
  (and
   (ropes-il-app-shape-p source)
   (or
    (equal (ropes-il-app-left source) child)
    (equal (ropes-il-app-right source) child))))

;; The common precondition generated for either recursive App call.

(defun ropes-il-recursive-call-obligations-p
    (queue source child)
  (and
   (ropes-il-app-child-p source child)
   (< 2 (len queue))
   (equal
    (len queue)
    (+ (ropes-il-max) 1))
   (ropes-il-rope-inv-p child)
   (ropes-il-all-invariant-p
    queue 2 (ropes-il-max))
   (< (+ (ropes-il-string-length
          (ropes-il-string-of-queue queue))
         (ropes-il-rope-length child))
      (ropes-il-fib
       (+ (ropes-il-max) 1)))))

;; q2 is the universally quantified post-state of the recursive call on the
;; right child. Its conclusion is the original call's complete postcondition.

(defun-sk ropes-il-app-right-post-universal-p
    (original-queue queue1 source right)
  (forall (queue2)
    (implies
     (ropes-il-rope-list-p queue2)
     (implies
      (equal
       (len queue2)
       (len queue1))
      (implies
       (and
        (ropes-il-all-invariant-p
         queue2 2 (ropes-il-max))
        (ropes-il-string-equal-p
         (ropes-il-string-of-queue queue2)
         (ropes-il-string-app
          (ropes-il-string-of-queue queue1)
          (ropes-il-rope-string right))))
       (and
        (ropes-il-all-invariant-p
         queue2 2 (ropes-il-max))
        (ropes-il-string-equal-p
         (ropes-il-string-of-queue queue2)
         (ropes-il-string-app
          (ropes-il-string-of-queue original-queue)
          (ropes-il-rope-string source)))))))))

;; q1 is the universally quantified post-state of the recursive call on the
;; left child. It establishes the right call and its universal postcondition.

(defun-sk ropes-il-app-left-post-universal-p
    (queue source left right)
  (forall (queue1)
    (implies
     (ropes-il-rope-list-p queue1)
     (implies
      (equal
       (len queue1)
       (len queue))
      (implies
       (and
        (ropes-il-all-invariant-p
         queue1 2 (ropes-il-max))
        (ropes-il-string-equal-p
         (ropes-il-string-of-queue queue1)
         (ropes-il-string-app
          (ropes-il-string-of-queue queue)
          (ropes-il-rope-string left))))
       (and
        (ropes-il-recursive-call-obligations-p
         queue1 source right)
        (ropes-il-app-right-post-universal-p
         queue queue1 source right)))))))

;; The Str branch calls insert at index 2, then universally quantifies over its
;; possible post-state q1 with the exact frame and modeled-string hypotheses.

(defun-sk ropes-il-leaf-post-universal-p
    (queue source)
  (forall (queue1)
    (implies
     (ropes-il-rope-list-p queue1)
     (implies
      (equal
       (len queue1)
       (len queue))
      (implies
       (and
        (ropes-il-all-invariant-p
         queue1 2 (ropes-il-max))
        (ropes-il-prefix-equal-p
         queue1 queue 2 2)
        (ropes-il-string-equal-p
         (ropes-il-string-of-array
          queue1
          2
          (+ (ropes-il-max) 1))
         (ropes-il-string-app
          (ropes-il-string-of-array
           queue
           2
           (+ (ropes-il-max) 1))
          (ropes-il-rope-string source))))
       (and
        (ropes-il-all-invariant-p
         queue1 2 (ropes-il-max))
        (ropes-il-string-equal-p
         (ropes-il-string-of-queue queue1)
         (ropes-il-string-app
          (ropes-il-string-of-queue queue)
          (ropes-il-rope-string source)))))))))

(defun ropes-il-leaf-branch-p (queue source)
  (and
   (and
    (<= 2 2)
    (< 2 (len queue))
    (equal
     (len queue)
     (+ (ropes-il-max) 1)))
   (ropes-il-rope-inv-p source)
   (ropes-il-all-invariant-p
    queue 2 (ropes-il-max))
   (< (+ (ropes-il-string-length
          (ropes-il-string-of-array
           queue
           2
           (+ (ropes-il-max) 1)))
         (ropes-il-rope-length source))
      (ropes-il-fib
       (+ (ropes-il-max) 1)))
   (ropes-il-leaf-post-universal-p
    queue source)))

(defun ropes-il-empty-branch-p (queue source)
  (and
   (ropes-il-all-invariant-p
    queue 2 (ropes-il-max))
   (ropes-il-string-equal-p
    (ropes-il-string-of-queue queue)
    (ropes-il-string-app
     (ropes-il-string-of-queue queue)
     (ropes-il-rope-string source)))))

(defun ropes-il-app-branch-p (queue source)
  (let ((left (ropes-il-app-left source))
        (right (ropes-il-app-right source)))
    (and
     (ropes-il-recursive-call-obligations-p
      queue source left)
     (ropes-il-app-left-post-universal-p
      queue source left right))))

;; This conditional is definitionally the source match on r.

(defun ropes-il-insert-leaves-conclusion-p (queue source)
  (cond
   ((ropes-il-emp-p source)
    (ropes-il-empty-branch-p queue source))
   ((ropes-il-str-shape-p source)
    (ropes-il-leaf-branch-p queue source))
   ((ropes-il-app-shape-p source)
    (ropes-il-app-branch-p queue source))
   (t nil)))

(defun-sk
    ntp4vc-pearl-ropes-balance-insert-leavesqtvc-statement ()
  (forall (queue source)
    (implies
     (and
      (ropes-il-background-p)
      (ropes-il-rope-list-p queue)
      (ropes-il-rope-p source)
      (< 2 (len queue))
      (equal
       (len queue)
       (+ (ropes-il-max) 1))
      (ropes-il-rope-inv-p source)
      (ropes-il-all-invariant-p
       queue 2 (ropes-il-max))
      (< (+ (ropes-il-string-length
             (ropes-il-string-of-queue queue))
            (ropes-il-rope-length source))
         (ropes-il-fib
          (+ (ropes-il-max) 1))))
     (ropes-il-insert-leaves-conclusion-p
      queue source))))

(value-triple :itpeval-statement-checked)
:q
