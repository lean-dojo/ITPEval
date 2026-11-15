;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/ropes_Balance_balanceqtvc: the rope balancing verification condition
;; for queue initialization, leaf insertion, and reconstruction of a balanced
;; rope with the same modeled string. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces for the source's abstract character and immutable
;; string carriers, Fibonacci function, and string-of-array specification.

(defstub ropes-char-p (value) t)
(defstub ropes-char-string-p (value) t)
(defstub ropes-dummy-char () t)
(defstub ropes-string-length (string) t)
(defstub ropes-string-index (string index) t)
(defstub ropes-string-empty () t)
(defstub ropes-string-app (left right) t)
(defstub ropes-string-sub (string offset length) t)
(defstub ropes-fib (index) t)
(defstub ropes-max () t)
(defstub ropes-string-of-array (queue lower upper) t)

;; Source string equality is extensional equality: equal lengths and equal
;; characters at every integer index in the shared valid range.

(defun-sk ropes-strings-agree-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (ropes-string-length left)))
      (equal
       (ropes-string-index left index)
       (ropes-string-index right index))))))

(defun ropes-string-equal-p (left right)
  (and
   (ropes-char-string-p left)
   (ropes-char-string-p right)
   (equal
    (ropes-string-length left)
    (ropes-string-length right))
   (ropes-strings-agree-p left right)))

;; Exact records for the Why3 algebraic datatype:
;;   (:ROPE-EMP)
;;   (:ROPE-STR string offset length)
;;   (:ROPE-APP left right length).

(defun ropes-emp ()
  (list :rope-emp))

(defun ropes-emp-p (rope)
  (equal rope (ropes-emp)))

(defun ropes-str-shape-p (rope)
  (and
   (true-listp rope)
   (equal (len rope) 4)
   (equal (car rope) :rope-str)))

(defun ropes-str-string (rope)
  (cadr rope))

(defun ropes-str-offset (rope)
  (caddr rope))

(defun ropes-str-length (rope)
  (cadddr rope))

(defun ropes-app-shape-p (rope)
  (and
   (true-listp rope)
   (equal (len rope) 4)
   (equal (car rope) :rope-app)))

(defun ropes-app-left (rope)
  (cadr rope))

(defun ropes-app-right (rope)
  (caddr rope))

(defun ropes-app-length (rope)
  (cadddr rope))

(defun ropes-rope-p (rope)
  (declare (xargs :measure (acl2-count rope)))
  (cond
   ((ropes-emp-p rope)
    t)
   ((ropes-str-shape-p rope)
    (and
     (ropes-char-string-p
      (ropes-str-string rope))
     (integerp
      (ropes-str-offset rope))
     (integerp
      (ropes-str-length rope))))
   ((ropes-app-shape-p rope)
    (and
     (ropes-rope-p
      (ropes-app-left rope))
     (ropes-rope-p
      (ropes-app-right rope))
     (integerp
      (ropes-app-length rope))))
   (t nil)))

(defun ropes-rope-list-p (queue)
  (declare (xargs :measure (acl2-count queue)))
  (if (consp queue)
      (and
       (ropes-rope-p (car queue))
       (ropes-rope-list-p (cdr queue)))
    (equal queue nil)))

;; These are the source definitions of Rope.length, Rope.inv, and Rope.string.

(defun ropes-rope-length (rope)
  (cond
   ((ropes-emp-p rope)
    0)
   ((ropes-str-shape-p rope)
    (ropes-str-length rope))
   ((ropes-app-shape-p rope)
    (ropes-app-length rope))
   (t 0)))

(defun ropes-rope-inv-p (rope)
  (declare (xargs :measure (acl2-count rope)))
  (cond
   ((ropes-emp-p rope)
    t)
   ((ropes-str-shape-p rope)
    (let ((string (ropes-str-string rope))
          (offset (ropes-str-offset rope))
          (length (ropes-str-length rope)))
      (and
       (< 0 length)
       (<= 0 offset)
       (< offset
          (ropes-string-length string))
       (<= (+ offset length)
           (ropes-string-length string)))))
   ((ropes-app-shape-p rope)
    (let ((left (ropes-app-left rope))
          (right (ropes-app-right rope))
          (length (ropes-app-length rope)))
      (and
       (< 0 (ropes-rope-length left))
       (ropes-rope-inv-p left)
       (< 0 (ropes-rope-length right))
       (ropes-rope-inv-p right)
       (equal
        length
        (+ (ropes-rope-length left)
           (ropes-rope-length right))))))
   (t nil)))

(defun ropes-rope-string (rope)
  (declare (xargs :measure (acl2-count rope)))
  (cond
   ((ropes-emp-p rope)
    (ropes-string-empty))
   ((ropes-str-shape-p rope)
    (ropes-string-sub
     (ropes-str-string rope)
     (ropes-str-offset rope)
     (ropes-str-length rope)))
   ((ropes-app-shape-p rope)
    (ropes-string-app
     (ropes-rope-string
      (ropes-app-left rope))
     (ropes-rope-string
      (ropes-app-right rope))))
   (t
    (ropes-string-empty))))

;; Proper lists of ropes are exact finite-array values for this VC. All array
;; reads occur under translated integer bounds, so NTH with NFIX is precisely
;; the exported Int.toNat/list indexing representation.

(defun ropes-array-get (queue index)
  (nth (nfix index) queue))

(defun ropes-string-of-queue (queue)
  (ropes-string-of-array
   queue
   2
   (len queue)))

;; The complete source typing and axiomatic context remains explicit in the
;; statement instead of being admitted as ACL2 axioms.

(defun-sk ropes-string-function-types-p ()
  (forall (string left right index offset length)
    (and
     (implies
      (ropes-char-string-p string)
      (integerp
       (ropes-string-length string)))
     (implies
      (and
       (ropes-char-string-p string)
       (integerp index))
      (ropes-char-p
       (ropes-string-index string index)))
     (implies
      (and
       (ropes-char-string-p left)
       (ropes-char-string-p right))
      (ropes-char-string-p
       (ropes-string-app left right)))
     (implies
      (and
       (ropes-char-string-p string)
       (integerp offset)
       (integerp length))
      (ropes-char-string-p
       (ropes-string-sub
        string offset length))))))

(defun-sk ropes-string-length-nonnegative-p ()
  (forall (string)
    (implies
     (ropes-char-string-p string)
     (<= 0
         (ropes-string-length string)))))

(defun-sk ropes-string-extensionality-p ()
  (forall (left right)
    (implies
     (and
      (ropes-char-string-p left)
      (ropes-char-string-p right)
      (ropes-string-equal-p left right))
     (equal left right))))

(defun-sk ropes-string-app-length-law-p ()
  (forall (left right)
    (implies
     (and
      (ropes-char-string-p left)
      (ropes-char-string-p right))
     (equal
      (ropes-string-length
       (ropes-string-app left right))
      (+ (ropes-string-length left)
         (ropes-string-length right))))))

(defun-sk ropes-string-app-left-law-p ()
  (forall (left right index)
    (implies
     (and
      (ropes-char-string-p left)
      (ropes-char-string-p right)
      (integerp index)
      (<= 0 index)
      (< index
         (ropes-string-length left)))
     (equal
      (ropes-string-index
       (ropes-string-app left right)
       index)
      (ropes-string-index left index)))))

(defun-sk ropes-string-app-right-law-p ()
  (forall (left right index)
    (implies
     (and
      (ropes-char-string-p left)
      (ropes-char-string-p right)
      (integerp index)
      (<= (ropes-string-length left)
          index)
      (< index
         (+ (ropes-string-length left)
            (ropes-string-length right))))
     (equal
      (ropes-string-index
       (ropes-string-app left right)
       index)
      (ropes-string-index
       right
       (- index
          (ropes-string-length left)))))))

(defun-sk ropes-string-sub-length-law-p ()
  (forall (string offset length)
    (implies
     (and
      (ropes-char-string-p string)
      (integerp offset)
      (integerp length)
      (<= 0 length)
      (<= 0 offset)
      (<= offset
          (ropes-string-length string))
      (<= (+ offset length)
          (ropes-string-length string)))
     (equal
      (ropes-string-length
       (ropes-string-sub
        string offset length))
      length))))

(defun-sk ropes-string-sub-index-law-p ()
  (forall (string offset length index)
    (implies
     (and
      (ropes-char-string-p string)
      (integerp offset)
      (integerp length)
      (integerp index)
      (<= 0 length)
      (<= 0 offset)
      (<= offset
          (ropes-string-length string))
      (<= (+ offset length)
          (ropes-string-length string))
      (<= 0 index)
      (< index length))
     (equal
      (ropes-string-index
       (ropes-string-sub
        string offset length)
       index)
      (ropes-string-index
       string
       (+ offset index))))))

(defun-sk ropes-fibonacci-law-p ()
  (forall (index)
    (implies
     (integerp index)
     (and
      (integerp (ropes-fib index))
      (implies
       (<= 0 index)
       (equal
        (ropes-fib index)
        (if (equal index 0)
            0
          (if (equal index 1)
              1
            (+ (ropes-fib (- index 1))
               (ropes-fib (- index 2)))))))))))

(defun-sk ropes-string-of-array-type-p ()
  (forall (queue lower upper)
    (implies
     (and
      (ropes-rope-list-p queue)
      (integerp lower)
      (integerp upper))
     (ropes-char-string-p
      (ropes-string-of-array
       queue lower upper)))))

(defun-sk ropes-string-of-array-empty-law-p ()
  (forall (queue lower)
    (implies
     (and
      (ropes-rope-list-p queue)
      (integerp lower)
      (<= 0 lower)
      (<= lower (len queue)))
     (ropes-string-equal-p
      (ropes-string-of-array
       queue lower lower)
      (ropes-string-empty)))))

(defun-sk ropes-string-of-array-concat-left-law-p ()
  (forall (queue lower upper)
    (implies
     (and
      (ropes-rope-list-p queue)
      (integerp lower)
      (integerp upper)
      (<= 0 lower)
      (< lower upper)
      (<= upper (len queue)))
     (ropes-string-equal-p
      (ropes-string-of-array
       queue lower upper)
      (ropes-string-app
       (ropes-string-of-array
        queue (+ lower 1) upper)
       (ropes-rope-string
        (ropes-array-get queue lower)))))))

(defun ropes-background-p ()
  (and
   (ropes-char-p
    (ropes-dummy-char))
   (ropes-char-string-p
    (ropes-string-empty))
   (equal
    (ropes-string-length
     (ropes-string-empty))
    0)
   (ropes-string-function-types-p)
   (ropes-string-length-nonnegative-p)
   (ropes-string-extensionality-p)
   (ropes-string-app-length-law-p)
   (ropes-string-app-left-law-p)
   (ropes-string-app-right-law-p)
   (ropes-string-sub-length-law-p)
   (ropes-string-sub-index-law-p)
   (ropes-fibonacci-law-p)
   (integerp (ropes-max))
   (<= 2 (ropes-max))
   (ropes-string-of-array-type-p)
   (ropes-string-of-array-empty-law-p)
   (ropes-string-of-array-concat-left-law-p)))

;; Range predicates retain the source universal quantification over all
;; mathematical integers.

(defun-sk ropes-all-emp-p (queue upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index upper))
      (equal
       (ropes-array-get queue index)
       (ropes-emp))))))

(defun-sk ropes-all-invariant-p (queue lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (<= index upper))
      (ropes-rope-inv-p
       (ropes-array-get queue index))))))

;; This is the innermost universal obligation for the result of concatenating
;; q1[i] with the loop accumulator.

(defun-sk ropes-concat-result-universal-p
    (queue index current item)
  (forall (combined)
    (implies
     (ropes-rope-p combined)
     (implies
      (and
       (ropes-rope-inv-p combined)
       (ropes-string-equal-p
        (ropes-rope-string combined)
        (ropes-string-app
         (ropes-rope-string item)
         (ropes-rope-string current))))
      (and
       (ropes-rope-inv-p combined)
       (ropes-string-equal-p
        (ropes-rope-string combined)
        (ropes-string-of-array
         queue
         2
         (+ index 1))))))))

;; Preserve the loop invariant's universal quantifier over integer indices and
;; its conjunction of bounds, current invariant, and modeled-string equality.

(defun-sk ropes-loop-index-universal-p
    (queue upper current)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 2 index)
       (<= index upper)
       (ropes-rope-inv-p current)
       (ropes-string-equal-p
        (ropes-rope-string current)
        (ropes-string-of-array
         queue 2 index)))
      (and
       (<= 0 index)
       (< index (len queue))
       (let ((item
              (ropes-array-get
               queue index)))
         (and
          (ropes-rope-inv-p item)
          (ropes-rope-inv-p current)
          (ropes-concat-result-universal-p
           queue index current item))))))))

;; For every possible loop accumulator, retain both the iteration obligation
;; and the implication from the final invariant to the balance postcondition.

(defun-sk ropes-loop-result-universal-p
    (queue source upper)
  (forall (current)
    (implies
     (ropes-rope-p current)
     (and
      (ropes-loop-index-universal-p
       queue upper current)
      (implies
       (and
        (ropes-rope-inv-p current)
        (ropes-string-equal-p
         (ropes-rope-string current)
         (ropes-string-of-array
          queue
          2
          (+ upper 1))))
       (and
        (ropes-rope-inv-p current)
        (ropes-string-equal-p
         (ropes-rope-string current)
         (ropes-rope-string source))))))))

(defun ropes-fold-obligations-p (queue source)
  (let ((upper (ropes-max)))
    (and
     (implies
      (<= 2 (+ upper 1))
      (and
       (ropes-rope-inv-p
        (ropes-emp))
       (ropes-string-equal-p
        (ropes-rope-string
         (ropes-emp))
        (ropes-string-of-array
         queue 2 2))
       (ropes-loop-result-universal-p
        queue source upper)))
     (implies
      (< (+ upper 1) 2)
      (let ((result (ropes-emp)))
        (and
         (ropes-rope-inv-p result)
         (ropes-string-equal-p
          (ropes-rope-string result)
          (ropes-rope-string source))))))))

;; q1 is the universally quantified post-state of insert_leaves. Its length,
;; per-entry invariant, and modeled concatenation postcondition are unchanged.

(defun-sk ropes-insert-leaves-post-universal-p
    (queue source)
  (forall (queue1)
    (implies
     (ropes-rope-list-p queue1)
     (implies
      (equal
       (len queue1)
       (len queue))
      (implies
       (and
        (ropes-all-invariant-p
         queue1 2 (ropes-max))
        (ropes-string-equal-p
         (ropes-string-of-queue queue1)
         (ropes-string-app
          (ropes-string-of-queue queue)
          (ropes-rope-string source))))
       (ropes-fold-obligations-p
        queue1 source))))))

;; q is the universally quantified array initialized to Emp at every index
;; below max+1. The implication body is the exact exported balance VC.

(defun-sk ropes-initial-queue-universal-p
    (source upper)
  (forall (queue)
    (implies
     (ropes-rope-list-p queue)
     (implies
      (and
       (ropes-all-emp-p queue upper)
       (equal (len queue) upper))
      (and
       (< 2 (len queue))
       (equal
        (len queue)
        (+ (ropes-max) 1))
       (ropes-rope-inv-p source)
       (ropes-all-invariant-p
        queue 2 (ropes-max))
       (< (+ (ropes-string-length
              (ropes-string-of-queue queue))
             (ropes-rope-length source))
          (ropes-fib
           (+ (ropes-max) 1)))
       (ropes-insert-leaves-post-universal-p
        queue source))))))

(defun-sk
    ntp4vc-pearl-ropes-balance-balanceqtvc-statement ()
  (forall (source)
    (implies
     (and
      (ropes-background-p)
      (ropes-rope-p source)
      (ropes-rope-inv-p source)
      (< (ropes-rope-length source)
         (ropes-fib
          (+ (ropes-max) 1))))
     (let ((upper
            (+ (ropes-max) 1)))
       (and
        (<= 0 upper)
        (ropes-initial-queue-universal-p
         source upper))))))

(value-triple :itpeval-statement-checked)
:q
