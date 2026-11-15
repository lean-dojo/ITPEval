;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_add_Why3_ide_VClist_add_call_list_final_add_pre_Linked_2_part4_goal44:
;; preservation of a linked-list segment after a range havoc and pointer
;; update in the final list-add verification condition. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lag44-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lag44-address-base (address)
  (car address))

(defun lag44-address-offset (address)
  (cdr address))

(defun lag44-shift (address amount)
  (cons
   (lag44-address-base address)
   (+ (lag44-address-offset address) amount)))

(defun lag44-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2 and t_3, allocation function t, real-valued memory
;; t_1, region and linked operations, and l_index_of specialized to t_3.
;; The values of t_1 are only compared for equality in this VC.  An arbitrary
;; ACL2-valued function therefore preserves exactly the possible equality
;; patterns of a real-valued function on the countable address domain.

(defstub lag44-t2 (address) t)
(defstub lag44-t3 (address) t)
(defstub lag44-malloc (index) t)
(defstub lag44-t1 (address) t)
(defstub lag44-region (base) t)
(defstub lag44-linked-op () t)
(defstub lag44-l-index-of (item array down up) t)

(defun-sk lag44-pointer-functions-p ()
  (forall (address)
    (implies
     (lag44-address-p address)
     (and
      (lag44-address-p (lag44-t2 address))
      (lag44-address-p (lag44-t3 address))))))

(defun-sk lag44-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lag44-malloc index)))))

(defun-sk lag44-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lag44-region base)))))

(defun-sk lag44-l-index-of-type-p ()
  (forall (item array down up)
    (implies
     (and
      (lag44-address-p item)
      (lag44-address-p array)
      (integerp down)
      (integerp up))
     (integerp
      (lag44-l-index-of item array down up)))))

(defun lag44-linked-p ()
  (if (lag44-linked-op) t nil))

(defun lag44-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lag44-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lag44-address-base left)
     (lag44-address-base right)))
   (<=
    (+ (lag44-address-offset right) right-length)
    (lag44-address-offset left))
   (<=
    (+ (lag44-address-offset left) left-length)
    (lag44-address-offset right))))

(defun lag44-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lag44-address-base address))
    (<= 0 (lag44-address-offset address))
    (<=
     (+ (lag44-address-offset address) length)
     (lag44-malloc (lag44-address-base address))))))

;; These are exactly the three source axioms characterizing l_index_of for
;; the arbitrary pointer function t_3.

(defun-sk lag44-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lag44-address-p item)
      (lag44-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lag44-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lag44-t3 (lag44-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lag44-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lag44-t3 (lag44-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lag44-l-index-of item array (+ 1 down) up)
        (lag44-l-index-of item array down up)))))))

;; M is the two successive source functional updates of t_3.  The second
;; update has precedence even when the update addresses alias.

(defun lag44-m-read
    (a2 a a1 a5 address)
  (let ((second-update-address
         (lag44-shift (lag44-t3 a5) 0)))
    (cond
     ((equal address second-update-address) a1)
     ((equal address a2) a)
     (t (lag44-t3 address)))))

;; A7 is the source havoc: outside the possibly modified interval it reads M,
;; and inside that interval it reads the arbitrary prior memory t_2.

(defun lag44-a7-read
    (a2 a a1 a5 havoc-start havoc-length address)
  (if
      (lag44-separated-p address 1 havoc-start havoc-length)
      (lag44-m-read a2 a a1 a5 address)
    (lag44-t2 address)))

;; A8 is the exact functional update of A7 at shift(a4,0) with null.

(defun lag44-a8-read
    (a2 a a1 a5 havoc-start havoc-length a4 address)
  (if (equal address (lag44-shift a4 0))
      (lag44-null-address)
    (lag44-a7-read
     a2 a a1 a5 havoc-start havoc-length address)))

(defun lag44-mptr-read
    (memory-kind a2 a a1 a5 havoc-start havoc-length a4 address)
  (cond
   ((equal memory-kind :t3)
    (lag44-t3 address))
   ((equal memory-kind :a7)
    (lag44-a7-read
     a2 a a1 a5 havoc-start havoc-length address))
   ((equal memory-kind :a8)
    (lag44-a8-read
     a2 a a1 a5 havoc-start havoc-length a4 address))
   (t nil)))

;; A nonempty node list is constructor evidence for the source inductive
;; p_linked_n relation.  Each adjacent pair records one cons constructor.

(defun lag44-linked-path-steps-p
    (memory-kind a2 a a1 a5 havoc-start havoc-length a4
                 nodes array index)
  (if (and (consp nodes) (consp (cdr nodes)))
      (and
       (equal
        (lag44-mptr-read
         memory-kind a2 a a1 a5 havoc-start havoc-length a4
         (lag44-shift array index))
        (car nodes))
       (lag44-valid-rw-p (car nodes) 4)
       (equal
        (cadr nodes)
        (lag44-mptr-read
         memory-kind a2 a a1 a5 havoc-start havoc-length a4
         (lag44-shift (car nodes) 0)))
       (lag44-linked-path-steps-p
        memory-kind a2 a a1 a5 havoc-start havoc-length a4
        (cdr nodes) array (+ 1 index)))
    (and (consp nodes) (endp (cdr nodes)))))

(defun-sk lag44-p-linked-n-p
    (memory-kind a2 a a1 a5 havoc-start havoc-length a4
                 root array index n bound)
  (exists (nodes)
    (and
     (member-eq memory-kind '(:t3 :a7 :a8))
     (lag44-address-p root)
     (lag44-address-p array)
     (integerp index)
     (integerp n)
     (lag44-address-p bound)
     (true-listp nodes)
     (equal (len nodes) (+ 1 n))
     (equal (car nodes) root)
     (equal (car (last nodes)) bound)
     (if (equal n 0)
         (and
          (equal root bound)
          (<= 0 index)
          (<= index 2147483646))
       (and
        (< 0 n)
        (<= 0 index)
        (<= 0 (+ index n))
        (<= (+ index n) 2147483646)
        (lag44-linked-path-steps-p
         memory-kind a2 a a1 a5 havoc-start havoc-length a4
         nodes array index))))))

(defun-sk lag44-framed-p ()
  (forall (address)
    (implies
     (lag44-address-p address)
     (<=
      (lag44-region
       (lag44-address-base (lag44-t3 address)))
      0))))

;; This unfolds load_s1_list and eqs1_list.  Pointer fields are read through
;; the selected pointer memories and the three scalar fields through t_1.

(defun lag44-eqs1-loads-p
    (left-kind right-kind
               a2 a a1 a5 havoc-start havoc-length a4
               left-root right-root)
  (and
   (equal
    (lag44-mptr-read
     right-kind a2 a a1 a5 havoc-start havoc-length a4
     (lag44-shift right-root 0))
    (lag44-mptr-read
     left-kind a2 a a1 a5 havoc-start havoc-length a4
     (lag44-shift left-root 0)))
   (equal
    (lag44-t1 (lag44-shift right-root 1))
    (lag44-t1 (lag44-shift left-root 1)))
   (equal
    (lag44-t1 (lag44-shift right-root 2))
    (lag44-t1 (lag44-shift left-root 2)))
   (equal
    (lag44-t1 (lag44-shift right-root 3))
    (lag44-t1 (lag44-shift left-root 3)))))

(defun-sk lag44-a4-in-t3-closed-range-p
    (a4 array lower upper)
  (exists (index)
    (and
     (integerp index)
     (equal
      a4
      (lag44-t3 (lag44-shift array index)))
     (<= lower index)
     (<= index upper))))

(defun-sk lag44-a4-not-in-t3-closed-range-p
    (a4 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (not
      (equal
       a4
       (lag44-t3 (lag44-shift array index)))))))

(defun-sk lag44-array-swipe-left-p
    (a2 a a1 a5 havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lag44-t3 (lag44-shift array (+ 1 index)))
      (lag44-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag44-shift array index))))))

;; In p_unchanged both real-valued memories are t_1.  Once the selected
;; addresses are equal, the three scalar-field equalities are reflexive.  The
;; next-pointer equality and valid_rw implication remain explicit.

(defun-sk lag44-unchanged-p
    (a2 a a1 a5 havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lag44-shift array index))
          (left-address
           (lag44-a7-read
            a2 a a1 a5 havoc-start havoc-length slot))
          (right-address (lag44-t3 slot)))
       (and
        (equal left-address right-address)
        (equal
         (lag44-t3 (lag44-shift right-address 0))
         (lag44-a7-read
          a2 a a1 a5 havoc-start havoc-length
          (lag44-shift left-address 0)))
        (implies
         (lag44-valid-rw-p right-address 4)
         (lag44-valid-rw-p left-address 4)))))))

(defun-sk lag44-a7-not-a4-open-range-p
    (a2 a a1 a5 havoc-start havoc-length a4 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (not
      (equal
       (lag44-a7-read
        a2 a a1 a5 havoc-start havoc-length
        (lag44-shift array index))
       a4)))))

(defun-sk lag44-a7-not-a4-closed-range-p
    (a2 a a1 a5 havoc-start havoc-length a4 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (not
      (equal
       (lag44-a7-read
        a2 a a1 a5 havoc-start havoc-length
        (lag44-shift array index))
       a4)))))

(defun-sk lag44-a2-separated-a7-open-range-p
    (a2 a a1 a5 havoc-start havoc-length array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lag44-separated-p
      a2 1
      (lag44-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag44-shift array index))
      4))))

(defun-sk lag44-a2-separated-a7-closed-range-p
    (a2 a a1 a5 havoc-start havoc-length array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (lag44-separated-p
      a2 1
      (lag44-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag44-shift array index))
      4))))

(defun-sk lag44-a4-separated-a7-open-range-p
    (a2 a a1 a5 havoc-start havoc-length a4 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lag44-separated-p
      a4 4
      (lag44-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag44-shift array index))
      4))))

(defun-sk lag44-a4-separated-a7-closed-range-p
    (a2 a a1 a5 havoc-start havoc-length a4 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (lag44-separated-p
      a4 4
      (lag44-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag44-shift array index))
      4))))

(defun-sk lag44-a7-open-range-separated-array-p
    (a2 a a1 a5 havoc-start havoc-length
        array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lag44-separated-p
      (lag44-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag44-shift array index))
      4 array-base 2147483646))))

(defun-sk lag44-a7-closed-range-separated-array-p
    (a2 a a1 a5 havoc-start havoc-length
        array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (lag44-separated-p
      (lag44-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag44-shift array index))
      4 array-base 2147483646))))

(defun-sk lag44-a7-loads-equal-t3-successors-p
    (a2 a a1 a5 havoc-start havoc-length a4 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lag44-eqs1-loads-p
      :a7 :t3
      a2 a a1 a5 havoc-start havoc-length a4
      (lag44-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag44-shift array index))
      (lag44-t3
       (lag44-shift array (+ 1 index)))))))

(defun-sk lag44-a7-open-range-distinct-p
    (a2 a a1 a5 havoc-start havoc-length array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (<= lower right-index)
      (<= lower left-index)
      (< right-index upper)
      (< left-index upper))
     (not
      (equal
       (lag44-a7-read
        a2 a a1 a5 havoc-start havoc-length
        (lag44-shift array left-index))
       (lag44-a7-read
        a2 a a1 a5 havoc-start havoc-length
        (lag44-shift array right-index)))))))

(defun-sk lag44-a7-closed-range-distinct-p
    (a2 a a1 a5 havoc-start havoc-length array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (<= lower right-index)
      (<= lower left-index)
      (<= right-index upper)
      (<= left-index upper))
     (not
      (equal
       (lag44-a7-read
        a2 a a1 a5 havoc-start havoc-length
        (lag44-shift array left-index))
       (lag44-a7-read
        a2 a a1 a5 havoc-start havoc-length
        (lag44-shift array right-index)))))))

(defun-sk lag44-a7-open-range-separated-p
    (a2 a a1 a5 havoc-start havoc-length array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (<= lower right-index)
      (<= lower left-index)
      (< right-index upper)
      (< left-index upper))
     (lag44-separated-p
      (lag44-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag44-shift array left-index))
      4
      (lag44-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag44-shift array right-index))
      4))))

(defun-sk lag44-a7-closed-range-separated-p
    (a2 a a1 a5 havoc-start havoc-length array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (<= lower right-index)
      (<= lower left-index)
      (<= right-index upper)
      (<= left-index upper))
     (lag44-separated-p
      (lag44-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag44-shift array left-index))
      4
      (lag44-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag44-shift array right-index))
      4))))

(defun-sk lag44-a2-separated-t3-closed-range-p
    (a2 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (lag44-separated-p
      a2 1
      (lag44-t3 (lag44-shift array index))
      4))))

(defun-sk lag44-t3-closed-range-separated-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (lag44-separated-p
      (lag44-t3 (lag44-shift array index))
      4 array-base 2147483646))))

(defun-sk lag44-a4-separated-t3-closed-range-p
    (a4 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        a4
        (lag44-t3 (lag44-shift array index))))
      (<= lower index)
      (<= index upper))
     (lag44-separated-p
      a4 4
      (lag44-t3 (lag44-shift array index))
      4))))

(defun-sk lag44-t3-closed-range-distinct-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (<= lower right-index)
      (<= lower left-index)
      (<= right-index upper)
      (<= left-index upper))
     (not
      (equal
       (lag44-t3 (lag44-shift array left-index))
       (lag44-t3 (lag44-shift array right-index)))))))

(defun-sk lag44-t3-closed-range-separated-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (<= lower right-index)
      (<= lower left-index)
      (<= right-index upper)
      (<= left-index upper))
     (lag44-separated-p
      (lag44-t3 (lag44-shift array left-index))
      4
      (lag44-t3 (lag44-shift array right-index))
      4))))

(defun lag44-goal-body (a3 i2 i i1 a2 a a1)
  (let*
        ((a4 (lag44-t3 (lag44-shift a3 i2)))
         (x (+ 1 i i1))
         (x1 (lag44-l-index-of a4 a3 i1 x))
         (x2 (- x1 1))
         (a5 (lag44-shift a3 x2))
         (a6 (lag44-t3 a5))
         (havoc-start (lag44-shift a3 x1))
         (havoc-length (- x x1))
         (a9
          (lag44-a8-read
           a2 a a1 a5 havoc-start havoc-length a4 a2))
         (x3 (- (+ i i1) 1))
         (a10
          (lag44-a8-read
           a2 a a1 a5 havoc-start havoc-length a4
           (lag44-shift a3 x3)))
         (x4 (+ i i1))
         (x5 (+ 1 i))
         (a11 (lag44-shift a3 0))
         (a12 (lag44-t3 a2))
         (a13
          (lag44-a7-read
           a2 a a1 a5 havoc-start havoc-length a2))
         (in-range
          (lag44-a4-in-t3-closed-range-p
           a4 a3 i1 x4))
         (not-in-range
          (lag44-a4-not-in-t3-closed-range-p
           a4 a3 i1 x4)))
      (implies
       (and
        (not (equal a4 (lag44-null-address)))
        (not (equal x x1))
        (not (equal a9 (lag44-null-address)))
        (not (equal a10 (lag44-null-address)))
        (<= 0 i1)
        (<= i1 i2)
        (<= i2 x4)
        (<= (lag44-region (lag44-address-base a2)) 0)
        (<= (lag44-region (lag44-address-base a3)) 0)
        (<= (lag44-region (lag44-address-base a4)) 0)
        (<= i1 x1)
        (<= x1 x4)
        (<= -1 i)
        (<= i 2147483644)
        (<= i1 2147483645)
        (<= x4 2147483644)
        (<= x1 x)
        (lag44-framed-p)
        (lag44-linked-p)
        (lag44-is-sint32-p i)
        (lag44-is-sint32-p i1)
        (lag44-valid-rw-p a2 1)
        (lag44-is-sint32-p x5)
        (lag44-valid-rw-p a11 2147483646)
        (lag44-valid-rw-p (lag44-shift a3 i1) x5)
        (lag44-valid-rw-p a4 4)
        (lag44-separated-p a2 1 a11 2147483646)
        (lag44-separated-p a12 4 a11 2147483646)
        (lag44-separated-p a2 1 a4 4)
        (lag44-separated-p a4 4 a11 2147483646)
        (lag44-p-linked-n-p
         :t3 a2 a a1 a5 havoc-start havoc-length a4
         a12 a3 i1 x5 (lag44-null-address))
        (lag44-is-sint32-p x1)
        (lag44-separated-p a13 4 a11 2147483646)
        (lag44-eqs1-loads-p
         :a7 :t3
         a2 a a1 a5 havoc-start havoc-length a4
         a4 a4)
        (lag44-p-linked-n-p
         :a8 a2 a a1 a5 havoc-start havoc-length a4
         a9 a3 i1 i (lag44-null-address))
        (lag44-p-linked-n-p
         :a8 a2 a a1 a5 havoc-start havoc-length a4
         a9 a3 i1 (- i 1) a10)
        (implies
         (and (< i1 x1) in-range)
         (equal
          (lag44-a7-read
           a2 a a1 a5 havoc-start havoc-length a5)
          a6))
        (implies
         in-range
         (lag44-array-swipe-left-p
          a2 a a1 a5 havoc-start havoc-length
          a3 x1 x4))
        (implies
         in-range
         (lag44-a7-not-a4-open-range-p
          a2 a a1 a5 havoc-start havoc-length
          a4 a3 i1 x4))
        (implies
         not-in-range
         (lag44-a7-not-a4-closed-range-p
          a2 a a1 a5 havoc-start havoc-length
          a4 a3 i1 x4))
        (implies
         in-range
         (lag44-p-linked-n-p
          :a7 a2 a a1 a5 havoc-start havoc-length a4
          a13 a3 i1 i (lag44-null-address)))
        (implies
         not-in-range
         (lag44-p-linked-n-p
          :a7 a2 a a1 a5 havoc-start havoc-length a4
          a13 a3 i1 x5 (lag44-null-address)))
        (implies
         not-in-range
         (lag44-unchanged-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x))
        (implies
         in-range
         (lag44-unchanged-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x2))
        (implies
         in-range
         (lag44-a2-separated-a7-open-range-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x4))
        (implies
         not-in-range
         (lag44-a2-separated-a7-closed-range-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x4))
        (implies
         in-range
         (lag44-a4-separated-a7-open-range-p
          a2 a a1 a5 havoc-start havoc-length
          a4 a3 i1 x4))
        (implies
         not-in-range
         (lag44-a4-separated-a7-closed-range-p
          a2 a a1 a5 havoc-start havoc-length
          a4 a3 i1 x4))
        (implies
         in-range
         (lag44-a7-open-range-separated-array-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x4 a11))
        (implies
         not-in-range
         (lag44-a7-closed-range-separated-array-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x4 a11))
        (implies
         in-range
         (lag44-a7-loads-equal-t3-successors-p
          a2 a a1 a5 havoc-start havoc-length
          a4 a3 x1 x4))
        (implies
         in-range
         (lag44-a7-open-range-distinct-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x4))
        (implies
         not-in-range
         (lag44-a7-closed-range-distinct-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x4))
        (implies
         in-range
         (lag44-a7-open-range-separated-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x4))
        (implies
         not-in-range
         (lag44-a7-closed-range-separated-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x4))
        (lag44-a2-separated-t3-closed-range-p
         a2 a3 i1 x4)
        (lag44-t3-closed-range-separated-array-p
         a3 i1 x4 a11)
        (lag44-a4-separated-t3-closed-range-p
         a4 a3 i1 x4)
        (lag44-t3-closed-range-distinct-p
         a3 i1 x4)
        (lag44-t3-closed-range-separated-p
         a3 i1 x4))
       (lag44-p-linked-n-p
        :a8 a2 a a1 a5 havoc-start havoc-length a4
        a10 a3 x3 1
        (lag44-a8-read
         a2 a a1 a5 havoc-start havoc-length a4
          (lag44-shift a10 0))))))

(defun-sk
    ntp4vc-list-add-call-list-final-add-pre-linked-2-part4-goal44-statement ()
  (forall
   (a3 i2 i i1 a2 a a1)
   (implies
    (and
     (lag44-pointer-functions-p)
     (lag44-malloc-function-p)
     (lag44-region-function-p)
     (lag44-l-index-of-type-p)
     (lag44-l-index-of-laws-p)
     (lag44-address-p a3)
     (integerp i2)
     (integerp i)
     (integerp i1)
     (lag44-address-p a2)
     (lag44-address-p a)
     (lag44-address-p a1))
    (lag44-goal-body a3 i2 i i1 a2 a a1))))

(value-triple :itpeval-statement-checked)

:q
