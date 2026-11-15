;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_add_Why3_ide_VClist_add_call_list_tail_pre_2_part4_goal33:
;; preservation of a linked-list segment after a range havoc and null-pointer
;; update under the list-add memory and separation invariants. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lag33-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lag33-address-base (address)
  (car address))

(defun lag33-address-offset (address)
  (cdr address))

(defun lag33-shift (address amount)
  (cons
   (lag33-address-base address)
   (+ (lag33-address-offset address) amount)))

(defun lag33-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2 and t_3, allocation function t, real-valued memory
;; t_1, region and linked operations, and l_index_of specialized to t_3.
;; Values of t_1 are only compared for equality in this VC.  Since the
;; address domain is countable, arbitrary ACL2 values preserve exactly the
;; equality patterns realizable by a real-valued function.

(defstub lag33-t2 (address) t)
(defstub lag33-t3 (address) t)
(defstub lag33-malloc (index) t)
(defstub lag33-t1 (address) t)
(defstub lag33-region (base) t)
(defstub lag33-linked-op () t)
(defstub lag33-l-index-of (item array down up) t)

(defun-sk lag33-pointer-functions-p ()
  (forall (address)
    (implies
     (lag33-address-p address)
     (and
      (lag33-address-p (lag33-t2 address))
      (lag33-address-p (lag33-t3 address))))))

(defun-sk lag33-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lag33-malloc index)))))

(defun-sk lag33-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lag33-region base)))))

(defun-sk lag33-l-index-of-type-p ()
  (forall (item array down up)
    (implies
     (and
      (lag33-address-p item)
      (lag33-address-p array)
      (integerp down)
      (integerp up))
     (integerp
      (lag33-l-index-of item array down up)))))

(defun lag33-linked-p ()
  (if (lag33-linked-op) t nil))

(defun lag33-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lag33-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lag33-address-base left)
     (lag33-address-base right)))
   (<=
    (+ (lag33-address-offset right) right-length)
    (lag33-address-offset left))
   (<=
    (+ (lag33-address-offset left) left-length)
    (lag33-address-offset right))))

(defun lag33-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lag33-address-base address))
    (<= 0 (lag33-address-offset address))
    (<=
     (+ (lag33-address-offset address) length)
     (lag33-malloc (lag33-address-base address))))))

;; These are exactly the three source axioms characterizing l_index_of for
;; the arbitrary pointer function t_3.

(defun-sk lag33-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lag33-address-p item)
      (lag33-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lag33-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lag33-t3 (lag33-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lag33-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lag33-t3 (lag33-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lag33-l-index-of item array (+ 1 down) up)
        (lag33-l-index-of item array down up)))))))

;; M is the two successive source functional updates of t_3.  The second
;; update has precedence even when the update addresses alias.

(defun lag33-m-read
    (a2 a a1 a5 address)
  (let ((second-update-address
         (lag33-shift (lag33-t3 a5) 0)))
    (cond
     ((equal address second-update-address) a1)
     ((equal address a2) a)
     (t (lag33-t3 address)))))

;; A7 is the source havoc: outside the possibly modified interval it reads M,
;; and inside that interval it reads the arbitrary prior memory t_2.

(defun lag33-a7-read
    (a2 a a1 a5 havoc-start havoc-length address)
  (if
      (lag33-separated-p address 1 havoc-start havoc-length)
      (lag33-m-read a2 a a1 a5 address)
    (lag33-t2 address)))

;; A8 is the exact functional update of A7 at shift(a4,0) with null.

(defun lag33-a8-read
    (a2 a a1 a5 havoc-start havoc-length a4 address)
  (if (equal address (lag33-shift a4 0))
      (lag33-null-address)
    (lag33-a7-read
     a2 a a1 a5 havoc-start havoc-length address)))

(defun lag33-mptr-read
    (memory-kind a2 a a1 a5 havoc-start havoc-length a4 address)
  (cond
   ((equal memory-kind :t3)
    (lag33-t3 address))
   ((equal memory-kind :a7)
    (lag33-a7-read
     a2 a a1 a5 havoc-start havoc-length address))
   ((equal memory-kind :a8)
    (lag33-a8-read
     a2 a a1 a5 havoc-start havoc-length a4 address))
   (t nil)))

;; A list of N successive roots is constructor evidence for the source
;; inductive p_linked_n relation.  The empty witness is exactly its bound
;; constructor; every cons cell is one cons constructor and advances both
;; the array index and next pointer.

(defun lag33-linked-steps-p
    (memory-kind a2 a a1 a5 havoc-start havoc-length a4
                 roots root array index bound)
  (if (consp roots)
      (and
       (lag33-address-p root)
       (equal (car roots) root)
       (equal
        (lag33-mptr-read
         memory-kind a2 a a1 a5 havoc-start havoc-length a4
         (lag33-shift array index))
        root)
       (lag33-valid-rw-p root 4)
       (lag33-linked-steps-p
        memory-kind a2 a a1 a5 havoc-start havoc-length a4
        (cdr roots)
        (lag33-mptr-read
         memory-kind a2 a a1 a5 havoc-start havoc-length a4
         (lag33-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lag33-p-linked-n-p
    (memory-kind a2 a a1 a5 havoc-start havoc-length a4
                 root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:t3 :a7 :a8))
     (lag33-address-p root)
     (lag33-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lag33-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lag33-linked-steps-p
      memory-kind a2 a a1 a5 havoc-start havoc-length a4
      roots root array index bound))))

(defun-sk lag33-framed-p ()
  (forall (address)
    (implies
     (lag33-address-p address)
     (<=
      (lag33-region
       (lag33-address-base (lag33-t3 address)))
      0))))

;; This unfolds load_s1_list and eqs1_list.  Pointer fields are read through
;; the selected pointer memories and the three scalar fields through t_1.

(defun lag33-eqs1-loads-p
    (left-kind right-kind
               a2 a a1 a5 havoc-start havoc-length a4
               left-root right-root)
  (and
   (equal
    (lag33-mptr-read
     right-kind a2 a a1 a5 havoc-start havoc-length a4
     (lag33-shift right-root 0))
    (lag33-mptr-read
     left-kind a2 a a1 a5 havoc-start havoc-length a4
     (lag33-shift left-root 0)))
   (equal
    (lag33-t1 (lag33-shift right-root 1))
    (lag33-t1 (lag33-shift left-root 1)))
   (equal
    (lag33-t1 (lag33-shift right-root 2))
    (lag33-t1 (lag33-shift left-root 2)))
   (equal
    (lag33-t1 (lag33-shift right-root 3))
    (lag33-t1 (lag33-shift left-root 3)))))

(defun-sk lag33-a4-in-t3-closed-range-p
    (a4 array lower upper)
  (exists (index)
    (and
     (integerp index)
     (equal
      a4
      (lag33-t3 (lag33-shift array index)))
     (<= lower index)
     (<= index upper))))

(defun-sk lag33-a4-not-in-t3-closed-range-p
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
       (lag33-t3 (lag33-shift array index)))))))

(defun-sk lag33-array-swipe-left-p
    (a2 a a1 a5 havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lag33-t3 (lag33-shift array (+ 1 index)))
      (lag33-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag33-shift array index))))))

;; In p_unchanged both real-valued memories are t_1.  Once the selected
;; addresses are equal, the three scalar-field equalities are reflexive.  The
;; next-pointer equality and valid_rw implication remain explicit.

(defun-sk lag33-unchanged-p
    (a2 a a1 a5 havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lag33-shift array index))
          (left-address
           (lag33-a7-read
            a2 a a1 a5 havoc-start havoc-length slot))
          (right-address (lag33-t3 slot)))
       (and
        (equal left-address right-address)
        (equal
         (lag33-t3 (lag33-shift right-address 0))
         (lag33-a7-read
          a2 a a1 a5 havoc-start havoc-length
          (lag33-shift left-address 0)))
        (implies
         (lag33-valid-rw-p right-address 4)
         (lag33-valid-rw-p left-address 4)))))))

(defun lag33-range-index-p (index lower upper closedp)
  (and
   (integerp index)
   (<= lower index)
   (if closedp
       (<= index upper)
     (< index upper))))

(defun-sk lag33-a7-not-a4-range-p
    (a2 a a1 a5 havoc-start havoc-length
        a4 array lower upper closedp)
  (forall (index)
    (implies
     (lag33-range-index-p index lower upper closedp)
     (not
      (equal
       (lag33-a7-read
        a2 a a1 a5 havoc-start havoc-length
        (lag33-shift array index))
       a4)))))

(defun-sk lag33-a2-separated-a7-range-p
    (a2 a a1 a5 havoc-start havoc-length
        array lower upper closedp)
  (forall (index)
    (implies
     (lag33-range-index-p index lower upper closedp)
     (lag33-separated-p
      a2 1
      (lag33-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag33-shift array index))
      4))))

(defun-sk lag33-a4-separated-a7-range-p
    (a2 a a1 a5 havoc-start havoc-length
        a4 array lower upper closedp)
  (forall (index)
    (implies
     (lag33-range-index-p index lower upper closedp)
     (lag33-separated-p
      a4 4
      (lag33-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag33-shift array index))
      4))))

(defun-sk lag33-a7-range-separated-array-p
    (a2 a a1 a5 havoc-start havoc-length
        array lower upper array-base closedp)
  (forall (index)
    (implies
     (lag33-range-index-p index lower upper closedp)
     (lag33-separated-p
      (lag33-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag33-shift array index))
      4 array-base 2147483646))))

(defun-sk lag33-a7-loads-equal-t3-successors-p
    (a2 a a1 a5 havoc-start havoc-length a4 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< index upper)
      (<= lower index))
     (lag33-eqs1-loads-p
      :a7 :t3
      a2 a a1 a5 havoc-start havoc-length a4
      (lag33-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag33-shift array index))
      (lag33-t3
       (lag33-shift array (+ 1 index)))))))

(defun-sk lag33-a7-range-distinct-p
    (a2 a a1 a5 havoc-start havoc-length
        array lower upper closedp)
  (forall (left-index right-index)
    (implies
     (and
      (lag33-range-index-p left-index lower upper closedp)
      (lag33-range-index-p right-index lower upper closedp)
      (not (equal left-index right-index)))
     (not
      (equal
       (lag33-a7-read
        a2 a a1 a5 havoc-start havoc-length
        (lag33-shift array left-index))
       (lag33-a7-read
        a2 a a1 a5 havoc-start havoc-length
        (lag33-shift array right-index)))))))

(defun-sk lag33-a7-range-separated-p
    (a2 a a1 a5 havoc-start havoc-length
        array lower upper closedp)
  (forall (left-index right-index)
    (implies
     (and
      (lag33-range-index-p left-index lower upper closedp)
      (lag33-range-index-p right-index lower upper closedp)
      (not (equal left-index right-index)))
     (lag33-separated-p
      (lag33-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag33-shift array left-index))
      4
      (lag33-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag33-shift array right-index))
      4))))

(defun-sk lag33-a2-separated-t3-closed-range-p
    (a2 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (lag33-separated-p
      a2 1
      (lag33-t3 (lag33-shift array index))
      4))))

(defun-sk lag33-t3-closed-range-separated-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (lag33-separated-p
      (lag33-t3 (lag33-shift array index))
      4 array-base 2147483646))))

(defun-sk lag33-a4-separated-t3-closed-range-p
    (a4 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        a4
        (lag33-t3 (lag33-shift array index))))
      (<= lower index)
      (<= index upper))
     (lag33-separated-p
      a4 4
      (lag33-t3 (lag33-shift array index))
      4))))

(defun-sk lag33-t3-closed-range-distinct-p
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
       (lag33-t3 (lag33-shift array left-index))
       (lag33-t3 (lag33-shift array right-index)))))))

(defun-sk lag33-t3-closed-range-separated-p
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
     (lag33-separated-p
      (lag33-t3 (lag33-shift array left-index))
      4
      (lag33-t3 (lag33-shift array right-index))
      4))))

(defun
    ntp4vc-list-add-call-list-tail-pre-2-part4-goal33-statement
    (a3 i2 i i1 a2 a a1)
   (implies
    (and
     (lag33-pointer-functions-p)
     (lag33-malloc-function-p)
     (lag33-region-function-p)
     (lag33-l-index-of-type-p)
     (lag33-l-index-of-laws-p)
     (lag33-address-p a3)
     (integerp i2)
     (integerp i)
     (integerp i1)
     (lag33-address-p a2)
     (lag33-address-p a)
     (lag33-address-p a1))
    (let*
        ((a4 (lag33-t3 (lag33-shift a3 i2)))
         (x (+ 1 i i1))
         (x1 (lag33-l-index-of a4 a3 i1 x))
         (x2 (- x1 1))
         (a5 (lag33-shift a3 x2))
         (a6 (lag33-t3 a5))
         (havoc-start (lag33-shift a3 x1))
         (havoc-length (- x x1))
         (a9
          (lag33-a8-read
           a2 a a1 a5 havoc-start havoc-length a4 a2))
         (x3 (+ i i1))
         (x4 (+ 1 i))
         (a11 (lag33-shift a3 0))
         (a12 (lag33-t3 a2))
         (a13
          (lag33-a7-read
           a2 a a1 a5 havoc-start havoc-length a2))
         (in-range
          (lag33-a4-in-t3-closed-range-p
           a4 a3 i1 x3))
         (not-in-range
          (lag33-a4-not-in-t3-closed-range-p
           a4 a3 i1 x3)))
      (implies
       (and
        (not (equal a4 (lag33-null-address)))
        (not (equal x x1))
        (not (equal a9 (lag33-null-address)))
        (<= 0 i1)
        (<= i1 i2)
        (<= i2 x3)
        (<= (lag33-region (lag33-address-base a2)) 0)
        (<= (lag33-region (lag33-address-base a3)) 0)
        (<= (lag33-region (lag33-address-base a4)) 0)
        (<= i1 x1)
        (<= x1 x3)
        (<= -1 i)
        (<= i 2147483644)
        (<= i1 2147483645)
        (<= x3 2147483644)
        (<= x1 x)
        (lag33-framed-p)
        (lag33-linked-p)
        (lag33-is-sint32-p i)
        (lag33-is-sint32-p i1)
        (lag33-valid-rw-p a2 1)
        (lag33-is-sint32-p x4)
        (lag33-valid-rw-p a11 2147483646)
        (lag33-valid-rw-p (lag33-shift a3 i1) x4)
        (lag33-valid-rw-p a4 4)
        (lag33-separated-p a2 1 a11 2147483646)
        (lag33-separated-p a12 4 a11 2147483646)
        (lag33-separated-p a2 1 a4 4)
        (lag33-separated-p a4 4 a11 2147483646)
        (lag33-p-linked-n-p
         :t3 a2 a a1 a5 havoc-start havoc-length a4
         a12 a3 i1 x4 (lag33-null-address))
        (lag33-is-sint32-p x1)
        (lag33-separated-p a13 4 a11 2147483646)
        (lag33-eqs1-loads-p
         :a7 :t3
         a2 a a1 a5 havoc-start havoc-length a4
         a4 a4)
        (implies
         (and (< i1 x1) in-range)
         (equal
          (lag33-a7-read
           a2 a a1 a5 havoc-start havoc-length a5)
          a6))
        (implies
         in-range
         (lag33-array-swipe-left-p
          a2 a a1 a5 havoc-start havoc-length
          a3 x1 x3))
        (implies
         in-range
         (lag33-a7-not-a4-range-p
          a2 a a1 a5 havoc-start havoc-length
          a4 a3 i1 x3 nil))
        (implies
         not-in-range
         (lag33-a7-not-a4-range-p
          a2 a a1 a5 havoc-start havoc-length
          a4 a3 i1 x3 t))
        (implies
         in-range
         (lag33-p-linked-n-p
          :a7 a2 a a1 a5 havoc-start havoc-length a4
          a13 a3 i1 i (lag33-null-address)))
        (implies
         not-in-range
         (lag33-p-linked-n-p
          :a7 a2 a a1 a5 havoc-start havoc-length a4
          a13 a3 i1 x4 (lag33-null-address)))
        (implies
         not-in-range
         (lag33-unchanged-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x))
        (implies
         in-range
         (lag33-unchanged-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x2))
        (implies
         in-range
         (lag33-a2-separated-a7-range-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 nil))
        (implies
         not-in-range
         (lag33-a2-separated-a7-range-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 t))
        (implies
         in-range
         (lag33-a4-separated-a7-range-p
          a2 a a1 a5 havoc-start havoc-length
          a4 a3 i1 x3 nil))
        (implies
         not-in-range
         (lag33-a4-separated-a7-range-p
          a2 a a1 a5 havoc-start havoc-length
          a4 a3 i1 x3 t))
        (implies
         in-range
         (lag33-a7-range-separated-array-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 a11 nil))
        (implies
         not-in-range
         (lag33-a7-range-separated-array-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 a11 t))
        (implies
         in-range
         (lag33-a7-loads-equal-t3-successors-p
          a2 a a1 a5 havoc-start havoc-length
          a4 a3 x1 x3))
        (implies
         in-range
         (lag33-a7-range-distinct-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 nil))
        (implies
         not-in-range
         (lag33-a7-range-distinct-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 t))
        (implies
         in-range
         (lag33-a7-range-separated-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 nil))
        (implies
         not-in-range
         (lag33-a7-range-separated-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 t))
        (lag33-a2-separated-t3-closed-range-p
         a2 a3 i1 x3)
        (lag33-t3-closed-range-separated-array-p
         a3 i1 x3 a11)
        (lag33-a4-separated-t3-closed-range-p
         a4 a3 i1 x3)
        (lag33-t3-closed-range-distinct-p
         a3 i1 x3)
        (lag33-t3-closed-range-separated-p
         a3 i1 x3))
       (lag33-p-linked-n-p
        :a8 a2 a a1 a5 havoc-start havoc-length a4
        a9 a3 i1 i (lag33-null-address))))))

(value-triple :itpeval-statement-checked)

:q
