;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_push_Why3_ide_VClist_push_contains_item_post_Unique_part4_goal43:
;; inequality of two final updated linked-list pointers at distinct indices
;; after havoc and pointer updates, under integer bounds, memory validity,
;; framing, separation, and uniqueness hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lp43-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lp43-address-base (address)
  (car address))

(defun lp43-address-offset (address)
  (cdr address))

(defun lp43-shift (address amount)
  (cons
   (lp43-address-base address)
   (+ (lp43-address-offset address) amount)))

(defun lp43-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2, t_3, and t_4, allocation function t, real-valued
;; memory t_1, region and linked operations, and l_index_of specialized to t_3.
;; Values of t_1 are used only through equality.  Since the address domain is
;; countable, arbitrary ACL2 values preserve exactly the equality patterns
;; realizable by a real-valued source function.

(defstub lp43-t2 (address) t)
(defstub lp43-t3 (address) t)
(defstub lp43-t4 (address) t)
(defstub lp43-a16 (address) t)
(defstub lp43-malloc (index) t)
(defstub lp43-t1 (address) t)
(defstub lp43-region (base) t)
(defstub lp43-linked-op () t)
(defstub lp43-l-index-of (item array down up) t)

(defun-sk lp43-pointer-functions-p ()
  (forall (address)
    (implies
     (lp43-address-p address)
     (and
      (lp43-address-p (lp43-t2 address))
      (lp43-address-p (lp43-t3 address))
      (lp43-address-p (lp43-t4 address))
      (lp43-address-p (lp43-a16 address))))))

(defun-sk lp43-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lp43-malloc index)))))

(defun-sk lp43-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lp43-region base)))))

(defun-sk lp43-l-index-of-type-p ()
  (forall (item array down up)
    (implies
     (and
      (lp43-address-p item)
      (lp43-address-p array)
      (integerp down)
      (integerp up))
     (integerp
      (lp43-l-index-of item array down up)))))

(defun lp43-linked-p ()
  (if (lp43-linked-op) t nil))

(defun lp43-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lp43-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lp43-address-base left)
     (lp43-address-base right)))
   (<=
    (+ (lp43-address-offset right) right-length)
    (lp43-address-offset left))
   (<=
    (+ (lp43-address-offset left) left-length)
    (lp43-address-offset right))))

(defun lp43-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lp43-address-base address))
    (<= 0 (lp43-address-offset address))
    (<=
     (+ (lp43-address-offset address) length)
     (lp43-malloc (lp43-address-base address))))))

(defun-sk lp43-framed-p ()
  (forall (address)
    (implies
     (lp43-address-p address)
     (<=
      (lp43-region
       (lp43-address-base (lp43-t3 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lp43-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lp43-address-p item)
      (lp43-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lp43-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lp43-t3 (lp43-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lp43-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lp43-t3 (lp43-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lp43-l-index-of item array (+ 1 down) up)
        (lp43-l-index-of item array down up)))))))

;; M is the two successive source functional updates of t_3.  The second
;; update has precedence even when the update addresses alias.

(defun lp43-m-read (a2 a a1 a10 address)
  (cond
   ((equal address (lp43-shift a10 0)) a1)
   ((equal address a2) a)
   (t (lp43-t3 address))))

;; A11 is the source havoc: outside the possibly modified interval it reads M,
;; and inside that interval it reads the arbitrary prior memory t_2.

(defun lp43-a11-read
    (a2 a a1 a10 havoc-start havoc-length address)
  (if
      (lp43-separated-p address 1 havoc-start havoc-length)
      (lp43-m-read a2 a a1 a10 address)
    (lp43-t2 address)))

;; A16 is the second source havoc. This extensional constraint makes the
;; conservative function symbol lp43-a16 exactly that let-bound map.

(defun-sk lp43-a16-definition-p
    (a2 a a1 a10 havoc-start havoc-length
        second-havoc-start second-havoc-length)
  (forall (address)
    (implies
     (lp43-address-p address)
     (equal
      (lp43-a16 address)
      (if
          (lp43-separated-p
           address 1 second-havoc-start second-havoc-length)
          (lp43-a11-read
           a2 a a1 a10 havoc-start havoc-length address)
        (lp43-t4 address))))))

;; A13 and A14 are the exact source functional updates, with the later update
;; taking precedence in each definition.

(defun lp43-a13-read
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 address)
  (declare
   (ignore a2 a a1 a10 havoc-start havoc-length))
  (cond
   ((equal address a8) a4)
   ((equal address (lp43-shift a4 0)) a12)
   (t (lp43-a16 address))))

(defun lp43-a14-read
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 address)
  (if (equal address a2)
      a4
    (lp43-a13-read
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address)))

(defun lp43-mptr-read
    (memory-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address)
  (cond
   ((equal memory-kind :t3)
    (lp43-t3 address))
   ((equal memory-kind :a11)
    (lp43-a11-read
     a2 a a1 a10 havoc-start havoc-length address))
   ((equal memory-kind :a16)
    (lp43-a16 address))
   ((equal memory-kind :a13)
    (lp43-a13-read
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address))
   ((equal memory-kind :a14)
    (lp43-a14-read
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address))
   (t nil)))

;; A true list of N successive roots is constructor evidence for the source
;; inductive p_linked_n relation.  The empty witness is exactly its bound
;; constructor; every cons cell is one cons constructor and advances both the
;; array index and next pointer.

(defun lp43-linked-steps-p
    (memory-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     roots root array index bound)
  (if (consp roots)
      (and
       (lp43-address-p root)
       (equal (car roots) root)
       (equal
        (lp43-mptr-read
         memory-kind
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         (lp43-shift array index))
        root)
       (lp43-valid-rw-p root 4)
       (lp43-linked-steps-p
        memory-kind
        a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8
        (cdr roots)
        (lp43-mptr-read
         memory-kind
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         (lp43-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lp43-p-linked-n-p
    (memory-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:t3 :a11 :a16))
     (lp43-address-p root)
     (lp43-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lp43-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lp43-linked-steps-p
      memory-kind
      a2 a a1 a10 havoc-start havoc-length
      a4 a12 a8
      roots root array index bound))))

;; This unfolds load_s1_list and eqs1_list.  Pointer fields are read through
;; the selected pointer memories and the three scalar fields through t_1.

(defun lp43-eqs1-loads-p
    (left-kind right-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     left-root right-root)
  (and
   (equal
    (lp43-mptr-read
     right-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     (lp43-shift right-root 0))
    (lp43-mptr-read
     left-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     (lp43-shift left-root 0)))
   (equal
    (lp43-t1 (lp43-shift right-root 1))
    (lp43-t1 (lp43-shift left-root 1)))
   (equal
    (lp43-t1 (lp43-shift right-root 2))
    (lp43-t1 (lp43-shift left-root 2)))
   (equal
    (lp43-t1 (lp43-shift right-root 3))
    (lp43-t1 (lp43-shift left-root 3)))))

;; This is p_unchanged with the common malloc and real-valued memories
;; specialized to t and t_1, but with both pointer memories left explicit.

(defun-sk lp43-unchanged-p
    (left-kind right-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lp43-shift array index))
          (left-address
           (lp43-mptr-read
            left-kind
            a2 a a1 a10 havoc-start havoc-length
            a4 a12 a8 slot))
          (right-address
           (lp43-mptr-read
            right-kind
            a2 a a1 a10 havoc-start havoc-length
            a4 a12 a8 slot)))
       (and
        (equal left-address right-address)
        (lp43-eqs1-loads-p
         left-kind right-kind
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         left-address right-address)
        (implies
         (lp43-valid-rw-p right-address 4)
         (lp43-valid-rw-p left-address 4)))))))

(defun-sk lp43-a4-in-t3-range-p
    (a4 array lower upper)
  (exists (index)
    (and
     (integerp index)
     (equal
      a4
      (lp43-t3 (lp43-shift array index)))
     (< index upper)
     (<= lower (+ 1 index)))))

(defun-sk lp43-a4-not-in-t3-range-p
    (a4 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< index upper)
      (<= lower (+ 1 index)))
     (not
      (equal
       a4
       (lp43-t3 (lp43-shift array index)))))))

(defun-sk lp43-array-swipe-left-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lp43-t3 (lp43-shift array (+ 1 index)))
      (lp43-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp43-shift array index))))))

;; When SHIFTEDP is nil this is i < upper; when it is true this is the
;; source's 2 + i <= upper branch.  Both branches retain lower <= 1 + i.

(defun lp43-range-index-p
    (index lower upper shiftedp)
  (and
   (integerp index)
   (<= lower (+ 1 index))
   (if shiftedp
       (<= (+ 2 index) upper)
     (< index upper))))

(defun-sk lp43-a11-not-a4-range-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 array lower upper shiftedp)
  (forall (index)
    (implies
     (lp43-range-index-p index lower upper shiftedp)
     (not
      (equal
       (lp43-a11-read
        a2 a a1 a10 havoc-start havoc-length
        (lp43-shift array index))
       a4)))))

(defun-sk lp43-a2-separated-a11-range-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper shiftedp)
  (forall (index)
    (implies
     (lp43-range-index-p index lower upper shiftedp)
     (lp43-separated-p
      a2 1
      (lp43-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp43-shift array index))
      4))))

(defun-sk lp43-a4-separated-a11-range-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 array lower upper shiftedp)
  (forall (index)
    (implies
     (lp43-range-index-p index lower upper shiftedp)
     (lp43-separated-p
      a4 4
      (lp43-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp43-shift array index))
      4))))

(defun-sk lp43-a11-range-separated-array-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper array-base shiftedp)
  (forall (index)
    (implies
     (lp43-range-index-p index lower upper shiftedp)
     (lp43-separated-p
      (lp43-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp43-shift array index))
      4 array-base 2147483646))))

(defun-sk lp43-a11-loads-equal-t3-successors-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= (+ 2 index) upper))
     (lp43-eqs1-loads-p
      :a11 :t3
      a2 a a1 a10 havoc-start havoc-length
      a4 a12 a8
      (lp43-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp43-shift array index))
      (lp43-t3
       (lp43-shift array (+ 1 index)))))))

(defun-sk lp43-a11-range-distinct-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper shiftedp)
  (forall (left-index right-index)
    (implies
     (and
      (lp43-range-index-p
       left-index lower upper shiftedp)
      (lp43-range-index-p
       right-index lower upper shiftedp)
      (not (equal left-index right-index)))
     (not
      (equal
       (lp43-a11-read
        a2 a a1 a10 havoc-start havoc-length
        (lp43-shift array left-index))
       (lp43-a11-read
        a2 a a1 a10 havoc-start havoc-length
        (lp43-shift array right-index)))))))

(defun-sk lp43-a11-range-separated-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper shiftedp)
  (forall (left-index right-index)
    (implies
     (and
      (lp43-range-index-p
       left-index lower upper shiftedp)
      (lp43-range-index-p
       right-index lower upper shiftedp)
      (not (equal left-index right-index)))
     (lp43-separated-p
      (lp43-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp43-shift array left-index))
      4
      (lp43-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp43-shift array right-index))
      4))))

(defun-sk lp43-a2-separated-t3-range-p
    (a2 array lower upper)
  (forall (index)
    (implies
     (lp43-range-index-p index lower upper nil)
     (lp43-separated-p
      a2 1
      (lp43-t3 (lp43-shift array index))
      4))))

(defun-sk lp43-t3-range-separated-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (lp43-range-index-p index lower upper nil)
     (lp43-separated-p
      (lp43-t3 (lp43-shift array index))
      4 array-base 2147483646))))

(defun-sk lp43-a5-separated-t3-range-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (lp43-range-index-p index lower upper nil)
      (not
       (equal
        a5
        (lp43-t3 (lp43-shift array index)))))
     (lp43-separated-p
      a5 4
      (lp43-t3 (lp43-shift array index))
      4))))

(defun-sk lp43-a4-separated-t3-range-p
    (a4 array lower upper)
  (forall (index)
    (implies
     (and
      (lp43-range-index-p index lower upper nil)
      (not
       (equal
        a4
        (lp43-t3 (lp43-shift array index)))))
     (lp43-separated-p
      a4 4
      (lp43-t3 (lp43-shift array index))
      4))))

(defun-sk lp43-t3-range-distinct-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp43-range-index-p left-index lower upper nil)
      (lp43-range-index-p right-index lower upper nil)
      (not (equal left-index right-index)))
     (not
      (equal
       (lp43-t3 (lp43-shift array left-index))
       (lp43-t3 (lp43-shift array right-index)))))))

(defun-sk lp43-t3-range-separated-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp43-range-index-p left-index lower upper nil)
      (lp43-range-index-p right-index lower upper nil)
      (not (equal left-index right-index)))
     (lp43-separated-p
      (lp43-t3 (lp43-shift array left-index))
      4
      (lp43-t3 (lp43-shift array right-index))
      4))))

(defun-sk lp43-a2-separated-a16-range-p
    (a2 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lp43-separated-p
      a2 1
      (lp43-a16 (lp43-shift array index))
      4))))

(defun-sk lp43-a16-range-separated-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lp43-separated-p
      (lp43-a16 (lp43-shift array index))
      4
      array-base
      2147483646))))

(defun-sk lp43-a16-range-separated-p
    (array lower upper)
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
     (lp43-separated-p
      (lp43-a16 (lp43-shift array left-index))
      4
      (lp43-a16 (lp43-shift array right-index))
      4))))

(defun-sk lp43-a16-range-distinct-p
    (array lower upper)
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
       (lp43-a16 (lp43-shift array left-index))
       (lp43-a16 (lp43-shift array right-index)))))))

(defun-sk lp43-array-swipe-right-a16-a11-p
    (a2 a a1 a10 havoc-start havoc-length
        array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lp43-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp43-shift array (- index 1)))
      (lp43-a16 (lp43-shift array index))))))

(defun lp43-goal43-instance-p
    (a3 i3 i2 i1 i a2 a a1 i5 i4)
   (implies
    (and
     (lp43-pointer-functions-p)
     (lp43-malloc-function-p)
     (lp43-region-function-p)
     (lp43-l-index-of-type-p)
     (lp43-l-index-of-laws-p)
     (lp43-address-p a3)
     (integerp i3)
     (integerp i2)
     (integerp i1)
     (integerp i)
     (lp43-address-p a2)
     (lp43-address-p a)
     (lp43-address-p a1)
     (integerp i5)
     (integerp i4))
    (let*
        ((a4 (lp43-t3 (lp43-shift a3 i3)))
         (a5 (lp43-t3 (lp43-shift a3 i2)))
         (x (- i1 1))
         (x1 (+ i i1))
         (x2 (lp43-l-index-of a4 a3 x x1))
         (x3 (+ 1 i))
         (a6 (lp43-shift a3 0))
         (a7 (lp43-t3 a2))
         (a8 (lp43-shift a3 x))
         (x4 (- x2 1))
         (a9 (lp43-shift a3 x4))
         (a10 (lp43-t3 a9))
         (havoc-start (lp43-shift a3 x2))
         (havoc-length (- (+ i i1) x2))
         (a12
          (lp43-a11-read
           a2 a a1 a10 havoc-start havoc-length a2))
         (in-range
          (lp43-a4-in-t3-range-p a4 a3 i1 x1))
         (not-in-range
          (lp43-a4-not-in-t3-range-p a4 a3 i1 x1)))
      (implies
      (and
        (lp43-a16-definition-p
         a2 a a1 a10 havoc-start havoc-length
         a8 x3)
        (not (equal i5 i4))
        (not (equal a4 (lp43-null-address)))
        (equal a4 a5)
        (equal x2 (lp43-l-index-of a5 a3 x x1))
        (not (equal x1 x2))
        (< 0 i1)
        (< i2 x1)
        (< i3 x1)
        (< i4 x1)
        (< i5 x1)
        (<= (lp43-region (lp43-address-base a2)) 0)
        (<= (lp43-region (lp43-address-base a3)) 0)
        (<= (lp43-region (lp43-address-base a4)) 0)
        (< x2 x1)
        (<= x2 x1)
        (<= -1 i)
        (<= i 2147483644)
        (<= x1 2147483645)
        (<= i1 (+ 1 i2))
        (<= i1 (+ 1 i3))
        (<= i1 (+ 1 i4))
        (<= i1 (+ 1 i5))
        (<= i1 (+ 1 x2))
        (lp43-framed-p)
        (lp43-linked-p)
        (lp43-is-sint32-p i)
        (lp43-is-sint32-p i1)
        (lp43-valid-rw-p a2 1)
        (lp43-is-sint32-p x)
        (lp43-is-sint32-p x3)
        (lp43-valid-rw-p a6 2147483646)
        (lp43-valid-rw-p a5 4)
        (lp43-separated-p a2 1 a6 2147483646)
        (lp43-separated-p a7 4 a6 2147483646)
        (lp43-separated-p a2 1 a5 4)
        (lp43-separated-p a5 4 a6 2147483646)
        (lp43-valid-rw-p a8 x3)
        (lp43-p-linked-n-p
         :t3
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a7 a3 x x3 (lp43-null-address))
        (lp43-is-sint32-p x2)
        (lp43-separated-p a12 4 a6 2147483646)
        (lp43-eqs1-loads-p
         :a11 :t3
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a4 a4)
        (lp43-unchanged-p
         :a14 :a13
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a3 x x1)
        (implies
         (and
          (<= i1 x2)
          in-range)
         (equal
          (lp43-a11-read
           a2 a a1 a10 havoc-start havoc-length a9)
          a10))
        (implies
         in-range
         (lp43-array-swipe-left-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a3 x2 (- (+ i i1) 1)))
        (implies
         not-in-range
         (lp43-a11-not-a4-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 nil))
        (implies
         in-range
         (lp43-a11-not-a4-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 t))
        (implies
         in-range
         (lp43-p-linked-n-p
          :a11
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a12 a3 x i (lp43-null-address)))
        (implies
         not-in-range
         (lp43-p-linked-n-p
          :a11
         a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a12 a3 x x3 (lp43-null-address)))
        (implies
         not-in-range
         (lp43-unchanged-p
          :a11 :t3
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a3 x x1))
        (implies
         in-range
         (lp43-unchanged-p
          :a11 :t3
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
          a3 x x4))
        (implies
         not-in-range
         (lp43-a2-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 nil))
        (implies
         in-range
         (lp43-a2-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 t))
        (implies
         not-in-range
         (lp43-a4-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 nil))
        (implies
         in-range
         (lp43-a4-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 t))
        (implies
         not-in-range
         (lp43-a11-range-separated-array-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 a6 nil))
        (implies
         in-range
         (lp43-a11-range-separated-array-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 a6 t))
        (implies
         in-range
         (lp43-a11-loads-equal-t3-successors-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a3 x2 x1))
        (implies
         not-in-range
         (lp43-a11-range-distinct-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 nil))
        (implies
         in-range
         (lp43-a11-range-distinct-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 t))
        (implies
         not-in-range
         (lp43-a11-range-separated-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 nil))
        (implies
         in-range
         (lp43-a11-range-separated-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 t))
        (lp43-a2-separated-t3-range-p
         a2 a3 i1 x1)
        (lp43-t3-range-separated-array-p
         a3 i1 x1 a6)
        (lp43-a5-separated-t3-range-p
         a5 a3 i1 x1)
        (lp43-a4-separated-t3-range-p
         a4 a3 i1 x1)
        (lp43-t3-range-distinct-p
         a3 i1 x1)
       (lp43-t3-range-separated-p
         a3 i1 x1)
        (equal (lp43-a16 a2) a12)
        (lp43-separated-p
         (lp43-a16 a2) 4 a6 2147483646)
        (lp43-a2-separated-a16-range-p
         a2 a3 i1 x1)
        (lp43-a16-range-separated-array-p
         a3 i1 x1 a6)
        (lp43-a16-range-separated-p
         a3 i1 x1)
        (lp43-a16-range-distinct-p
         a3 x x1)
        (lp43-array-swipe-right-a16-a11-p
         a2 a a1 a10 havoc-start havoc-length
         a3 i1 x1)
        (lp43-p-linked-n-p
         :a16
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a12 a3 i1 i (lp43-null-address)))
       (not
        (equal
        (lp43-a14-read
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         (lp43-shift a3 i5))
        (lp43-a14-read
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         (lp43-shift a3 i4))))))))

(defun-sk
    ntp4vc-list-push-contains-item-post-unique-part4-goal43-statement ()
  (forall
   (a3 i3 i2 i1 i a2 a a1 i5 i4)
   (lp43-goal43-instance-p
    a3 i3 i2 i1 i a2 a a1 i5 i4)))

(value-triple :itpeval-statement-checked)

:q
