;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_push_Why3_ide_VClist_push_contains_item_post_Separation_2_part4_goal41:
;; separation of two distinct final updated linked-list pointers after havoc
;; and pointer updates, under integer bounds, memory validity, framing,
;; separation, and uniqueness hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lp41-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lp41-address-base (address)
  (car address))

(defun lp41-address-offset (address)
  (cdr address))

(defun lp41-shift (address amount)
  (cons
   (lp41-address-base address)
   (+ (lp41-address-offset address) amount)))

(defun lp41-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2, t_3, and t_4, allocation function t, real-valued
;; memory t_1, region and linked operations, and l_index_of specialized to t_3.
;; Values of t_1 are used only through equality.  Since the address domain is
;; countable, arbitrary ACL2 values preserve exactly the equality patterns
;; realizable by a real-valued source function.

(defstub lp41-t2 (address) t)
(defstub lp41-t3 (address) t)
(defstub lp41-t4 (address) t)
(defstub lp41-a16 (address) t)
(defstub lp41-malloc (index) t)
(defstub lp41-t1 (address) t)
(defstub lp41-region (base) t)
(defstub lp41-linked-op () t)
(defstub lp41-l-index-of (item array down up) t)

(defun-sk lp41-pointer-functions-p ()
  (forall (address)
    (implies
     (lp41-address-p address)
     (and
      (lp41-address-p (lp41-t2 address))
      (lp41-address-p (lp41-t3 address))
      (lp41-address-p (lp41-t4 address))
      (lp41-address-p (lp41-a16 address))))))

(defun-sk lp41-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lp41-malloc index)))))

(defun-sk lp41-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lp41-region base)))))

(defun-sk lp41-l-index-of-type-p ()
  (forall (item array down up)
    (implies
     (and
      (lp41-address-p item)
      (lp41-address-p array)
      (integerp down)
      (integerp up))
     (integerp
      (lp41-l-index-of item array down up)))))

(defun lp41-linked-p ()
  (if (lp41-linked-op) t nil))

(defun lp41-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lp41-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lp41-address-base left)
     (lp41-address-base right)))
   (<=
    (+ (lp41-address-offset right) right-length)
    (lp41-address-offset left))
   (<=
    (+ (lp41-address-offset left) left-length)
    (lp41-address-offset right))))

(defun lp41-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lp41-address-base address))
    (<= 0 (lp41-address-offset address))
    (<=
     (+ (lp41-address-offset address) length)
     (lp41-malloc (lp41-address-base address))))))

(defun-sk lp41-framed-p ()
  (forall (address)
    (implies
     (lp41-address-p address)
     (<=
      (lp41-region
       (lp41-address-base (lp41-t3 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lp41-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lp41-address-p item)
      (lp41-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lp41-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lp41-t3 (lp41-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lp41-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lp41-t3 (lp41-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lp41-l-index-of item array (+ 1 down) up)
        (lp41-l-index-of item array down up)))))))

;; M is the two successive source functional updates of t_3.  The second
;; update has precedence even when the update addresses alias.

(defun lp41-m-read (a2 a a1 a10 address)
  (cond
   ((equal address (lp41-shift a10 0)) a1)
   ((equal address a2) a)
   (t (lp41-t3 address))))

;; A11 is the source havoc: outside the possibly modified interval it reads M,
;; and inside that interval it reads the arbitrary prior memory t_2.

(defun lp41-a11-read
    (a2 a a1 a10 havoc-start havoc-length address)
  (if
      (lp41-separated-p address 1 havoc-start havoc-length)
      (lp41-m-read a2 a a1 a10 address)
    (lp41-t2 address)))

;; A16 is the second source havoc. This extensional constraint makes the
;; conservative function symbol lp41-a16 exactly that let-bound map.

(defun-sk lp41-a16-definition-p
    (a2 a a1 a10 havoc-start havoc-length
        second-havoc-start second-havoc-length)
  (forall (address)
    (implies
     (lp41-address-p address)
     (equal
      (lp41-a16 address)
      (if
          (lp41-separated-p
           address 1 second-havoc-start second-havoc-length)
          (lp41-a11-read
           a2 a a1 a10 havoc-start havoc-length address)
        (lp41-t4 address))))))

;; A13 and A14 are the exact source functional updates, with the later update
;; taking precedence in each definition.

(defun lp41-a13-read
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 address)
  (declare
   (ignore a2 a a1 a10 havoc-start havoc-length))
  (cond
   ((equal address a8) a4)
   ((equal address (lp41-shift a4 0)) a12)
   (t (lp41-a16 address))))

(defun lp41-a14-read
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 address)
  (if (equal address a2)
      a4
    (lp41-a13-read
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address)))

(defun lp41-mptr-read
    (memory-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address)
  (cond
   ((equal memory-kind :t3)
    (lp41-t3 address))
   ((equal memory-kind :a11)
    (lp41-a11-read
     a2 a a1 a10 havoc-start havoc-length address))
   ((equal memory-kind :a16)
    (lp41-a16 address))
   ((equal memory-kind :a13)
    (lp41-a13-read
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address))
   ((equal memory-kind :a14)
    (lp41-a14-read
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address))
   (t nil)))

;; A true list of N successive roots is constructor evidence for the source
;; inductive p_linked_n relation.  The empty witness is exactly its bound
;; constructor; every cons cell is one cons constructor and advances both the
;; array index and next pointer.

(defun lp41-linked-steps-p
    (memory-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     roots root array index bound)
  (if (consp roots)
      (and
       (lp41-address-p root)
       (equal (car roots) root)
       (equal
        (lp41-mptr-read
         memory-kind
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         (lp41-shift array index))
        root)
       (lp41-valid-rw-p root 4)
       (lp41-linked-steps-p
        memory-kind
        a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8
        (cdr roots)
        (lp41-mptr-read
         memory-kind
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         (lp41-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lp41-p-linked-n-p
    (memory-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:t3 :a11 :a16))
     (lp41-address-p root)
     (lp41-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lp41-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lp41-linked-steps-p
      memory-kind
      a2 a a1 a10 havoc-start havoc-length
      a4 a12 a8
      roots root array index bound))))

;; This unfolds load_s1_list and eqs1_list.  Pointer fields are read through
;; the selected pointer memories and the three scalar fields through t_1.

(defun lp41-eqs1-loads-p
    (left-kind right-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     left-root right-root)
  (and
   (equal
    (lp41-mptr-read
     right-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     (lp41-shift right-root 0))
    (lp41-mptr-read
     left-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     (lp41-shift left-root 0)))
   (equal
    (lp41-t1 (lp41-shift right-root 1))
    (lp41-t1 (lp41-shift left-root 1)))
   (equal
    (lp41-t1 (lp41-shift right-root 2))
    (lp41-t1 (lp41-shift left-root 2)))
   (equal
    (lp41-t1 (lp41-shift right-root 3))
    (lp41-t1 (lp41-shift left-root 3)))))

;; This is p_unchanged with the common malloc and real-valued memories
;; specialized to t and t_1, but with both pointer memories left explicit.

(defun-sk lp41-unchanged-p
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
         ((slot (lp41-shift array index))
          (left-address
           (lp41-mptr-read
            left-kind
            a2 a a1 a10 havoc-start havoc-length
            a4 a12 a8 slot))
          (right-address
           (lp41-mptr-read
            right-kind
            a2 a a1 a10 havoc-start havoc-length
            a4 a12 a8 slot)))
       (and
        (equal left-address right-address)
        (lp41-eqs1-loads-p
         left-kind right-kind
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         left-address right-address)
        (implies
         (lp41-valid-rw-p right-address 4)
         (lp41-valid-rw-p left-address 4)))))))

(defun-sk lp41-a4-in-t3-range-p
    (a4 array lower upper)
  (exists (index)
    (and
     (integerp index)
     (equal
      a4
      (lp41-t3 (lp41-shift array index)))
     (< index upper)
     (<= lower (+ 1 index)))))

(defun-sk lp41-a4-not-in-t3-range-p
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
       (lp41-t3 (lp41-shift array index)))))))

(defun-sk lp41-array-swipe-left-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lp41-t3 (lp41-shift array (+ 1 index)))
      (lp41-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp41-shift array index))))))

;; When SHIFTEDP is nil this is i < upper; when it is true this is the
;; source's 2 + i <= upper branch.  Both branches retain lower <= 1 + i.

(defun lp41-range-index-p
    (index lower upper shiftedp)
  (and
   (integerp index)
   (<= lower (+ 1 index))
   (if shiftedp
       (<= (+ 2 index) upper)
     (< index upper))))

(defun-sk lp41-a11-not-a4-range-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 array lower upper shiftedp)
  (forall (index)
    (implies
     (lp41-range-index-p index lower upper shiftedp)
     (not
      (equal
       (lp41-a11-read
        a2 a a1 a10 havoc-start havoc-length
        (lp41-shift array index))
       a4)))))

(defun-sk lp41-a2-separated-a11-range-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper shiftedp)
  (forall (index)
    (implies
     (lp41-range-index-p index lower upper shiftedp)
     (lp41-separated-p
      a2 1
      (lp41-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp41-shift array index))
      4))))

(defun-sk lp41-a4-separated-a11-range-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 array lower upper shiftedp)
  (forall (index)
    (implies
     (lp41-range-index-p index lower upper shiftedp)
     (lp41-separated-p
      a4 4
      (lp41-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp41-shift array index))
      4))))

(defun-sk lp41-a11-range-separated-array-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper array-base shiftedp)
  (forall (index)
    (implies
     (lp41-range-index-p index lower upper shiftedp)
     (lp41-separated-p
      (lp41-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp41-shift array index))
      4 array-base 2147483646))))

(defun-sk lp41-a11-loads-equal-t3-successors-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= (+ 2 index) upper))
     (lp41-eqs1-loads-p
      :a11 :t3
      a2 a a1 a10 havoc-start havoc-length
      a4 a12 a8
      (lp41-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp41-shift array index))
      (lp41-t3
       (lp41-shift array (+ 1 index)))))))

(defun-sk lp41-a11-range-distinct-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper shiftedp)
  (forall (left-index right-index)
    (implies
     (and
      (lp41-range-index-p
       left-index lower upper shiftedp)
      (lp41-range-index-p
       right-index lower upper shiftedp)
      (not (equal left-index right-index)))
     (not
      (equal
       (lp41-a11-read
        a2 a a1 a10 havoc-start havoc-length
        (lp41-shift array left-index))
       (lp41-a11-read
        a2 a a1 a10 havoc-start havoc-length
        (lp41-shift array right-index)))))))

(defun-sk lp41-a11-range-separated-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper shiftedp)
  (forall (left-index right-index)
    (implies
     (and
      (lp41-range-index-p
       left-index lower upper shiftedp)
      (lp41-range-index-p
       right-index lower upper shiftedp)
      (not (equal left-index right-index)))
     (lp41-separated-p
      (lp41-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp41-shift array left-index))
      4
      (lp41-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp41-shift array right-index))
      4))))

(defun-sk lp41-a2-separated-t3-range-p
    (a2 array lower upper)
  (forall (index)
    (implies
     (lp41-range-index-p index lower upper nil)
     (lp41-separated-p
      a2 1
      (lp41-t3 (lp41-shift array index))
      4))))

(defun-sk lp41-t3-range-separated-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (lp41-range-index-p index lower upper nil)
     (lp41-separated-p
      (lp41-t3 (lp41-shift array index))
      4 array-base 2147483646))))

(defun-sk lp41-a5-separated-t3-range-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (lp41-range-index-p index lower upper nil)
      (not
       (equal
        a5
        (lp41-t3 (lp41-shift array index)))))
     (lp41-separated-p
      a5 4
      (lp41-t3 (lp41-shift array index))
      4))))

(defun-sk lp41-a4-separated-t3-range-p
    (a4 array lower upper)
  (forall (index)
    (implies
     (and
      (lp41-range-index-p index lower upper nil)
      (not
       (equal
        a4
        (lp41-t3 (lp41-shift array index)))))
     (lp41-separated-p
      a4 4
      (lp41-t3 (lp41-shift array index))
      4))))

(defun-sk lp41-t3-range-distinct-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp41-range-index-p left-index lower upper nil)
      (lp41-range-index-p right-index lower upper nil)
      (not (equal left-index right-index)))
     (not
      (equal
       (lp41-t3 (lp41-shift array left-index))
       (lp41-t3 (lp41-shift array right-index)))))))

(defun-sk lp41-t3-range-separated-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp41-range-index-p left-index lower upper nil)
      (lp41-range-index-p right-index lower upper nil)
      (not (equal left-index right-index)))
     (lp41-separated-p
      (lp41-t3 (lp41-shift array left-index))
      4
      (lp41-t3 (lp41-shift array right-index))
      4))))

(defun-sk lp41-a2-separated-a16-range-p
    (a2 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lp41-separated-p
      a2 1
      (lp41-a16 (lp41-shift array index))
      4))))

(defun-sk lp41-a16-range-separated-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lp41-separated-p
      (lp41-a16 (lp41-shift array index))
      4
      array-base
      2147483646))))

(defun-sk lp41-a16-range-separated-p
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
     (lp41-separated-p
      (lp41-a16 (lp41-shift array left-index))
      4
      (lp41-a16 (lp41-shift array right-index))
      4))))

(defun-sk lp41-a16-range-distinct-p
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
       (lp41-a16 (lp41-shift array left-index))
       (lp41-a16 (lp41-shift array right-index)))))))

(defun-sk lp41-array-swipe-right-a16-a11-p
    (a2 a a1 a10 havoc-start havoc-length
        array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lp41-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp41-shift array (- index 1)))
      (lp41-a16 (lp41-shift array index))))))

(defun lp41-goal41-instance-p
    (a3 i3 i2 i1 i a2 a a1 i5 i4)
   (implies
    (and
     (lp41-pointer-functions-p)
     (lp41-malloc-function-p)
     (lp41-region-function-p)
     (lp41-l-index-of-type-p)
     (lp41-l-index-of-laws-p)
     (lp41-address-p a3)
     (integerp i3)
     (integerp i2)
     (integerp i1)
     (integerp i)
     (lp41-address-p a2)
     (lp41-address-p a)
     (lp41-address-p a1)
     (integerp i5)
     (integerp i4))
    (let*
        ((a4 (lp41-t3 (lp41-shift a3 i3)))
         (a5 (lp41-t3 (lp41-shift a3 i2)))
         (x (- i1 1))
         (x1 (+ i i1))
         (x2 (lp41-l-index-of a4 a3 x x1))
         (x3 (+ 1 i))
         (a6 (lp41-shift a3 0))
         (a7 (lp41-t3 a2))
         (a8 (lp41-shift a3 x))
         (x4 (- x2 1))
         (a9 (lp41-shift a3 x4))
         (a10 (lp41-t3 a9))
         (havoc-start (lp41-shift a3 x2))
         (havoc-length (- (+ i i1) x2))
         (a12
          (lp41-a11-read
           a2 a a1 a10 havoc-start havoc-length a2))
         (in-range
          (lp41-a4-in-t3-range-p a4 a3 i1 x1))
         (not-in-range
          (lp41-a4-not-in-t3-range-p a4 a3 i1 x1)))
      (implies
      (and
        (lp41-a16-definition-p
         a2 a a1 a10 havoc-start havoc-length
         a8 x3)
        (not (equal i5 i4))
        (not (equal a4 (lp41-null-address)))
        (equal a4 a5)
        (equal x2 (lp41-l-index-of a5 a3 x x1))
        (not (equal x1 x2))
        (< 0 i1)
        (< i2 x1)
        (< i3 x1)
        (< i4 x1)
        (< i5 x1)
        (<= (lp41-region (lp41-address-base a2)) 0)
        (<= (lp41-region (lp41-address-base a3)) 0)
        (<= (lp41-region (lp41-address-base a4)) 0)
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
        (lp41-framed-p)
        (lp41-linked-p)
        (lp41-is-sint32-p i)
        (lp41-is-sint32-p i1)
        (lp41-valid-rw-p a2 1)
        (lp41-is-sint32-p x)
        (lp41-is-sint32-p x3)
        (lp41-valid-rw-p a6 2147483646)
        (lp41-valid-rw-p a5 4)
        (lp41-separated-p a2 1 a6 2147483646)
        (lp41-separated-p a7 4 a6 2147483646)
        (lp41-separated-p a2 1 a5 4)
        (lp41-separated-p a5 4 a6 2147483646)
        (lp41-valid-rw-p a8 x3)
        (lp41-p-linked-n-p
         :t3
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a7 a3 x x3 (lp41-null-address))
        (lp41-is-sint32-p x2)
        (lp41-separated-p a12 4 a6 2147483646)
        (lp41-eqs1-loads-p
         :a11 :t3
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a4 a4)
        (lp41-unchanged-p
         :a14 :a13
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a3 x x1)
        (implies
         (and
          (<= i1 x2)
          in-range)
         (equal
          (lp41-a11-read
           a2 a a1 a10 havoc-start havoc-length a9)
          a10))
        (implies
         in-range
         (lp41-array-swipe-left-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a3 x2 (- (+ i i1) 1)))
        (implies
         not-in-range
         (lp41-a11-not-a4-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 nil))
        (implies
         in-range
         (lp41-a11-not-a4-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 t))
        (implies
         in-range
         (lp41-p-linked-n-p
          :a11
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a12 a3 x i (lp41-null-address)))
        (implies
         not-in-range
         (lp41-p-linked-n-p
          :a11
         a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a12 a3 x x3 (lp41-null-address)))
        (implies
         not-in-range
         (lp41-unchanged-p
          :a11 :t3
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a3 x x1))
        (implies
         in-range
         (lp41-unchanged-p
          :a11 :t3
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
          a3 x x4))
        (implies
         not-in-range
         (lp41-a2-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 nil))
        (implies
         in-range
         (lp41-a2-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 t))
        (implies
         not-in-range
         (lp41-a4-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 nil))
        (implies
         in-range
         (lp41-a4-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 t))
        (implies
         not-in-range
         (lp41-a11-range-separated-array-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 a6 nil))
        (implies
         in-range
         (lp41-a11-range-separated-array-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 a6 t))
        (implies
         in-range
         (lp41-a11-loads-equal-t3-successors-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a3 x2 x1))
        (implies
         not-in-range
         (lp41-a11-range-distinct-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 nil))
        (implies
         in-range
         (lp41-a11-range-distinct-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 t))
        (implies
         not-in-range
         (lp41-a11-range-separated-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 nil))
        (implies
         in-range
         (lp41-a11-range-separated-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 t))
        (lp41-a2-separated-t3-range-p
         a2 a3 i1 x1)
        (lp41-t3-range-separated-array-p
         a3 i1 x1 a6)
        (lp41-a5-separated-t3-range-p
         a5 a3 i1 x1)
        (lp41-a4-separated-t3-range-p
         a4 a3 i1 x1)
        (lp41-t3-range-distinct-p
         a3 i1 x1)
       (lp41-t3-range-separated-p
         a3 i1 x1)
        (equal (lp41-a16 a2) a12)
        (lp41-separated-p
         (lp41-a16 a2) 4 a6 2147483646)
        (lp41-a2-separated-a16-range-p
         a2 a3 i1 x1)
        (lp41-a16-range-separated-array-p
         a3 i1 x1 a6)
        (lp41-a16-range-separated-p
         a3 i1 x1)
        (lp41-a16-range-distinct-p
         a3 x x1)
        (lp41-array-swipe-right-a16-a11-p
         a2 a a1 a10 havoc-start havoc-length
         a3 i1 x1)
        (lp41-p-linked-n-p
         :a16
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a12 a3 i1 i (lp41-null-address)))
       (lp41-separated-p
        (lp41-a14-read
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         (lp41-shift a3 i5))
        4
        (lp41-a14-read
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         (lp41-shift a3 i4))
        4)))))

(defun-sk
    ntp4vc-list-push-contains-item-post-separation-2-part4-goal41-statement ()
  (forall
   (a3 i3 i2 i1 i a2 a a1 i5 i4)
   (lp41-goal41-instance-p
    a3 i3 i2 i1 i a2 a a1 i5 i4)))

(value-triple :itpeval-statement-checked)

:q
