;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_push_Why3_ide_VClist_push_contains_item_post_Separation_part4_goal39:
;; separation of a final updated linked-list pointer from the list array
;; after havoc and pointer updates, under integer bounds, memory validity,
;; framing, separation, and uniqueness hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lp39-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lp39-address-base (address)
  (car address))

(defun lp39-address-offset (address)
  (cdr address))

(defun lp39-shift (address amount)
  (cons
   (lp39-address-base address)
   (+ (lp39-address-offset address) amount)))

(defun lp39-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2, t_3, and t_4, allocation function t, real-valued
;; memory t_1, region and linked operations, and l_index_of specialized to t_3.
;; Values of t_1 are used only through equality.  Since the address domain is
;; countable, arbitrary ACL2 values preserve exactly the equality patterns
;; realizable by a real-valued source function.

(defstub lp39-t2 (address) t)
(defstub lp39-t3 (address) t)
(defstub lp39-t4 (address) t)
(defstub lp39-a16 (address) t)
(defstub lp39-malloc (index) t)
(defstub lp39-t1 (address) t)
(defstub lp39-region (base) t)
(defstub lp39-linked-op () t)
(defstub lp39-l-index-of (item array down up) t)

(defun-sk lp39-pointer-functions-p ()
  (forall (address)
    (implies
     (lp39-address-p address)
     (and
      (lp39-address-p (lp39-t2 address))
      (lp39-address-p (lp39-t3 address))
      (lp39-address-p (lp39-t4 address))
      (lp39-address-p (lp39-a16 address))))))

(defun-sk lp39-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lp39-malloc index)))))

(defun-sk lp39-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lp39-region base)))))

(defun-sk lp39-l-index-of-type-p ()
  (forall (item array down up)
    (implies
     (and
      (lp39-address-p item)
      (lp39-address-p array)
      (integerp down)
      (integerp up))
     (integerp
      (lp39-l-index-of item array down up)))))

(defun lp39-linked-p ()
  (if (lp39-linked-op) t nil))

(defun lp39-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lp39-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lp39-address-base left)
     (lp39-address-base right)))
   (<=
    (+ (lp39-address-offset right) right-length)
    (lp39-address-offset left))
   (<=
    (+ (lp39-address-offset left) left-length)
    (lp39-address-offset right))))

(defun lp39-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lp39-address-base address))
    (<= 0 (lp39-address-offset address))
    (<=
     (+ (lp39-address-offset address) length)
     (lp39-malloc (lp39-address-base address))))))

(defun-sk lp39-framed-p ()
  (forall (address)
    (implies
     (lp39-address-p address)
     (<=
      (lp39-region
       (lp39-address-base (lp39-t3 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lp39-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lp39-address-p item)
      (lp39-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lp39-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lp39-t3 (lp39-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lp39-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lp39-t3 (lp39-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lp39-l-index-of item array (+ 1 down) up)
        (lp39-l-index-of item array down up)))))))

;; M is the two successive source functional updates of t_3.  The second
;; update has precedence even when the update addresses alias.

(defun lp39-m-read (a2 a a1 a10 address)
  (cond
   ((equal address (lp39-shift a10 0)) a1)
   ((equal address a2) a)
   (t (lp39-t3 address))))

;; A11 is the source havoc: outside the possibly modified interval it reads M,
;; and inside that interval it reads the arbitrary prior memory t_2.

(defun lp39-a11-read
    (a2 a a1 a10 havoc-start havoc-length address)
  (if
      (lp39-separated-p address 1 havoc-start havoc-length)
      (lp39-m-read a2 a a1 a10 address)
    (lp39-t2 address)))

;; A16 is the second source havoc. This extensional constraint makes the
;; conservative function symbol lp39-a16 exactly that let-bound map.

(defun-sk lp39-a16-definition-p
    (a2 a a1 a10 havoc-start havoc-length
        second-havoc-start second-havoc-length)
  (forall (address)
    (implies
     (lp39-address-p address)
     (equal
      (lp39-a16 address)
      (if
          (lp39-separated-p
           address 1 second-havoc-start second-havoc-length)
          (lp39-a11-read
           a2 a a1 a10 havoc-start havoc-length address)
        (lp39-t4 address))))))

;; A13 and A14 are the exact source functional updates, with the later update
;; taking precedence in each definition.

(defun lp39-a13-read
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 address)
  (declare
   (ignore a2 a a1 a10 havoc-start havoc-length))
  (cond
   ((equal address a8) a4)
   ((equal address (lp39-shift a4 0)) a12)
   (t (lp39-a16 address))))

(defun lp39-a14-read
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 address)
  (if (equal address a2)
      a4
    (lp39-a13-read
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address)))

(defun lp39-mptr-read
    (memory-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address)
  (cond
   ((equal memory-kind :t3)
    (lp39-t3 address))
   ((equal memory-kind :a11)
    (lp39-a11-read
     a2 a a1 a10 havoc-start havoc-length address))
   ((equal memory-kind :a16)
    (lp39-a16 address))
   ((equal memory-kind :a13)
    (lp39-a13-read
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address))
   ((equal memory-kind :a14)
    (lp39-a14-read
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address))
   (t nil)))

;; A true list of N successive roots is constructor evidence for the source
;; inductive p_linked_n relation.  The empty witness is exactly its bound
;; constructor; every cons cell is one cons constructor and advances both the
;; array index and next pointer.

(defun lp39-linked-steps-p
    (memory-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     roots root array index bound)
  (if (consp roots)
      (and
       (lp39-address-p root)
       (equal (car roots) root)
       (equal
        (lp39-mptr-read
         memory-kind
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         (lp39-shift array index))
        root)
       (lp39-valid-rw-p root 4)
       (lp39-linked-steps-p
        memory-kind
        a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8
        (cdr roots)
        (lp39-mptr-read
         memory-kind
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         (lp39-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lp39-p-linked-n-p
    (memory-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:t3 :a11 :a16))
     (lp39-address-p root)
     (lp39-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lp39-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lp39-linked-steps-p
      memory-kind
      a2 a a1 a10 havoc-start havoc-length
      a4 a12 a8
      roots root array index bound))))

;; This unfolds load_s1_list and eqs1_list.  Pointer fields are read through
;; the selected pointer memories and the three scalar fields through t_1.

(defun lp39-eqs1-loads-p
    (left-kind right-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     left-root right-root)
  (and
   (equal
    (lp39-mptr-read
     right-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     (lp39-shift right-root 0))
    (lp39-mptr-read
     left-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     (lp39-shift left-root 0)))
   (equal
    (lp39-t1 (lp39-shift right-root 1))
    (lp39-t1 (lp39-shift left-root 1)))
   (equal
    (lp39-t1 (lp39-shift right-root 2))
    (lp39-t1 (lp39-shift left-root 2)))
   (equal
    (lp39-t1 (lp39-shift right-root 3))
    (lp39-t1 (lp39-shift left-root 3)))))

;; This is p_unchanged with the common malloc and real-valued memories
;; specialized to t and t_1, but with both pointer memories left explicit.

(defun-sk lp39-unchanged-p
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
         ((slot (lp39-shift array index))
          (left-address
           (lp39-mptr-read
            left-kind
            a2 a a1 a10 havoc-start havoc-length
            a4 a12 a8 slot))
          (right-address
           (lp39-mptr-read
            right-kind
            a2 a a1 a10 havoc-start havoc-length
            a4 a12 a8 slot)))
       (and
        (equal left-address right-address)
        (lp39-eqs1-loads-p
         left-kind right-kind
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         left-address right-address)
        (implies
         (lp39-valid-rw-p right-address 4)
         (lp39-valid-rw-p left-address 4)))))))

(defun-sk lp39-a4-in-t3-range-p
    (a4 array lower upper)
  (exists (index)
    (and
     (integerp index)
     (equal
      a4
      (lp39-t3 (lp39-shift array index)))
     (< index upper)
     (<= lower (+ 1 index)))))

(defun-sk lp39-a4-not-in-t3-range-p
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
       (lp39-t3 (lp39-shift array index)))))))

(defun-sk lp39-array-swipe-left-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lp39-t3 (lp39-shift array (+ 1 index)))
      (lp39-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp39-shift array index))))))

;; When SHIFTEDP is nil this is i < upper; when it is true this is the
;; source's 2 + i <= upper branch.  Both branches retain lower <= 1 + i.

(defun lp39-range-index-p
    (index lower upper shiftedp)
  (and
   (integerp index)
   (<= lower (+ 1 index))
   (if shiftedp
       (<= (+ 2 index) upper)
     (< index upper))))

(defun-sk lp39-a11-not-a4-range-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 array lower upper shiftedp)
  (forall (index)
    (implies
     (lp39-range-index-p index lower upper shiftedp)
     (not
      (equal
       (lp39-a11-read
        a2 a a1 a10 havoc-start havoc-length
        (lp39-shift array index))
       a4)))))

(defun-sk lp39-a2-separated-a11-range-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper shiftedp)
  (forall (index)
    (implies
     (lp39-range-index-p index lower upper shiftedp)
     (lp39-separated-p
      a2 1
      (lp39-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp39-shift array index))
      4))))

(defun-sk lp39-a4-separated-a11-range-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 array lower upper shiftedp)
  (forall (index)
    (implies
     (lp39-range-index-p index lower upper shiftedp)
     (lp39-separated-p
      a4 4
      (lp39-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp39-shift array index))
      4))))

(defun-sk lp39-a11-range-separated-array-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper array-base shiftedp)
  (forall (index)
    (implies
     (lp39-range-index-p index lower upper shiftedp)
     (lp39-separated-p
      (lp39-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp39-shift array index))
      4 array-base 2147483646))))

(defun-sk lp39-a11-loads-equal-t3-successors-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= (+ 2 index) upper))
     (lp39-eqs1-loads-p
      :a11 :t3
      a2 a a1 a10 havoc-start havoc-length
      a4 a12 a8
      (lp39-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp39-shift array index))
      (lp39-t3
       (lp39-shift array (+ 1 index)))))))

(defun-sk lp39-a11-range-distinct-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper shiftedp)
  (forall (left-index right-index)
    (implies
     (and
      (lp39-range-index-p
       left-index lower upper shiftedp)
      (lp39-range-index-p
       right-index lower upper shiftedp)
      (not (equal left-index right-index)))
     (not
      (equal
       (lp39-a11-read
        a2 a a1 a10 havoc-start havoc-length
        (lp39-shift array left-index))
       (lp39-a11-read
        a2 a a1 a10 havoc-start havoc-length
        (lp39-shift array right-index)))))))

(defun-sk lp39-a11-range-separated-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper shiftedp)
  (forall (left-index right-index)
    (implies
     (and
      (lp39-range-index-p
       left-index lower upper shiftedp)
      (lp39-range-index-p
       right-index lower upper shiftedp)
      (not (equal left-index right-index)))
     (lp39-separated-p
      (lp39-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp39-shift array left-index))
      4
      (lp39-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp39-shift array right-index))
      4))))

(defun-sk lp39-a2-separated-t3-range-p
    (a2 array lower upper)
  (forall (index)
    (implies
     (lp39-range-index-p index lower upper nil)
     (lp39-separated-p
      a2 1
      (lp39-t3 (lp39-shift array index))
      4))))

(defun-sk lp39-t3-range-separated-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (lp39-range-index-p index lower upper nil)
     (lp39-separated-p
      (lp39-t3 (lp39-shift array index))
      4 array-base 2147483646))))

(defun-sk lp39-a5-separated-t3-range-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (lp39-range-index-p index lower upper nil)
      (not
       (equal
        a5
        (lp39-t3 (lp39-shift array index)))))
     (lp39-separated-p
      a5 4
      (lp39-t3 (lp39-shift array index))
      4))))

(defun-sk lp39-a4-separated-t3-range-p
    (a4 array lower upper)
  (forall (index)
    (implies
     (and
      (lp39-range-index-p index lower upper nil)
      (not
       (equal
        a4
        (lp39-t3 (lp39-shift array index)))))
     (lp39-separated-p
      a4 4
      (lp39-t3 (lp39-shift array index))
      4))))

(defun-sk lp39-t3-range-distinct-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp39-range-index-p left-index lower upper nil)
      (lp39-range-index-p right-index lower upper nil)
      (not (equal left-index right-index)))
     (not
      (equal
       (lp39-t3 (lp39-shift array left-index))
       (lp39-t3 (lp39-shift array right-index)))))))

(defun-sk lp39-t3-range-separated-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp39-range-index-p left-index lower upper nil)
      (lp39-range-index-p right-index lower upper nil)
      (not (equal left-index right-index)))
     (lp39-separated-p
      (lp39-t3 (lp39-shift array left-index))
      4
      (lp39-t3 (lp39-shift array right-index))
      4))))

(defun-sk lp39-a2-separated-a16-range-p
    (a2 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lp39-separated-p
      a2 1
      (lp39-a16 (lp39-shift array index))
      4))))

(defun-sk lp39-a16-range-separated-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lp39-separated-p
      (lp39-a16 (lp39-shift array index))
      4
      array-base
      2147483646))))

(defun-sk lp39-a16-range-separated-p
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
     (lp39-separated-p
      (lp39-a16 (lp39-shift array left-index))
      4
      (lp39-a16 (lp39-shift array right-index))
      4))))

(defun-sk lp39-a16-range-distinct-p
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
       (lp39-a16 (lp39-shift array left-index))
       (lp39-a16 (lp39-shift array right-index)))))))

(defun-sk lp39-array-swipe-right-a16-a11-p
    (a2 a a1 a10 havoc-start havoc-length
        array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lp39-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp39-shift array (- index 1)))
      (lp39-a16 (lp39-shift array index))))))

(defun lp39-goal39-instance-p
    (a3 i3 i2 i1 i a2 a a1 i4)
   (implies
    (and
     (lp39-pointer-functions-p)
     (lp39-malloc-function-p)
     (lp39-region-function-p)
     (lp39-l-index-of-type-p)
     (lp39-l-index-of-laws-p)
     (lp39-address-p a3)
     (integerp i3)
     (integerp i2)
     (integerp i1)
     (integerp i)
     (lp39-address-p a2)
     (lp39-address-p a)
     (lp39-address-p a1)
     (integerp i4))
    (let*
        ((a4 (lp39-t3 (lp39-shift a3 i3)))
         (a5 (lp39-t3 (lp39-shift a3 i2)))
         (x (- i1 1))
         (x1 (+ i i1))
         (x2 (lp39-l-index-of a4 a3 x x1))
         (x3 (+ 1 i))
         (a6 (lp39-shift a3 0))
         (a7 (lp39-t3 a2))
         (a8 (lp39-shift a3 x))
         (x4 (- x2 1))
         (a9 (lp39-shift a3 x4))
         (a10 (lp39-t3 a9))
         (havoc-start (lp39-shift a3 x2))
         (havoc-length (- (+ i i1) x2))
         (a12
          (lp39-a11-read
           a2 a a1 a10 havoc-start havoc-length a2))
         (in-range
          (lp39-a4-in-t3-range-p a4 a3 i1 x1))
         (not-in-range
          (lp39-a4-not-in-t3-range-p a4 a3 i1 x1)))
      (implies
      (and
        (lp39-a16-definition-p
         a2 a a1 a10 havoc-start havoc-length
         a8 x3)
        (not (equal a4 (lp39-null-address)))
        (equal a4 a5)
        (equal x2 (lp39-l-index-of a5 a3 x x1))
        (not (equal x1 x2))
        (< 0 i1)
        (< i2 x1)
        (< i3 x1)
        (< i4 x1)
        (<= (lp39-region (lp39-address-base a2)) 0)
        (<= (lp39-region (lp39-address-base a3)) 0)
        (<= (lp39-region (lp39-address-base a4)) 0)
        (< x2 x1)
        (<= x2 x1)
        (<= -1 i)
        (<= i 2147483644)
        (<= x1 2147483645)
        (<= i1 (+ 1 i2))
        (<= i1 (+ 1 i3))
        (<= i1 (+ 1 i4))
        (<= i1 (+ 1 x2))
        (lp39-framed-p)
        (lp39-linked-p)
        (lp39-is-sint32-p i)
        (lp39-is-sint32-p i1)
        (lp39-valid-rw-p a2 1)
        (lp39-is-sint32-p x)
        (lp39-is-sint32-p x3)
        (lp39-valid-rw-p a6 2147483646)
        (lp39-valid-rw-p a5 4)
        (lp39-separated-p a2 1 a6 2147483646)
        (lp39-separated-p a7 4 a6 2147483646)
        (lp39-separated-p a2 1 a5 4)
        (lp39-separated-p a5 4 a6 2147483646)
        (lp39-valid-rw-p a8 x3)
        (lp39-p-linked-n-p
         :t3
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a7 a3 x x3 (lp39-null-address))
        (lp39-is-sint32-p x2)
        (lp39-separated-p a12 4 a6 2147483646)
        (lp39-eqs1-loads-p
         :a11 :t3
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a4 a4)
        (lp39-unchanged-p
         :a14 :a13
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a3 x x1)
        (implies
         (and
          (<= i1 x2)
          in-range)
         (equal
          (lp39-a11-read
           a2 a a1 a10 havoc-start havoc-length a9)
          a10))
        (implies
         in-range
         (lp39-array-swipe-left-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a3 x2 (- (+ i i1) 1)))
        (implies
         not-in-range
         (lp39-a11-not-a4-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 nil))
        (implies
         in-range
         (lp39-a11-not-a4-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 t))
        (implies
         in-range
         (lp39-p-linked-n-p
          :a11
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a12 a3 x i (lp39-null-address)))
        (implies
         not-in-range
         (lp39-p-linked-n-p
          :a11
         a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a12 a3 x x3 (lp39-null-address)))
        (implies
         not-in-range
         (lp39-unchanged-p
          :a11 :t3
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a3 x x1))
        (implies
         in-range
         (lp39-unchanged-p
          :a11 :t3
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
          a3 x x4))
        (implies
         not-in-range
         (lp39-a2-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 nil))
        (implies
         in-range
         (lp39-a2-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 t))
        (implies
         not-in-range
         (lp39-a4-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 nil))
        (implies
         in-range
         (lp39-a4-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 t))
        (implies
         not-in-range
         (lp39-a11-range-separated-array-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 a6 nil))
        (implies
         in-range
         (lp39-a11-range-separated-array-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 a6 t))
        (implies
         in-range
         (lp39-a11-loads-equal-t3-successors-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a3 x2 x1))
        (implies
         not-in-range
         (lp39-a11-range-distinct-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 nil))
        (implies
         in-range
         (lp39-a11-range-distinct-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 t))
        (implies
         not-in-range
         (lp39-a11-range-separated-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 nil))
        (implies
         in-range
         (lp39-a11-range-separated-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 t))
        (lp39-a2-separated-t3-range-p
         a2 a3 i1 x1)
        (lp39-t3-range-separated-array-p
         a3 i1 x1 a6)
        (lp39-a5-separated-t3-range-p
         a5 a3 i1 x1)
        (lp39-a4-separated-t3-range-p
         a4 a3 i1 x1)
        (lp39-t3-range-distinct-p
         a3 i1 x1)
       (lp39-t3-range-separated-p
         a3 i1 x1)
        (equal (lp39-a16 a2) a12)
        (lp39-separated-p
         (lp39-a16 a2) 4 a6 2147483646)
        (lp39-a2-separated-a16-range-p
         a2 a3 i1 x1)
        (lp39-a16-range-separated-array-p
         a3 i1 x1 a6)
        (lp39-a16-range-separated-p
         a3 i1 x1)
        (lp39-a16-range-distinct-p
         a3 x x1)
        (lp39-array-swipe-right-a16-a11-p
         a2 a a1 a10 havoc-start havoc-length
         a3 i1 x1)
        (lp39-p-linked-n-p
         :a16
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a12 a3 i1 i (lp39-null-address)))
       (lp39-separated-p
        (lp39-a14-read
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         (lp39-shift a3 i4))
        4
        a6
        2147483646)))))

(defun-sk
    ntp4vc-list-push-contains-item-post-separation-part4-goal39-statement ()
  (forall
   (a3 i3 i2 i1 i a2 a a1 i4)
   (lp39-goal39-instance-p
    a3 i3 i2 i1 i a2 a a1 i4)))

(value-triple :itpeval-statement-checked)

:q
