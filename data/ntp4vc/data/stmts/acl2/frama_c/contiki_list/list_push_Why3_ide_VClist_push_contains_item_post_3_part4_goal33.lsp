;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_push_Why3_ide_VClist_push_contains_item_post_3_part4_goal33:
;; a rightward linked-list pointer-array swipe after havoc and pointer updates,
;; under integer bounds, memory validity, framing, separation, and uniqueness
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lp33-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lp33-address-base (address)
  (car address))

(defun lp33-address-offset (address)
  (cdr address))

(defun lp33-shift (address amount)
  (cons
   (lp33-address-base address)
   (+ (lp33-address-offset address) amount)))

(defun lp33-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2, t_3, and t_4, allocation function t, real-valued
;; memory t_1, region and linked operations, and l_index_of specialized to t_3.
;; Values of t_1 are used only through equality.  Since the address domain is
;; countable, arbitrary ACL2 values preserve exactly the equality patterns
;; realizable by a real-valued source function.

(defstub lp33-t2 (address) t)
(defstub lp33-t3 (address) t)
(defstub lp33-t4 (address) t)
(defstub lp33-a16 (address) t)
(defstub lp33-malloc (index) t)
(defstub lp33-t1 (address) t)
(defstub lp33-region (base) t)
(defstub lp33-linked-op () t)
(defstub lp33-l-index-of (item array down up) t)

(defun-sk lp33-pointer-functions-p ()
  (forall (address)
    (implies
     (lp33-address-p address)
     (and
      (lp33-address-p (lp33-t2 address))
      (lp33-address-p (lp33-t3 address))
      (lp33-address-p (lp33-t4 address))
      (lp33-address-p (lp33-a16 address))))))

(defun-sk lp33-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lp33-malloc index)))))

(defun-sk lp33-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lp33-region base)))))

(defun-sk lp33-l-index-of-type-p ()
  (forall (item array down up)
    (implies
     (and
      (lp33-address-p item)
      (lp33-address-p array)
      (integerp down)
      (integerp up))
     (integerp
      (lp33-l-index-of item array down up)))))

(defun lp33-linked-p ()
  (if (lp33-linked-op) t nil))

(defun lp33-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lp33-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lp33-address-base left)
     (lp33-address-base right)))
   (<=
    (+ (lp33-address-offset right) right-length)
    (lp33-address-offset left))
   (<=
    (+ (lp33-address-offset left) left-length)
    (lp33-address-offset right))))

(defun lp33-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lp33-address-base address))
    (<= 0 (lp33-address-offset address))
    (<=
     (+ (lp33-address-offset address) length)
     (lp33-malloc (lp33-address-base address))))))

(defun-sk lp33-framed-p ()
  (forall (address)
    (implies
     (lp33-address-p address)
     (<=
      (lp33-region
       (lp33-address-base (lp33-t3 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lp33-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lp33-address-p item)
      (lp33-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lp33-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lp33-t3 (lp33-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lp33-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lp33-t3 (lp33-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lp33-l-index-of item array (+ 1 down) up)
        (lp33-l-index-of item array down up)))))))

;; M is the two successive source functional updates of t_3.  The second
;; update has precedence even when the update addresses alias.

(defun lp33-m-read (a2 a a1 a10 address)
  (cond
   ((equal address (lp33-shift a10 0)) a1)
   ((equal address a2) a)
   (t (lp33-t3 address))))

;; A11 is the source havoc: outside the possibly modified interval it reads M,
;; and inside that interval it reads the arbitrary prior memory t_2.

(defun lp33-a11-read
    (a2 a a1 a10 havoc-start havoc-length address)
  (if
      (lp33-separated-p address 1 havoc-start havoc-length)
      (lp33-m-read a2 a a1 a10 address)
    (lp33-t2 address)))

;; A16 is the second source havoc. This extensional constraint makes the
;; conservative function symbol lp33-a16 exactly that let-bound map.

(defun-sk lp33-a16-definition-p
    (a2 a a1 a10 havoc-start havoc-length
        second-havoc-start second-havoc-length)
  (forall (address)
    (implies
     (lp33-address-p address)
     (equal
      (lp33-a16 address)
      (if
          (lp33-separated-p
           address 1 second-havoc-start second-havoc-length)
          (lp33-a11-read
           a2 a a1 a10 havoc-start havoc-length address)
        (lp33-t4 address))))))

;; A13 and A14 are the exact source functional updates, with the later update
;; taking precedence in each definition.

(defun lp33-a13-read
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 address)
  (declare
   (ignore a2 a a1 a10 havoc-start havoc-length))
  (cond
   ((equal address a8) a4)
   ((equal address (lp33-shift a4 0)) a12)
   (t (lp33-a16 address))))

(defun lp33-a14-read
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 address)
  (if (equal address a2)
      a4
    (lp33-a13-read
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address)))

(defun lp33-mptr-read
    (memory-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address)
  (cond
   ((equal memory-kind :t3)
    (lp33-t3 address))
   ((equal memory-kind :a11)
    (lp33-a11-read
     a2 a a1 a10 havoc-start havoc-length address))
   ((equal memory-kind :a16)
    (lp33-a16 address))
   ((equal memory-kind :a13)
    (lp33-a13-read
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address))
   ((equal memory-kind :a14)
    (lp33-a14-read
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 address))
   (t nil)))

;; A true list of N successive roots is constructor evidence for the source
;; inductive p_linked_n relation.  The empty witness is exactly its bound
;; constructor; every cons cell is one cons constructor and advances both the
;; array index and next pointer.

(defun lp33-linked-steps-p
    (memory-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     roots root array index bound)
  (if (consp roots)
      (and
       (lp33-address-p root)
       (equal (car roots) root)
       (equal
        (lp33-mptr-read
         memory-kind
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         (lp33-shift array index))
        root)
       (lp33-valid-rw-p root 4)
       (lp33-linked-steps-p
        memory-kind
        a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8
        (cdr roots)
        (lp33-mptr-read
         memory-kind
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         (lp33-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lp33-p-linked-n-p
    (memory-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:t3 :a11 :a16))
     (lp33-address-p root)
     (lp33-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lp33-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lp33-linked-steps-p
      memory-kind
      a2 a a1 a10 havoc-start havoc-length
      a4 a12 a8
      roots root array index bound))))

;; This unfolds load_s1_list and eqs1_list.  Pointer fields are read through
;; the selected pointer memories and the three scalar fields through t_1.

(defun lp33-eqs1-loads-p
    (left-kind right-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     left-root right-root)
  (and
   (equal
    (lp33-mptr-read
     right-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     (lp33-shift right-root 0))
    (lp33-mptr-read
     left-kind
     a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8
     (lp33-shift left-root 0)))
   (equal
    (lp33-t1 (lp33-shift right-root 1))
    (lp33-t1 (lp33-shift left-root 1)))
   (equal
    (lp33-t1 (lp33-shift right-root 2))
    (lp33-t1 (lp33-shift left-root 2)))
   (equal
    (lp33-t1 (lp33-shift right-root 3))
    (lp33-t1 (lp33-shift left-root 3)))))

;; This is p_unchanged with the common malloc and real-valued memories
;; specialized to t and t_1, but with both pointer memories left explicit.

(defun-sk lp33-unchanged-p
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
         ((slot (lp33-shift array index))
          (left-address
           (lp33-mptr-read
            left-kind
            a2 a a1 a10 havoc-start havoc-length
            a4 a12 a8 slot))
          (right-address
           (lp33-mptr-read
            right-kind
            a2 a a1 a10 havoc-start havoc-length
            a4 a12 a8 slot)))
       (and
        (equal left-address right-address)
        (lp33-eqs1-loads-p
         left-kind right-kind
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         left-address right-address)
        (implies
         (lp33-valid-rw-p right-address 4)
         (lp33-valid-rw-p left-address 4)))))))

(defun-sk lp33-a4-in-t3-range-p
    (a4 array lower upper)
  (exists (index)
    (and
     (integerp index)
     (equal
      a4
      (lp33-t3 (lp33-shift array index)))
     (< index upper)
     (<= lower (+ 1 index)))))

(defun-sk lp33-a4-not-in-t3-range-p
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
       (lp33-t3 (lp33-shift array index)))))))

(defun-sk lp33-array-swipe-left-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lp33-t3 (lp33-shift array (+ 1 index)))
      (lp33-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp33-shift array index))))))

(defun-sk lp33-array-swipe-right-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lp33-t3 (lp33-shift array (- index 1)))
      (lp33-a14-read
       a2 a a1 a10 havoc-start havoc-length
       a4 a12 a8
       (lp33-shift array index))))))

;; When SHIFTEDP is nil this is i < upper; when it is true this is the
;; source's 2 + i <= upper branch.  Both branches retain lower <= 1 + i.

(defun lp33-range-index-p
    (index lower upper shiftedp)
  (and
   (integerp index)
   (<= lower (+ 1 index))
   (if shiftedp
       (<= (+ 2 index) upper)
     (< index upper))))

(defun-sk lp33-a11-not-a4-range-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 array lower upper shiftedp)
  (forall (index)
    (implies
     (lp33-range-index-p index lower upper shiftedp)
     (not
      (equal
       (lp33-a11-read
        a2 a a1 a10 havoc-start havoc-length
        (lp33-shift array index))
       a4)))))

(defun-sk lp33-a2-separated-a11-range-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper shiftedp)
  (forall (index)
    (implies
     (lp33-range-index-p index lower upper shiftedp)
     (lp33-separated-p
      a2 1
      (lp33-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp33-shift array index))
      4))))

(defun-sk lp33-a4-separated-a11-range-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 array lower upper shiftedp)
  (forall (index)
    (implies
     (lp33-range-index-p index lower upper shiftedp)
     (lp33-separated-p
      a4 4
      (lp33-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp33-shift array index))
      4))))

(defun-sk lp33-a11-range-separated-array-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper array-base shiftedp)
  (forall (index)
    (implies
     (lp33-range-index-p index lower upper shiftedp)
     (lp33-separated-p
      (lp33-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp33-shift array index))
      4 array-base 2147483646))))

(defun-sk lp33-a11-loads-equal-t3-successors-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= (+ 2 index) upper))
     (lp33-eqs1-loads-p
      :a11 :t3
      a2 a a1 a10 havoc-start havoc-length
      a4 a12 a8
      (lp33-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp33-shift array index))
      (lp33-t3
       (lp33-shift array (+ 1 index)))))))

(defun-sk lp33-a11-range-distinct-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper shiftedp)
  (forall (left-index right-index)
    (implies
     (and
      (lp33-range-index-p
       left-index lower upper shiftedp)
      (lp33-range-index-p
       right-index lower upper shiftedp)
      (not (equal left-index right-index)))
     (not
      (equal
       (lp33-a11-read
        a2 a a1 a10 havoc-start havoc-length
        (lp33-shift array left-index))
       (lp33-a11-read
        a2 a a1 a10 havoc-start havoc-length
        (lp33-shift array right-index)))))))

(defun-sk lp33-a11-range-separated-p
    (a2 a a1 a10 havoc-start havoc-length
        array lower upper shiftedp)
  (forall (left-index right-index)
    (implies
     (and
      (lp33-range-index-p
       left-index lower upper shiftedp)
      (lp33-range-index-p
       right-index lower upper shiftedp)
      (not (equal left-index right-index)))
     (lp33-separated-p
      (lp33-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp33-shift array left-index))
      4
      (lp33-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp33-shift array right-index))
      4))))

(defun-sk lp33-a2-separated-t3-range-p
    (a2 array lower upper)
  (forall (index)
    (implies
     (lp33-range-index-p index lower upper nil)
     (lp33-separated-p
      a2 1
      (lp33-t3 (lp33-shift array index))
      4))))

(defun-sk lp33-t3-range-separated-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (lp33-range-index-p index lower upper nil)
     (lp33-separated-p
      (lp33-t3 (lp33-shift array index))
      4 array-base 2147483646))))

(defun-sk lp33-a5-separated-t3-range-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (lp33-range-index-p index lower upper nil)
      (not
       (equal
        a5
        (lp33-t3 (lp33-shift array index)))))
     (lp33-separated-p
      a5 4
      (lp33-t3 (lp33-shift array index))
      4))))

(defun-sk lp33-a4-separated-t3-range-p
    (a4 array lower upper)
  (forall (index)
    (implies
     (and
      (lp33-range-index-p index lower upper nil)
      (not
       (equal
        a4
        (lp33-t3 (lp33-shift array index)))))
     (lp33-separated-p
      a4 4
      (lp33-t3 (lp33-shift array index))
      4))))

(defun-sk lp33-t3-range-distinct-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp33-range-index-p left-index lower upper nil)
      (lp33-range-index-p right-index lower upper nil)
      (not (equal left-index right-index)))
     (not
      (equal
       (lp33-t3 (lp33-shift array left-index))
       (lp33-t3 (lp33-shift array right-index)))))))

(defun-sk lp33-t3-range-separated-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp33-range-index-p left-index lower upper nil)
      (lp33-range-index-p right-index lower upper nil)
      (not (equal left-index right-index)))
     (lp33-separated-p
      (lp33-t3 (lp33-shift array left-index))
      4
      (lp33-t3 (lp33-shift array right-index))
      4))))

(defun-sk lp33-a2-separated-a16-range-p
    (a2 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lp33-separated-p
      a2 1
      (lp33-a16 (lp33-shift array index))
      4))))

(defun-sk lp33-a16-range-separated-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lp33-separated-p
      (lp33-a16 (lp33-shift array index))
      4
      array-base
      2147483646))))

(defun-sk lp33-a16-range-separated-p
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
     (lp33-separated-p
      (lp33-a16 (lp33-shift array left-index))
      4
      (lp33-a16 (lp33-shift array right-index))
      4))))

(defun-sk lp33-a16-range-distinct-p
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
       (lp33-a16 (lp33-shift array left-index))
       (lp33-a16 (lp33-shift array right-index)))))))

(defun-sk lp33-array-swipe-right-a16-a11-p
    (a2 a a1 a10 havoc-start havoc-length
        array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lp33-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp33-shift array (- index 1)))
      (lp33-a16 (lp33-shift array index))))))

(defun ntp4vc-list-push-contains-item-post-3-part4-goal33-statement
    (a3 i3 i2 i1 i a2 a a1)
  (implies
    (and
     (lp33-pointer-functions-p)
     (lp33-malloc-function-p)
     (lp33-region-function-p)
     (lp33-l-index-of-type-p)
     (lp33-l-index-of-laws-p)
     (lp33-address-p a3)
     (integerp i3)
     (integerp i2)
     (integerp i1)
     (integerp i)
     (lp33-address-p a2)
     (lp33-address-p a)
     (lp33-address-p a1))
    (let*
        ((a4 (lp33-t3 (lp33-shift a3 i3)))
         (a5 (lp33-t3 (lp33-shift a3 i2)))
         (x (- i1 1))
         (x1 (+ i i1))
         (x2 (lp33-l-index-of a4 a3 x x1))
         (x3 (lp33-l-index-of a5 a3 x x1))
         (x4 (+ 1 i))
         (a6 (lp33-shift a3 0))
         (a7 (lp33-t3 a2))
         (a8 (lp33-shift a3 x))
         (x5 (- x2 1))
         (a9 (lp33-shift a3 x5))
         (a10 (lp33-t3 a9))
         (havoc-start (lp33-shift a3 x2))
         (havoc-length (- (+ i i1) x2))
         (a12
          (lp33-a11-read
           a2 a a1 a10 havoc-start havoc-length a2))
         (in-range
          (lp33-a4-in-t3-range-p a4 a3 i1 x1))
         (not-in-range
          (lp33-a4-not-in-t3-range-p a4 a3 i1 x1)))
      (implies
       (and
        (lp33-a16-definition-p
         a2 a a1 a10 havoc-start havoc-length
         a8 x4)
        (not (equal a4 (lp33-null-address)))
        (equal a4 a5)
        (equal x2 x3)
        (not (equal x1 x2))
        (< 0 i1)
        (< i2 x1)
        (< i3 x1)
        (<= (lp33-region (lp33-address-base a2)) 0)
        (<= (lp33-region (lp33-address-base a3)) 0)
        (<= (lp33-region (lp33-address-base a4)) 0)
        (< x2 x1)
        (<= x2 x1)
        (<= -1 i)
        (<= i 2147483644)
        (<= x1 2147483645)
        (<= i1 (+ 1 i2))
        (<= i1 (+ 1 i3))
        (<= i1 (+ 1 x2))
        (lp33-framed-p)
        (lp33-linked-p)
        (lp33-is-sint32-p i)
        (lp33-is-sint32-p i1)
        (lp33-valid-rw-p a2 1)
        (lp33-is-sint32-p x)
        (lp33-is-sint32-p x4)
        (lp33-valid-rw-p a6 2147483646)
        (lp33-valid-rw-p a5 4)
        (lp33-separated-p a2 1 a6 2147483646)
        (lp33-separated-p a7 4 a6 2147483646)
        (lp33-separated-p a2 1 a5 4)
        (lp33-separated-p a5 4 a6 2147483646)
        (lp33-valid-rw-p a8 x4)
        (lp33-p-linked-n-p
         :t3
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a7 a3 x x4 (lp33-null-address))
        (lp33-is-sint32-p x3)
        (lp33-is-sint32-p x2)
        (lp33-separated-p a12 4 a6 2147483646)
        (lp33-eqs1-loads-p
         :a11 :t3
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a4 a4)
        (lp33-unchanged-p
         :a14 :a13
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a3 x x1)
        (implies
         (and
          (<= i1 x2)
          in-range)
         (equal
          (lp33-a11-read
           a2 a a1 a10 havoc-start havoc-length a9)
          a10))
        (implies
         in-range
         (lp33-array-swipe-left-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a3 x2 (- (+ i i1) 1)))
        (implies
         not-in-range
         (lp33-a11-not-a4-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 nil))
        (implies
         in-range
         (lp33-a11-not-a4-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 t))
        (implies
         in-range
         (lp33-p-linked-n-p
          :a11
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a12 a3 x i (lp33-null-address)))
        (implies
         not-in-range
         (lp33-p-linked-n-p
          :a11
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a12 a3 x x4 (lp33-null-address)))
        (implies
         not-in-range
         (lp33-unchanged-p
          :a11 :t3
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a3 x x1))
        (implies
         in-range
         (lp33-unchanged-p
          :a11 :t3
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a3 x x5))
        (implies
         not-in-range
         (lp33-a2-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 nil))
        (implies
         in-range
         (lp33-a2-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 t))
        (implies
         not-in-range
         (lp33-a4-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 nil))
        (implies
         in-range
         (lp33-a4-separated-a11-range-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a3 i1 x1 t))
        (implies
         not-in-range
         (lp33-a11-range-separated-array-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 a6 nil))
        (implies
         in-range
         (lp33-a11-range-separated-array-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 a6 t))
        (implies
         in-range
         (lp33-a11-loads-equal-t3-successors-p
          a2 a a1 a10 havoc-start havoc-length
          a4 a12 a8
          a3 x2 x1))
        (implies
         not-in-range
         (lp33-a11-range-distinct-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 nil))
        (implies
         in-range
         (lp33-a11-range-distinct-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 t))
        (implies
         not-in-range
         (lp33-a11-range-separated-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 nil))
        (implies
         in-range
         (lp33-a11-range-separated-p
          a2 a a1 a10 havoc-start havoc-length
          a3 i1 x1 t))
        (lp33-a2-separated-t3-range-p
         a2 a3 i1 x1)
        (lp33-t3-range-separated-array-p
         a3 i1 x1 a6)
        (lp33-a5-separated-t3-range-p
         a5 a3 i1 x1)
        (lp33-a4-separated-t3-range-p
         a4 a3 i1 x1)
        (lp33-t3-range-distinct-p
         a3 i1 x1)
        (lp33-t3-range-separated-p
         a3 i1 x1)
        (equal (lp33-a16 a2) a12)
        (lp33-separated-p
         (lp33-a16 a2) 4 a6 2147483646)
        (lp33-a2-separated-a16-range-p
         a2 a3 i1 x1)
        (lp33-a16-range-separated-array-p
         a3 i1 x1 a6)
        (lp33-a16-range-separated-p
         a3 i1 x1)
        (lp33-a16-range-distinct-p
         a3 x x1)
        (lp33-array-swipe-right-a16-a11-p
         a2 a a1 a10 havoc-start havoc-length
         a3 i1 x1)
        (lp33-p-linked-n-p
         :a16
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8
         a12 a3 i1 i (lp33-null-address)))
       (lp33-array-swipe-right-p
        a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8
        a3 i1 (+ 1 x3))))))

(value-triple :itpeval-statement-checked)

:q
