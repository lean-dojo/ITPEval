;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_push_Why3_ide_VClist_push_stmt_post_part1_goal44:
;; preservation of a linked-list array segment after ordered pointer updates,
;; a zero-length havoc, and a subsequent bounded havoc, under integer bounds,
;; memory validity, framing, separation, linkage, and uniqueness hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lp44-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lp44-address-base (address)
  (car address))

(defun lp44-address-offset (address)
  (cdr address))

;; Source shift and shift_ptr both add their integer offset directly to the
;; address offset; shift_ptr remains distinct to mirror pointer-array syntax.

(defun lp44-shift (address amount)
  (cons
   (lp44-address-base address)
   (+ (lp44-address-offset address) amount)))

(defun lp44-shift-ptr (address index)
  (lp44-shift address index))

(defun lp44-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2, t_3, and t_4, allocation function t, real-valued
;; memory
;; t_1, region and linked operations, and l_index_of specialized to t_3.
;; Values of t_1 are used only through equality. Since the address domain is
;; countable, arbitrary ACL2 values preserve exactly the equality patterns
;; realizable by a real-valued source function.

(defstub lp44-t2 (address) t)
(defstub lp44-t3 (address) t)
(defstub lp44-t4 (address) t)
(defstub lp44-malloc (index) t)
(defstub lp44-t1 (address) t)
(defstub lp44-region (base) t)
(defstub lp44-linked-op () t)
(defstub lp44-l-index-of (item array down up) t)

(defun-sk lp44-environment-types-p ()
  (forall (address index base item array down up)
    (and
     (implies
      (lp44-address-p address)
      (and
       (lp44-address-p (lp44-t2 address))
       (lp44-address-p (lp44-t3 address))
       (lp44-address-p (lp44-t4 address))))
     (implies
      (integerp index)
      (integerp (lp44-malloc index)))
     (implies
      (integerp base)
      (integerp (lp44-region base)))
     (implies
      (and
       (lp44-address-p item)
       (lp44-address-p array)
       (integerp down)
       (integerp up))
      (integerp
       (lp44-l-index-of item array down up))))))

(defun lp44-linked-p ()
  (if (lp44-linked-op) t nil))

(defun lp44-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lp44-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lp44-address-base left)
     (lp44-address-base right)))
   (<=
    (+ (lp44-address-offset right) right-length)
    (lp44-address-offset left))
   (<=
    (+ (lp44-address-offset left) left-length)
    (lp44-address-offset right))))

(defun lp44-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lp44-address-base address))
    (<= 0 (lp44-address-offset address))
    (<=
     (+ (lp44-address-offset address) length)
     (lp44-malloc (lp44-address-base address))))))

(defun-sk lp44-framed-p ()
  (forall (address)
    (implies
     (lp44-address-p address)
     (<=
      (lp44-region
       (lp44-address-base (lp44-t3 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lp44-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lp44-address-p item)
      (lp44-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lp44-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lp44-t3 (lp44-shift-ptr array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lp44-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lp44-t3 (lp44-shift-ptr array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lp44-l-index-of item array (+ 1 down) up)
        (lp44-l-index-of item array down up)))))))

;; M is the two successive source functional updates of t_3. The second
;; update has precedence even when the update addresses alias.

(defun lp44-m-read (a2 a a1 a9 address)
  (cond
   ((equal address (lp44-shift a9 0)) a1)
   ((equal address a2) a)
   (t (lp44-t3 address))))

;; A11 is the exact havoc access equation. Its source interval has length
;; zero, but retaining the equation exposes the original definition directly.

(defun lp44-a11-read
    (a2 a a1 a9 havoc-start address)
  (if
      (lp44-separated-p address 1 havoc-start 0)
      (lp44-m-read a2 a a1 a9 address)
    (lp44-t2 address)))

;; A14 is the second source havoc: outside its interval it reads A11, and
;; inside that interval it reads the arbitrary prior pointer memory t_4.

(defun lp44-a14-read
    (a2 a a1 a9 havoc-start
        second-havoc-start second-havoc-length address)
  (if
      (lp44-separated-p
       address 1 second-havoc-start second-havoc-length)
      (lp44-a11-read a2 a a1 a9 havoc-start address)
    (lp44-t4 address)))

;; A12 and FINAL are the successive functional updates from the source.
;; Later updates have precedence when update addresses alias.

(defun lp44-a12-read
    (a2 a a1 a9 havoc-start item a10 a7
        second-havoc-length address)
  (cond
   ((equal address a7) item)
   ((equal address (lp44-shift item 0)) a10)
   (t
    (lp44-a14-read
     a2 a a1 a9 havoc-start
     a7 second-havoc-length address))))

(defun lp44-final-read
    (a2 a a1 a9 havoc-start item a10 a7
        second-havoc-length address)
  (if (equal address a2)
      item
    (lp44-a12-read
     a2 a a1 a9 havoc-start item a10 a7
     second-havoc-length address)))

(defun lp44-mptr-read
    (memory-kind
     a2 a a1 a9 havoc-start item a10 a7
     second-havoc-length address)
  (cond
   ((equal memory-kind :t3)
    (lp44-t3 address))
   ((equal memory-kind :m)
    (lp44-m-read a2 a a1 a9 address))
   ((equal memory-kind :a11)
    (lp44-a11-read a2 a a1 a9 havoc-start address))
   ((equal memory-kind :a14)
    (lp44-a14-read
     a2 a a1 a9 havoc-start
     a7 second-havoc-length address))
   ((equal memory-kind :a12)
    (lp44-a12-read
     a2 a a1 a9 havoc-start item a10 a7
     second-havoc-length address))
   ((equal memory-kind :final)
    (lp44-final-read
     a2 a a1 a9 havoc-start item a10 a7
     second-havoc-length address))
   (t nil)))

;; A true list of N successive roots is constructor evidence for the source
;; inductive p_linked_n relation. The empty witness is its bound constructor;
;; each cons cell is one cons constructor.

(defun lp44-linked-steps-p
    (memory-kind
     a2 a a1 a9 havoc-start item a10 a7
     second-havoc-length
     roots root array index bound)
  (if (consp roots)
      (and
       (lp44-address-p root)
       (equal (car roots) root)
       (equal
        (lp44-mptr-read
         memory-kind
         a2 a a1 a9 havoc-start item a10 a7
         second-havoc-length
         (lp44-shift-ptr array index))
        root)
       (lp44-valid-rw-p root 4)
       (lp44-linked-steps-p
        memory-kind
        a2 a a1 a9 havoc-start item a10 a7
        second-havoc-length
        (cdr roots)
        (lp44-mptr-read
         memory-kind
         a2 a a1 a9 havoc-start item a10 a7
         second-havoc-length
         (lp44-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lp44-p-linked-n-p
    (memory-kind
     a2 a a1 a9 havoc-start item a10 a7
     second-havoc-length
     root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:t3 :a11 :a14))
     (lp44-address-p root)
     (lp44-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lp44-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lp44-linked-steps-p
      memory-kind
      a2 a a1 a9 havoc-start item a10 a7
      second-havoc-length
      roots root array index bound))))

;; This unfolds load_s1_list and eqs1_list. Pointer fields use the selected
;; pointer memories and the three scalar fields use t_1.

(defun lp44-eqs1-loads-p
    (left-kind right-kind
     a2 a a1 a9 havoc-start item a10 a7
     second-havoc-length
     left-root right-root)
  (and
   (equal
    (lp44-mptr-read
     right-kind
     a2 a a1 a9 havoc-start item a10 a7
     second-havoc-length
     (lp44-shift right-root 0))
    (lp44-mptr-read
     left-kind
     a2 a a1 a9 havoc-start item a10 a7
     second-havoc-length
     (lp44-shift left-root 0)))
   (equal
    (lp44-t1 (lp44-shift right-root 1))
    (lp44-t1 (lp44-shift left-root 1)))
   (equal
    (lp44-t1 (lp44-shift right-root 2))
    (lp44-t1 (lp44-shift left-root 2)))
   (equal
    (lp44-t1 (lp44-shift right-root 3))
    (lp44-t1 (lp44-shift left-root 3)))))

(defun-sk lp44-unchanged-p
    (left-kind right-kind
     a2 a a1 a9 havoc-start item a10 a7
     second-havoc-length
     array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lp44-shift-ptr array index))
          (left-address
           (lp44-mptr-read
            left-kind
            a2 a a1 a9 havoc-start item a10 a7
            second-havoc-length slot))
          (right-address
           (lp44-mptr-read
            right-kind
            a2 a a1 a9 havoc-start item a10 a7
            second-havoc-length slot)))
       (and
        (equal left-address right-address)
        (lp44-eqs1-loads-p
         left-kind right-kind
         a2 a a1 a9 havoc-start item a10 a7
         second-havoc-length
         left-address right-address)
        (implies
         (lp44-valid-rw-p right-address 4)
         (lp44-valid-rw-p left-address 4)))))))

(defun-sk lp44-item-in-range-p (item array lower upper)
  (exists (index)
    (and
     (integerp index)
     (equal
      (lp44-t3 (lp44-shift-ptr array index))
      item)
     (<= lower (+ 1 index))
     (<= (+ 2 index) upper))))

(defun lp44-range-index-p (index lower upper offset)
  (and
   (integerp index)
   (<= lower (+ 1 index))
   (<= (+ offset index) upper)))

(defun-sk lp44-no-item-range-p (item array lower upper)
  (forall (index)
    (implies
     (lp44-range-index-p index lower upper 2)
     (not
      (equal
       (lp44-t3 (lp44-shift-ptr array index))
       item)))))

(defun-sk lp44-m-range-property-p
    (property offset
     a2 a a1 a9 array lower upper item a5)
  (forall (index)
    (implies
     (lp44-range-index-p index lower upper offset)
     (let ((value
            (lp44-m-read
             a2 a a1 a9
             (lp44-shift-ptr array index))))
       (cond
        ((equal property :not-item)
         (not (equal value item)))
        ((equal property :separated-a2)
         (lp44-separated-p a2 1 value 4))
        ((equal property :separated-item)
         (lp44-separated-p item 4 value 4))
        ((equal property :separated-array)
         (lp44-separated-p value 4 a5 2147483646))
        (t nil))))))

(defun-sk lp44-m-pair-property-p
    (property offset
     a2 a a1 a9 array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp44-range-index-p left-index lower upper offset)
      (lp44-range-index-p right-index lower upper offset)
      (not (equal left-index right-index)))
     (let
         ((left
           (lp44-m-read
            a2 a a1 a9
            (lp44-shift-ptr array left-index)))
          (right
           (lp44-m-read
            a2 a a1 a9
            (lp44-shift-ptr array right-index))))
       (cond
        ((equal property :distinct)
         (not (equal left right)))
        ((equal property :separated)
         (lp44-separated-p left 4 right 4))
        (t nil))))))

(defun-sk lp44-array-swipe-left-p
    (a2 a a1 a9 havoc-start array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lp44-t3 (lp44-shift-ptr array (+ 1 index)))
      (lp44-a11-read
       a2 a a1 a9 havoc-start
       (lp44-shift-ptr array index))))))

(defun-sk lp44-successor-loads-p
    (a2 a a1 a9 havoc-start item a10 a7
        second-havoc-length array upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= upper (+ 1 index))
      (<= (+ 3 index) upper))
     (lp44-eqs1-loads-p
      :a11 :t3
      a2 a a1 a9 havoc-start item a10 a7
      second-havoc-length
      (lp44-m-read
       a2 a a1 a9
       (lp44-shift-ptr array index))
      (lp44-t3
       (lp44-shift-ptr array (+ 1 index)))))))

(defun-sk lp44-t3-range-property-p
    (property item a2 array lower upper a5)
  (forall (index)
    (implies
     (lp44-range-index-p index lower upper 2)
     (let ((value
            (lp44-t3 (lp44-shift-ptr array index))))
       (cond
        ((equal property :sint32-not-item)
         (implies
          (lp44-is-sint32-p index)
          (not (equal value item))))
        ((equal property :separated-a2)
         (lp44-separated-p a2 1 value 4))
        ((equal property :separated-array)
         (lp44-separated-p value 4 a5 2147483646))
        ((equal property :separated-item-if-different)
         (implies
          (not (equal value item))
          (lp44-separated-p item 4 value 4)))
        (t nil))))))

(defun-sk lp44-t3-pair-property-p
    (property array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp44-range-index-p left-index lower upper 2)
      (lp44-range-index-p right-index lower upper 2)
      (not (equal left-index right-index)))
     (let
         ((left
           (lp44-t3 (lp44-shift-ptr array left-index)))
          (right
           (lp44-t3 (lp44-shift-ptr array right-index))))
       (cond
        ((equal property :distinct)
         (not (equal left right)))
        ((equal property :separated)
         (lp44-separated-p left 4 right 4))
        (t nil))))))

;; These predicates encode the source's quantified invariants over A14,
;; retaining the two different lower bounds used for separation and
;; distinctness.

(defun-sk lp44-a14-range-property-p
    (property
     a2 a a1 a9 havoc-start a7 second-havoc-length
     array lower upper a5)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (let
         ((value
           (lp44-a14-read
            a2 a a1 a9 havoc-start
            a7 second-havoc-length
            (lp44-shift-ptr array index))))
       (cond
        ((equal property :separated-a2)
         (lp44-separated-p a2 1 value 4))
        ((equal property :separated-array)
         (lp44-separated-p value 4 a5 2147483646))
        (t nil))))))

(defun-sk lp44-a14-pair-property-p
    (property
     a2 a a1 a9 havoc-start a7 second-havoc-length
     array lower upper)
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
     (let
         ((left
           (lp44-a14-read
            a2 a a1 a9 havoc-start
            a7 second-havoc-length
            (lp44-shift-ptr array left-index)))
          (right
           (lp44-a14-read
            a2 a a1 a9 havoc-start
            a7 second-havoc-length
            (lp44-shift-ptr array right-index))))
       (cond
        ((equal property :distinct)
         (not (equal left right)))
        ((equal property :separated)
         (lp44-separated-p left 4 right 4))
        (t nil))))))

(defun-sk lp44-array-swipe-right-p
    (a2 a a1 a9 havoc-start a7 second-havoc-length
        array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lp44-a11-read
       a2 a a1 a9 havoc-start
       (lp44-shift-ptr array (- index 1)))
      (lp44-a14-read
       a2 a a1 a9 havoc-start
       a7 second-havoc-length
       (lp44-shift-ptr array index))))))

(defun
    ntp4vc-list-push-stmt-post-part1-goal44-instance-p
    (i1 i item array a2 a a1)
  (implies
   (and
    (lp44-environment-types-p)
    (lp44-l-index-of-laws-p)
    (integerp i1)
    (integerp i)
    (lp44-address-p item)
    (lp44-address-p array)
    (lp44-address-p a2)
    (lp44-address-p a)
    (lp44-address-p a1))
   (let*
       ((x (- i1 1))
        (x1 (- (+ i i1) 1))
        (x2 (lp44-l-index-of item array x x1))
        (x3 (+ i i1))
        (a5 (lp44-shift-ptr array 0))
        (a6 (lp44-t3 a2))
        (a7 (lp44-shift-ptr array x))
        (x4 (- (+ i i1) 2))
        (a8 (lp44-shift-ptr array x4))
        (a9 (lp44-t3 a8))
        (havoc-start (lp44-shift-ptr array x1))
        (second-havoc-length (+ 1 i))
        (a10 (lp44-m-read a2 a a1 a9 a2))
        (item-in-range
         (lp44-item-in-range-p item array i1 x3))
        (no-item-in-range
         (lp44-no-item-range-p item array i1 x3)))
     (implies
      (and
       (not (equal (lp44-null-address) item))
       (equal (+ 1 x2) x3)
       (< 0 i1)
       (<= 0 i)
       (<= (lp44-region (lp44-address-base a2)) 0)
       (<= (lp44-region (lp44-address-base item)) 0)
       (<= (lp44-region (lp44-address-base array)) 0)
       (<= i 2147483645)
       (<= x3 2147483646)
       (lp44-framed-p)
       (lp44-linked-p)
       (lp44-is-sint32-p i)
       (lp44-is-sint32-p i1)
       (lp44-valid-rw-p a2 1)
       (lp44-valid-rw-p item 4)
       (lp44-separated-p a2 1 item 4)
       (lp44-is-sint32-p x)
       (lp44-is-sint32-p x1)
       (lp44-valid-rw-p a5 2147483646)
       (lp44-separated-p a2 1 a5 2147483646)
       (lp44-separated-p item 4 a5 2147483646)
       (lp44-separated-p a6 4 a5 2147483646)
       (lp44-valid-rw-p a7 i)
       (lp44-p-linked-n-p
        :t3
        a2 a a1 a9 havoc-start item a10 a7
        second-havoc-length
        a6 array x i (lp44-null-address))
       (lp44-is-sint32-p x2)
       (lp44-separated-p a10 4 a5 2147483646)
       (lp44-eqs1-loads-p
        :a11 :t3
        a2 a a1 a9 havoc-start item a10 a7
        second-havoc-length
        item item)
       (implies
        (< 0 i)
        (implies
         item-in-range
         (equal
          (lp44-m-read a2 a a1 a9 a8)
          a9)))
       (implies
        no-item-in-range
        (lp44-m-range-property-p
         :not-item 2
         a2 a a1 a9 array i1 x3 item a5))
       (implies
        item-in-range
        (lp44-m-range-property-p
         :not-item 3
         a2 a a1 a9 array i1 x3 item a5))
       (implies
        item-in-range
        (lp44-array-swipe-left-p
         a2 a a1 a9 havoc-start array x1 x4))
       (implies
        no-item-in-range
        (lp44-m-range-property-p
         :separated-a2 2
         a2 a a1 a9 array i1 x3 item a5))
       (implies
        item-in-range
        (lp44-m-range-property-p
         :separated-a2 3
         a2 a a1 a9 array i1 x3 item a5))
       (implies
        no-item-in-range
        (lp44-m-range-property-p
         :separated-item 2
         a2 a a1 a9 array i1 x3 item a5))
       (implies
        item-in-range
        (lp44-m-range-property-p
         :separated-item 3
         a2 a a1 a9 array i1 x3 item a5))
       (implies
        no-item-in-range
        (lp44-m-range-property-p
         :separated-array 2
         a2 a a1 a9 array i1 x3 item a5))
       (implies
        item-in-range
        (lp44-m-range-property-p
         :separated-array 3
         a2 a a1 a9 array i1 x3 item a5))
       (implies
        no-item-in-range
        (lp44-p-linked-n-p
         :a11
         a2 a a1 a9 havoc-start item a10 a7
         second-havoc-length
         a10 array x i (lp44-null-address)))
       (implies
        item-in-range
        (lp44-p-linked-n-p
         :a11
         a2 a a1 a9 havoc-start item a10 a7
         second-havoc-length
         a10 array x (- i 1) (lp44-null-address)))
       (implies
        no-item-in-range
        (lp44-m-pair-property-p
         :distinct 2
         a2 a a1 a9 array i1 x3))
       (implies
        item-in-range
        (lp44-m-pair-property-p
         :distinct 3
         a2 a a1 a9 array i1 x3))
       (implies
        item-in-range
        (lp44-unchanged-p
         :a11 :t3
         a2 a a1 a9 havoc-start item a10 a7
         second-havoc-length
         array x x4))
       (implies
        no-item-in-range
        (lp44-unchanged-p
         :a11 :t3
         a2 a a1 a9 havoc-start item a10 a7
         second-havoc-length
         array x x1))
       (implies
        item-in-range
        (lp44-successor-loads-p
         a2 a a1 a9 havoc-start item a10 a7
         second-havoc-length
         array x3))
       (implies
        no-item-in-range
        (lp44-m-pair-property-p
         :separated 2
         a2 a a1 a9 array i1 x3))
       (implies
        item-in-range
        (lp44-m-pair-property-p
         :separated 3
         a2 a a1 a9 array i1 x3))
       (lp44-t3-range-property-p
        :sint32-not-item item a2 array i1 x3 a5)
       (lp44-t3-range-property-p
        :separated-a2 item a2 array i1 x3 a5)
       (lp44-t3-range-property-p
        :separated-array item a2 array i1 x3 a5)
       (lp44-t3-range-property-p
        :separated-item-if-different
        item a2 array i1 x3 a5)
       (lp44-t3-pair-property-p
        :distinct array i1 x3)
       (lp44-t3-pair-property-p
        :separated array i1 x3)
       (equal
        (lp44-a14-read
         a2 a a1 a9 havoc-start
         a7 second-havoc-length a2)
        a10)
       (lp44-separated-p
        (lp44-a14-read
         a2 a a1 a9 havoc-start
         a7 second-havoc-length a2)
        4 a5 2147483646)
       (lp44-a14-range-property-p
        :separated-a2
        a2 a a1 a9 havoc-start a7 second-havoc-length
        array i1 x3 a5)
       (lp44-a14-range-property-p
        :separated-array
        a2 a a1 a9 havoc-start a7 second-havoc-length
        array i1 x3 a5)
       (lp44-a14-pair-property-p
        :separated
        a2 a a1 a9 havoc-start a7 second-havoc-length
        array i1 x3)
       (lp44-a14-pair-property-p
        :distinct
        a2 a a1 a9 havoc-start a7 second-havoc-length
        array x x3)
       (lp44-array-swipe-right-p
        a2 a a1 a9 havoc-start a7 second-havoc-length
        array i1 x3)
       (lp44-p-linked-n-p
        :a14
        a2 a a1 a9 havoc-start item a10 a7
        second-havoc-length
        a10 array i1 i (lp44-null-address)))
      (lp44-unchanged-p
       :final :a12
       a2 a a1 a9 havoc-start item a10 a7
       second-havoc-length
       array x x3)))))

(defun-sk
    ntp4vc-list-push-stmt-post-part1-goal44-statement ()
  (forall
   (i1 i item array a2 a a1)
   (ntp4vc-list-push-stmt-post-part1-goal44-instance-p
    i1 i item array a2 a a1)))

(value-triple :itpeval-statement-checked)

:q
