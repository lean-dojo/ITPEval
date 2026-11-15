;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_push_Why3_ide_VClist_push_does_not_contain_item_post_Separation_2_part1_goal56:
;; separation of two final updated linked-list pointers selected at distinct
;; integer array indices, after two pointer-memory havocs and pointer updates,
;; under bounds, validity, framing, linkage, and range-separation hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lp56-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lp56-address-base (address)
  (car address))

(defun lp56-address-offset (address)
  (cdr address))

(defun lp56-shift (address amount)
  (cons
   (lp56-address-base address)
   (+ (lp56-address-offset address) amount)))

(defun lp56-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2, t_3, and t_4, allocation function t, real-valued
;; memory t_1, region and linked operations, and l_index_of specialized to t_3.
;; Values of t_1 are used only through equality. Since the address domain is
;; countable, arbitrary ACL2 values preserve exactly the equality patterns
;; realizable by a real-valued source function.

(defstub lp56-t2 (address) t)
(defstub lp56-t3 (address) t)
(defstub lp56-t4 (address) t)
(defstub lp56-malloc (index) t)
(defstub lp56-t1 (address) t)
(defstub lp56-region (base) t)
(defstub lp56-linked-op () t)
(defstub lp56-l-index-of (item array down up) t)

(defun-sk lp56-pointer-functions-p ()
  (forall (address)
    (implies
     (lp56-address-p address)
     (and
      (lp56-address-p (lp56-t2 address))
      (lp56-address-p (lp56-t3 address))
      (lp56-address-p (lp56-t4 address))))))

(defun-sk lp56-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lp56-malloc index)))))

(defun-sk lp56-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lp56-region base)))))

(defun-sk lp56-l-index-of-type-p ()
  (forall (item array down up)
    (implies
     (and
      (lp56-address-p item)
      (lp56-address-p array)
      (integerp down)
      (integerp up))
     (integerp
      (lp56-l-index-of item array down up)))))

(defun lp56-linked-p ()
  (if (lp56-linked-op) t nil))

(defun lp56-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lp56-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lp56-address-base left)
     (lp56-address-base right)))
   (<=
    (+ (lp56-address-offset right) right-length)
    (lp56-address-offset left))
   (<=
    (+ (lp56-address-offset left) left-length)
    (lp56-address-offset right))))

(defun lp56-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lp56-address-base address))
    (<= 0 (lp56-address-offset address))
    (<=
     (+ (lp56-address-offset address) length)
     (lp56-malloc (lp56-address-base address))))))

(defun-sk lp56-framed-p ()
  (forall (address)
    (implies
     (lp56-address-p address)
     (<=
      (lp56-region
       (lp56-address-base (lp56-t3 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lp56-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lp56-address-p item)
      (lp56-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lp56-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lp56-t3 (lp56-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lp56-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lp56-t3 (lp56-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lp56-l-index-of item array (+ 1 down) up)
        (lp56-l-index-of item array down up)))))))

;; M is the two successive source functional updates of t_3. The second
;; update has precedence even when the update addresses alias.

(defun lp56-m-read
    (a2 a a1 update-target address)
  (cond
   ((equal address update-target) a1)
   ((equal address a2) a)
   (t (lp56-t3 address))))

;; A8 is the source havoc: outside the possibly modified interval it reads M,
;; and inside that interval it reads the arbitrary prior memory t_2.

(defun lp56-a8-read
    (a2 a a1 update-target
        havoc-start havoc-length address)
  (if
      (lp56-separated-p address 1 havoc-start havoc-length)
      (lp56-m-read a2 a a1 update-target address)
    (lp56-t2 address)))

;; A13 is the second source havoc: outside its interval it reads A8, and
;; inside it reads the arbitrary t_4. A10 and A11 are the subsequent source
;; functional updates, with the later update taking precedence.

(defun lp56-a13-read
    (a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length address)
  (if
      (lp56-separated-p
       address 1 second-havoc-start second-havoc-length)
      (lp56-a8-read
       a2 a a1 update-target havoc-start havoc-length address)
    (lp56-t4 address)))

(defun lp56-a10-read
    (a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a9 a7 address)
  (cond
   ((equal address a7) item)
   ((equal address (lp56-shift item 0)) a9)
   (t
    (lp56-a13-read
     a2 a a1 update-target
     havoc-start havoc-length
     second-havoc-start second-havoc-length address))))

(defun lp56-a11-read
    (a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a9 a7 address)
  (if (equal address a2)
      item
    (lp56-a10-read
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7 address)))

(defun lp56-mptr-read
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7 address)
  (declare (ignore item a9 a7))
  (cond
   ((equal memory-kind :t3)
    (lp56-t3 address))
   ((equal memory-kind :a8)
    (lp56-a8-read
     a2 a a1 update-target havoc-start havoc-length address))
   (t nil)))

(defun lp56-source-mptr-read
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7 address)
  (cond
   ((equal memory-kind :a13)
    (lp56-a13-read
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length address))
   ((equal memory-kind :a10)
    (lp56-a10-read
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7 address))
   ((equal memory-kind :a11)
    (lp56-a11-read
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7 address))
   (t nil)))

;; A true list of N successive roots is constructor evidence for the source
;; inductive p_linked_n relation. The empty witness is exactly its bound
;; constructor; every cons cell is one cons constructor and advances both the
;; array index and next pointer.

(defun lp56-linked-steps-p
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     roots root array index bound)
  (if (consp roots)
      (and
       (lp56-address-p root)
       (equal (car roots) root)
       (equal
        (lp56-mptr-read
         memory-kind
         a2 a a1 update-target havoc-start havoc-length
         item a9 a7
         (lp56-shift array index))
        root)
       (lp56-valid-rw-p root 4)
       (lp56-linked-steps-p
        memory-kind
        a2 a a1 update-target havoc-start havoc-length
        item a9 a7
        (cdr roots)
        (lp56-mptr-read
         memory-kind
         a2 a a1 update-target havoc-start havoc-length
         item a9 a7
         (lp56-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lp56-p-linked-n-p
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:t3 :a8))
     (lp56-address-p root)
     (lp56-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lp56-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lp56-linked-steps-p
      memory-kind
      a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     roots root array index bound))))

(defun lp56-source-linked-steps-p
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     roots root array index bound)
  (if (consp roots)
      (and
       (lp56-address-p root)
       (equal (car roots) root)
       (equal
        (lp56-source-mptr-read
         memory-kind
         a2 a a1 update-target havoc-start havoc-length
         second-havoc-start second-havoc-length
         item a9 a7
         (lp56-shift array index))
        root)
       (lp56-valid-rw-p root 4)
       (lp56-source-linked-steps-p
        memory-kind
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a9 a7
        (cdr roots)
        (lp56-source-mptr-read
         memory-kind
         a2 a a1 update-target havoc-start havoc-length
         second-havoc-start second-havoc-length
         item a9 a7
         (lp56-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lp56-source-p-linked-n-p
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:a13 :a11))
     (lp56-address-p root)
     (lp56-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lp56-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lp56-source-linked-steps-p
      memory-kind
      a2 a a1 update-target havoc-start havoc-length
      second-havoc-start second-havoc-length
      item a9 a7
      roots root array index bound))))

;; This unfolds load_s1_list and eqs1_list. Pointer fields are read through
;; the selected pointer memories and the three scalar fields through t_1.

(defun lp56-eqs1-loads-p
    (left-kind right-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     left-root right-root)
  (and
   (equal
    (lp56-mptr-read
     right-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     (lp56-shift right-root 0))
    (lp56-mptr-read
     left-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     (lp56-shift left-root 0)))
   (equal
    (lp56-t1 (lp56-shift right-root 1))
    (lp56-t1 (lp56-shift left-root 1)))
   (equal
    (lp56-t1 (lp56-shift right-root 2))
    (lp56-t1 (lp56-shift left-root 2)))
   (equal
    (lp56-t1 (lp56-shift right-root 3))
    (lp56-t1 (lp56-shift left-root 3)))))

;; This is p_unchanged with the common malloc and real-valued memories
;; specialized to t and t_1, but with both pointer memories left explicit.

(defun-sk lp56-unchanged-p
    (left-kind right-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lp56-shift array index))
          (left-address
           (lp56-mptr-read
            left-kind
            a2 a a1 update-target havoc-start havoc-length
            item a9 a7 slot))
          (right-address
           (lp56-mptr-read
            right-kind
            a2 a a1 update-target havoc-start havoc-length
            item a9 a7 slot)))
       (and
        (equal left-address right-address)
        (lp56-eqs1-loads-p
         left-kind right-kind
         a2 a a1 update-target havoc-start havoc-length
         item a9 a7
         left-address right-address)
        (implies
         (lp56-valid-rw-p right-address 4)
         (lp56-valid-rw-p left-address 4)))))))

(defun lp56-source-eqs1-loads-p
    (left-kind right-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     left-root right-root)
  (and
   (equal
    (lp56-source-mptr-read
     right-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     (lp56-shift right-root 0))
    (lp56-source-mptr-read
     left-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     (lp56-shift left-root 0)))
   (equal
    (lp56-t1 (lp56-shift right-root 1))
    (lp56-t1 (lp56-shift left-root 1)))
   (equal
    (lp56-t1 (lp56-shift right-root 2))
    (lp56-t1 (lp56-shift left-root 2)))
   (equal
    (lp56-t1 (lp56-shift right-root 3))
    (lp56-t1 (lp56-shift left-root 3)))))

(defun-sk lp56-source-unchanged-p
    (left-kind right-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lp56-shift array index))
          (left-address
           (lp56-source-mptr-read
            left-kind
            a2 a a1 update-target havoc-start havoc-length
            second-havoc-start second-havoc-length
            item a9 a7 slot))
          (right-address
           (lp56-source-mptr-read
            right-kind
            a2 a a1 update-target havoc-start havoc-length
            second-havoc-start second-havoc-length
            item a9 a7 slot)))
       (and
        (equal left-address right-address)
        (lp56-source-eqs1-loads-p
         left-kind right-kind
         a2 a a1 update-target havoc-start havoc-length
         second-havoc-start second-havoc-length
         item a9 a7
         left-address right-address)
        (implies
         (lp56-valid-rw-p right-address 4)
         (lp56-valid-rw-p left-address 4)))))))

(defun lp56-range-index-p (index lower upper)
  (and
   (integerp index)
   (<= lower (+ 1 index))
   (<= (+ 2 index) upper)))

(defun-sk lp56-t3-not-item-range-p
    (item array lower upper)
  (forall (index)
    (implies
     (lp56-range-index-p index lower upper)
     (not
      (equal
       (lp56-t3 (lp56-shift array index))
       item)))))

(defun-sk lp56-sint32-t3-not-item-range-p
    (item array lower upper)
  (forall (index)
    (implies
     (and
      (lp56-range-index-p index lower upper)
      (lp56-is-sint32-p index))
     (not
      (equal
       (lp56-t3 (lp56-shift array index))
       item)))))

(defun-sk lp56-a2-separated-t3-range-p
    (a2 array lower upper)
  (forall (index)
    (implies
     (lp56-range-index-p index lower upper)
     (lp56-separated-p
      a2 1
      (lp56-t3 (lp56-shift array index))
      4))))

(defun-sk lp56-t3-range-separated-a5-p
    (array lower upper a5)
  (forall (index)
    (implies
     (lp56-range-index-p index lower upper)
     (lp56-separated-p
      (lp56-t3 (lp56-shift array index))
      4 a5 2147483646))))

(defun-sk lp56-item-separated-t3-range-p
    (item array lower upper)
  (forall (index)
    (implies
     (and
      (lp56-range-index-p index lower upper)
      (not
       (equal
        (lp56-t3 (lp56-shift array index))
        item)))
     (lp56-separated-p
      item 4
      (lp56-t3 (lp56-shift array index))
      4))))

(defun-sk lp56-t3-range-distinct-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp56-range-index-p left-index lower upper)
      (lp56-range-index-p right-index lower upper)
      (not (equal left-index right-index)))
     (not
      (equal
       (lp56-t3 (lp56-shift array left-index))
       (lp56-t3 (lp56-shift array right-index)))))))

(defun-sk lp56-t3-range-separated-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp56-range-index-p left-index lower upper)
      (lp56-range-index-p right-index lower upper)
      (not (equal left-index right-index)))
     (lp56-separated-p
      (lp56-t3 (lp56-shift array left-index))
      4
      (lp56-t3 (lp56-shift array right-index))
      4))))

(defun-sk lp56-a8-not-item-range-p
    (a2 a a1 update-target havoc-start havoc-length
        item array lower upper)
  (forall (index)
    (implies
     (lp56-range-index-p index lower upper)
     (not
      (equal
       (lp56-a8-read
        a2 a a1 update-target havoc-start havoc-length
        (lp56-shift array index))
       item)))))

(defun-sk lp56-a2-separated-a8-range-p
    (a2 a a1 update-target havoc-start havoc-length
        array lower upper)
  (forall (index)
    (implies
     (lp56-range-index-p index lower upper)
     (lp56-separated-p
      a2 1
      (lp56-a8-read
       a2 a a1 update-target havoc-start havoc-length
       (lp56-shift array index))
      4))))

(defun-sk lp56-item-separated-a8-range-p
    (a2 a a1 update-target havoc-start havoc-length
        item array lower upper)
  (forall (index)
    (implies
     (lp56-range-index-p index lower upper)
     (lp56-separated-p
      item 4
      (lp56-a8-read
       a2 a a1 update-target havoc-start havoc-length
       (lp56-shift array index))
      4))))

(defun-sk lp56-a8-range-separated-a5-p
    (a2 a a1 update-target havoc-start havoc-length
        array lower upper a5)
  (forall (index)
    (implies
     (lp56-range-index-p index lower upper)
     (lp56-separated-p
      (lp56-a8-read
       a2 a a1 update-target havoc-start havoc-length
       (lp56-shift array index))
      4 a5 2147483646))))

(defun-sk lp56-a8-range-distinct-p
    (a2 a a1 update-target havoc-start havoc-length
        array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp56-range-index-p left-index lower upper)
      (lp56-range-index-p right-index lower upper)
      (not (equal left-index right-index)))
     (not
      (equal
       (lp56-a8-read
        a2 a a1 update-target havoc-start havoc-length
        (lp56-shift array left-index))
       (lp56-a8-read
        a2 a a1 update-target havoc-start havoc-length
        (lp56-shift array right-index)))))))

(defun-sk lp56-a8-range-separated-p
    (a2 a a1 update-target havoc-start havoc-length
        array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp56-range-index-p left-index lower upper)
      (lp56-range-index-p right-index lower upper)
      (not (equal left-index right-index)))
     (lp56-separated-p
      (lp56-a8-read
       a2 a a1 update-target havoc-start havoc-length
       (lp56-shift array left-index))
      4
      (lp56-a8-read
       a2 a a1 update-target havoc-start havoc-length
       (lp56-shift array right-index))
      4))))

(defun-sk lp56-a13-range-property-p
    (property
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     array lower upper a5)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (let
         ((value
           (lp56-a13-read
            a2 a a1 update-target havoc-start havoc-length
            second-havoc-start second-havoc-length
            (lp56-shift array index))))
       (cond
        ((equal property :separated-a2)
         (lp56-separated-p a2 1 value 4))
        ((equal property :separated-array)
         (lp56-separated-p value 4 a5 2147483646))
        (t nil))))))

(defun-sk lp56-a13-pair-property-p
    (property
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
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
           (lp56-a13-read
            a2 a a1 update-target havoc-start havoc-length
            second-havoc-start second-havoc-length
            (lp56-shift array left-index)))
          (right
           (lp56-a13-read
            a2 a a1 update-target havoc-start havoc-length
            second-havoc-start second-havoc-length
            (lp56-shift array right-index))))
       (cond
        ((equal property :distinct)
         (not (equal left right)))
        ((equal property :separated)
         (lp56-separated-p left 4 right 4))
        (t nil))))))

(defun-sk lp56-a13-array-swipe-right-p
    (a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lp56-a8-read
       a2 a a1 update-target havoc-start havoc-length
       (lp56-shift array (- index 1)))
      (lp56-a13-read
       a2 a a1 update-target havoc-start havoc-length
       second-havoc-start second-havoc-length
       (lp56-shift array index))))))

(defun
    ntp4vc-list-push-does-not-contain-item-post-separation-2-part1-goal56-instance-p
    (i i1 item array a2 a a1 i3 i2)
  (implies
   (and
    (lp56-pointer-functions-p)
    (lp56-malloc-function-p)
    (lp56-region-function-p)
    (lp56-l-index-of-type-p)
    (lp56-l-index-of-laws-p)
    (integerp i)
    (integerp i1)
    (integerp i3)
    (integerp i2)
    (lp56-address-p item)
    (lp56-address-p array)
    (lp56-address-p a2)
    (lp56-address-p a)
    (lp56-address-p a1))
   (let*
       ((x (- i 1))
        (x1 (- (+ i i1) 1))
        (x2 (lp56-l-index-of item array x x1))
        (x3 (+ 1 x2))
        (x4 (+ i i1))
        (a5 (lp56-shift array 0))
        (a6 (lp56-t3 a2))
        (a7 (lp56-shift array x))
        (update-target
         (lp56-shift
          (lp56-t3
           (lp56-shift array (- x2 1)))
          0))
        (havoc-start (lp56-shift array x2))
        (havoc-length (- x1 x2))
        (second-havoc-start (lp56-shift array x))
        (second-havoc-length (+ 1 i1))
        (a9
         (lp56-a8-read
          a2 a a1 update-target
          havoc-start havoc-length a2)))
     (implies
      (and
       (not (equal i3 i2))
       (not (equal (lp56-null-address) item))
       (equal x3 x4)
       (< 0 i)
       (<= 0 i1)
       (< i2 x4)
       (< i3 x4)
       (<= (lp56-region (lp56-address-base a2)) 0)
       (<= (lp56-region (lp56-address-base item)) 0)
       (<= (lp56-region (lp56-address-base array)) 0)
       (< x2 x4)
       (<= i1 2147483645)
       (<= x4 2147483646)
       (<= i (+ 1 i2))
       (<= i (+ 1 i3))
       (<= i x3)
       (lp56-framed-p)
       (lp56-linked-p)
       (lp56-is-sint32-p i)
       (lp56-is-sint32-p i1)
       (lp56-valid-rw-p a2 1)
       (lp56-valid-rw-p item 4)
       (lp56-separated-p a2 1 item 4)
       (lp56-is-sint32-p x)
       (lp56-valid-rw-p a5 2147483646)
       (lp56-separated-p a2 1 a5 2147483646)
       (lp56-separated-p item 4 a5 2147483646)
       (lp56-separated-p a6 4 a5 2147483646)
       (lp56-valid-rw-p a7 i1)
       (lp56-p-linked-n-p
        :t3
        a2 a a1 update-target havoc-start havoc-length
        item a9 a7
        a6 array x i1 (lp56-null-address))
       (lp56-is-sint32-p x2)
       (lp56-separated-p a9 4 a5 2147483646)
       (lp56-eqs1-loads-p
        :a8 :t3
        a2 a a1 update-target havoc-start havoc-length
        item a9 a7
        item item)
       (lp56-p-linked-n-p
        :a8
        a2 a a1 update-target havoc-start havoc-length
        item a9 a7
        a9 array x i1 (lp56-null-address))
       (lp56-unchanged-p
        :a8 :t3
        a2 a a1 update-target havoc-start havoc-length
        item a9 a7
        array x x1)
       (lp56-source-unchanged-p
        :a11 :a10
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a9 a7
        array x x4)
       (lp56-t3-not-item-range-p item array i x4)
       (lp56-sint32-t3-not-item-range-p item array i x4)
       (lp56-a2-separated-t3-range-p a2 array i x4)
       (lp56-t3-range-separated-a5-p array i x4 a5)
       (lp56-item-separated-t3-range-p item array i x4)
       (lp56-t3-range-distinct-p array i x4)
       (lp56-t3-range-separated-p array i x4)
       (lp56-a8-not-item-range-p
        a2 a a1 update-target havoc-start havoc-length
        item array i x4)
       (lp56-a2-separated-a8-range-p
        a2 a a1 update-target havoc-start havoc-length
        array i x4)
       (lp56-item-separated-a8-range-p
        a2 a a1 update-target havoc-start havoc-length
        item array i x4)
       (lp56-a8-range-separated-a5-p
        a2 a a1 update-target havoc-start havoc-length
        array i x4 a5)
       (lp56-a8-range-distinct-p
        a2 a a1 update-target havoc-start havoc-length
        array i x4)
       (lp56-a8-range-separated-p
        a2 a a1 update-target havoc-start havoc-length
        array i x4)
       (equal
        (lp56-a13-read
         a2 a a1 update-target havoc-start havoc-length
         second-havoc-start second-havoc-length a2)
        a9)
       (lp56-separated-p
        (lp56-a13-read
         a2 a a1 update-target havoc-start havoc-length
         second-havoc-start second-havoc-length a2)
        4 a5 2147483646)
       (lp56-a13-range-property-p
        :separated-a2
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        array i x4 a5)
       (lp56-a13-range-property-p
        :separated-array
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        array i x4 a5)
       (lp56-a13-pair-property-p
        :separated
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        array i x4)
       (lp56-a13-pair-property-p
        :distinct
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        array x x4)
       (lp56-a13-array-swipe-right-p
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        array i x4)
       (lp56-source-p-linked-n-p
        :a13
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a9 a7
        a9 array i i1 (lp56-null-address)))
      (lp56-separated-p
       (lp56-a11-read
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a9 a7
        (lp56-shift array i3))
       4
       (lp56-a11-read
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a9 a7
        (lp56-shift array i2))
       4)))))

(defun-sk
    ntp4vc-list-push-does-not-contain-item-post-separation-2-part1-goal56-statement ()
  (forall
   (i i1 item array a2 a a1 i3 i2)
   (ntp4vc-list-push-does-not-contain-item-post-separation-2-part1-goal56-instance-p
    i i1 item array a2 a a1 i3 i2)))

(value-triple :itpeval-statement-checked)

:q
