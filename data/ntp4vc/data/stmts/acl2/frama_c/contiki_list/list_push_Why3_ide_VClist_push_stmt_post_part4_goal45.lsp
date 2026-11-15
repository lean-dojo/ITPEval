;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_push_Why3_ide_VClist_push_stmt_post_part4_goal45:
;; preservation of a linked-list array segment after a bounded pointer-memory
;; havoc and successive pointer updates, under the stated integer, framing,
;; validity, separation, linkage, uniqueness, and unchanged-memory conditions.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lp45-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lp45-address-base (address)
  (car address))

(defun lp45-address-offset (address)
  (cdr address))

(defun lp45-shift (address amount)
  (cons
   (lp45-address-base address)
   (+ (lp45-address-offset address) amount)))

(defun lp45-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2, t_3, and t_4, allocation function t, real-valued
;; memory t_1, region and linked operations, and l_index_of specialized to t_3.
;; Values of t_1 are used only through equality. Since the address domain is
;; countable, arbitrary ACL2 values preserve exactly the equality patterns
;; realizable by a real-valued source function.

(defstub lp45-t2 (address) t)
(defstub lp45-t3 (address) t)
(defstub lp45-t4 (address) t)
(defstub lp45-malloc (index) t)
(defstub lp45-t1 (address) t)
(defstub lp45-region (base) t)
(defstub lp45-linked-op () t)
(defstub lp45-l-index-of (item array down up) t)

(defun-sk lp45-environment-types-p ()
  (forall (address index base item array down up)
    (and
     (implies
      (lp45-address-p address)
       (and
       (lp45-address-p (lp45-t2 address))
       (lp45-address-p (lp45-t3 address))
       (lp45-address-p (lp45-t4 address))))
     (implies
      (integerp index)
      (integerp (lp45-malloc index)))
     (implies
      (integerp base)
      (integerp (lp45-region base)))
     (implies
      (and
       (lp45-address-p item)
       (lp45-address-p array)
       (integerp down)
       (integerp up))
      (integerp
       (lp45-l-index-of item array down up))))))

(defun lp45-linked-p ()
  (if (lp45-linked-op) t nil))

(defun lp45-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lp45-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lp45-address-base left)
     (lp45-address-base right)))
   (<=
    (+ (lp45-address-offset right) right-length)
    (lp45-address-offset left))
   (<=
    (+ (lp45-address-offset left) left-length)
    (lp45-address-offset right))))

(defun lp45-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lp45-address-base address))
    (<= 0 (lp45-address-offset address))
    (<=
     (+ (lp45-address-offset address) length)
     (lp45-malloc (lp45-address-base address))))))

(defun-sk lp45-framed-p ()
  (forall (address)
    (implies
     (lp45-address-p address)
     (<=
      (lp45-region
       (lp45-address-base (lp45-t3 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lp45-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lp45-address-p item)
      (lp45-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lp45-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lp45-t3 (lp45-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lp45-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lp45-t3 (lp45-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lp45-l-index-of item array (+ 1 down) up)
        (lp45-l-index-of item array down up)))))))

;; M is the two successive source functional updates of t_3. The update at
;; shift(a9,0) has precedence over the update at a2 when the addresses alias.

(defun lp45-m-read (a2 a a1 a9 address)
  (cond
   ((equal address (lp45-shift a9 0)) a1)
   ((equal address a2) a)
   (t (lp45-t3 address))))

;; A10 is the exact source havoc access equation: outside the possibly
;; modified interval it reads M, and inside it reads the arbitrary t_2.

(defun lp45-a10-read
    (a2 a a1 a9 havoc-start havoc-length address)
  (if
      (lp45-separated-p address 1 havoc-start havoc-length)
      (lp45-m-read a2 a a1 a9 address)
    (lp45-t2 address)))

;; A14 is the second source havoc: outside its interval it reads A10, and
;; inside it reads the arbitrary t_4. A12 and FINAL are the subsequent source
;; updates; the later update has precedence when addresses alias.

(defun lp45-a14-read
    (a2 a a1 a9 havoc-start havoc-length
        second-havoc-start second-havoc-length address)
  (if
      (lp45-separated-p
       address 1 second-havoc-start second-havoc-length)
      (lp45-a10-read
       a2 a a1 a9 havoc-start havoc-length address)
    (lp45-t4 address)))

(defun lp45-source-a12-read
    (a2 a a1 a9 havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a11 a7 address)
  (cond
   ((equal address a7) item)
   ((equal address (lp45-shift item 0)) a11)
   (t
    (lp45-a14-read
     a2 a a1 a9 havoc-start havoc-length
     second-havoc-start second-havoc-length address))))

(defun lp45-source-final-read
    (a2 a a1 a9 havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a11 a7 address)
  (if (equal address a2)
      item
    (lp45-source-a12-read
     a2 a a1 a9 havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a11 a7 address)))

(defun lp45-mptr-read
    (memory-kind
     a2 a a1 a9 havoc-start havoc-length
     item a11 a7 address)
  (declare (ignore item a11 a7))
  (cond
   ((equal memory-kind :t3)
    (lp45-t3 address))
   ((equal memory-kind :a10)
    (lp45-a10-read
     a2 a a1 a9 havoc-start havoc-length address))
   (t nil)))

(defun lp45-source-mptr-read
    (memory-kind
     a2 a a1 a9 havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a11 a7 address)
  (cond
   ((equal memory-kind :a14)
    (lp45-a14-read
     a2 a a1 a9 havoc-start havoc-length
     second-havoc-start second-havoc-length address))
   ((equal memory-kind :a12)
    (lp45-source-a12-read
     a2 a a1 a9 havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a11 a7 address))
   ((equal memory-kind :final)
    (lp45-source-final-read
     a2 a a1 a9 havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a11 a7 address))
   (t nil)))

;; A true list of N successive roots is constructor evidence for the source
;; inductive p_linked_n relation. The empty witness is its bound constructor;
;; each cons cell is one cons constructor.

(defun lp45-linked-steps-p
    (memory-kind
     a2 a a1 a9 havoc-start havoc-length
     item a11 a7
     roots root array index bound)
  (if (consp roots)
      (and
       (lp45-address-p root)
       (equal (car roots) root)
       (equal
        (lp45-mptr-read
         memory-kind
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7
         (lp45-shift array index))
        root)
       (lp45-valid-rw-p root 4)
       (lp45-linked-steps-p
        memory-kind
        a2 a a1 a9 havoc-start havoc-length
        item a11 a7
        (cdr roots)
        (lp45-mptr-read
         memory-kind
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7
         (lp45-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lp45-p-linked-n-p
    (memory-kind
     a2 a a1 a9 havoc-start havoc-length
     item a11 a7
     root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:t3 :a10))
     (lp45-address-p root)
     (lp45-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lp45-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lp45-linked-steps-p
      memory-kind
      a2 a a1 a9 havoc-start havoc-length
      item a11 a7
      roots root array index bound))))

(defun lp45-a14-linked-steps-p
    (a2 a a1 a9 havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a11 a7
        roots root array index bound)
  (if (consp roots)
      (and
       (lp45-address-p root)
       (equal (car roots) root)
       (equal
        (lp45-source-mptr-read
         :a14
         a2 a a1 a9 havoc-start havoc-length
         second-havoc-start second-havoc-length
         item a11 a7
         (lp45-shift array index))
        root)
       (lp45-valid-rw-p root 4)
       (lp45-a14-linked-steps-p
        a2 a a1 a9 havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a11 a7
        (cdr roots)
        (lp45-source-mptr-read
         :a14
         a2 a a1 a9 havoc-start havoc-length
         second-havoc-start second-havoc-length
         item a11 a7
         (lp45-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lp45-a14-p-linked-n-p
    (a2 a a1 a9 havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a11 a7
        root array index n bound)
  (exists (roots)
    (and
     (lp45-address-p root)
     (lp45-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lp45-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lp45-a14-linked-steps-p
      a2 a a1 a9 havoc-start havoc-length
      second-havoc-start second-havoc-length
      item a11 a7
      roots root array index bound))))

;; This unfolds load_s1_list and eqs1_list. Pointer fields use the selected
;; pointer memories and the three scalar fields use t_1.

(defun lp45-eqs1-loads-p
    (left-kind right-kind
     a2 a a1 a9 havoc-start havoc-length
     item a11 a7
     left-root right-root)
  (and
   (equal
    (lp45-mptr-read
     right-kind
     a2 a a1 a9 havoc-start havoc-length
     item a11 a7
     (lp45-shift right-root 0))
    (lp45-mptr-read
     left-kind
     a2 a a1 a9 havoc-start havoc-length
     item a11 a7
     (lp45-shift left-root 0)))
   (equal
    (lp45-t1 (lp45-shift right-root 1))
    (lp45-t1 (lp45-shift left-root 1)))
   (equal
    (lp45-t1 (lp45-shift right-root 2))
    (lp45-t1 (lp45-shift left-root 2)))
   (equal
    (lp45-t1 (lp45-shift right-root 3))
    (lp45-t1 (lp45-shift left-root 3)))))

(defun-sk lp45-unchanged-p
    (left-kind right-kind
     a2 a a1 a9 havoc-start havoc-length
     item a11 a7
     array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lp45-shift array index))
          (left-address
           (lp45-mptr-read
            left-kind
            a2 a a1 a9 havoc-start havoc-length
            item a11 a7 slot))
          (right-address
           (lp45-mptr-read
            right-kind
            a2 a a1 a9 havoc-start havoc-length
            item a11 a7 slot)))
       (and
        (equal left-address right-address)
        (lp45-eqs1-loads-p
         left-kind right-kind
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7
         left-address right-address)
        (implies
         (lp45-valid-rw-p right-address 4)
         (lp45-valid-rw-p left-address 4)))))))

(defun lp45-source-eqs1-loads-p
    (left-kind right-kind
     a2 a a1 a9 havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a11 a7
     left-root right-root)
  (and
   (equal
    (lp45-source-mptr-read
     right-kind
     a2 a a1 a9 havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a11 a7
     (lp45-shift right-root 0))
    (lp45-source-mptr-read
     left-kind
     a2 a a1 a9 havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a11 a7
     (lp45-shift left-root 0)))
   (equal
    (lp45-t1 (lp45-shift right-root 1))
    (lp45-t1 (lp45-shift left-root 1)))
   (equal
    (lp45-t1 (lp45-shift right-root 2))
    (lp45-t1 (lp45-shift left-root 2)))
   (equal
    (lp45-t1 (lp45-shift right-root 3))
    (lp45-t1 (lp45-shift left-root 3)))))

(defun-sk lp45-source-unchanged-p
    (a2 a a1 a9 havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a11 a7
        array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lp45-shift array index))
          (left-address
           (lp45-source-mptr-read
            :final
            a2 a a1 a9 havoc-start havoc-length
            second-havoc-start second-havoc-length
            item a11 a7 slot))
          (right-address
           (lp45-source-mptr-read
            :a12
            a2 a a1 a9 havoc-start havoc-length
            second-havoc-start second-havoc-length
            item a11 a7 slot)))
       (and
        (equal left-address right-address)
        (lp45-source-eqs1-loads-p
         :final :a12
         a2 a a1 a9 havoc-start havoc-length
         second-havoc-start second-havoc-length
         item a11 a7
         left-address right-address)
        (implies
         (lp45-valid-rw-p right-address 4)
         (lp45-valid-rw-p left-address 4)))))))

;; These two predicates are the existential and universal source cases used
;; throughout the branch hypotheses.

(defun-sk lp45-item-in-range-p (item array lower upper)
  (exists (index)
    (and
     (integerp index)
     (equal
      item
      (lp45-t3 (lp45-shift array index)))
     (< index upper)
     (<= lower (+ 1 index)))))

(defun-sk lp45-no-item-in-range-p (item array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< index upper)
      (<= lower (+ 1 index)))
     (not
      (equal
       item
       (lp45-t3 (lp45-shift array index)))))))

(defun lp45-range-index-p
    (range-kind index lower upper x2)
  (and
   (integerp index)
   (cond
    ((equal range-kind :source)
     (and
      (< index upper)
      (<= lower (+ 1 index))))
    ((equal range-kind :interior)
     (and
      (<= lower (+ 1 index))
      (<= (+ 2 index) upper)))
    ((equal range-kind :suffix)
     (and
      (<= x2 index)
      (<= (+ 2 index) upper)))
    (t nil))))

(defun-sk lp45-a10-range-property-p
    (property range-kind
     a2 a a1 a9 havoc-start havoc-length
     item a11 a7 array lower upper x2 a5)
  (forall (index)
    (implies
     (lp45-range-index-p
      range-kind index lower upper x2)
     (let
         ((value
           (lp45-a10-read
            a2 a a1 a9 havoc-start havoc-length
            (lp45-shift array index))))
       (cond
        ((equal property :not-item)
         (not (equal value item)))
        ((equal property :separated-a2)
         (lp45-separated-p a2 1 value 4))
        ((equal property :separated-item)
         (lp45-separated-p item 4 value 4))
        ((equal property :separated-array)
         (lp45-separated-p value 4 a5 2147483646))
        (t nil))))))

(defun-sk lp45-a10-pair-property-p
    (property range-kind
     a2 a a1 a9 havoc-start havoc-length
     item a11 a7 array lower upper x2)
  (forall (left-index right-index)
    (implies
     (and
      (lp45-range-index-p
       range-kind left-index lower upper x2)
      (lp45-range-index-p
       range-kind right-index lower upper x2)
      (not (equal left-index right-index)))
     (let
         ((left
           (lp45-a10-read
            a2 a a1 a9 havoc-start havoc-length
            (lp45-shift array left-index)))
          (right
           (lp45-a10-read
            a2 a a1 a9 havoc-start havoc-length
            (lp45-shift array right-index))))
       (cond
        ((equal property :distinct)
         (not (equal left right)))
        ((equal property :separated)
         (lp45-separated-p left 4 right 4))
        (t nil))))))

(defun-sk lp45-array-swipe-left-p
    (a2 a a1 a9 havoc-start havoc-length
        array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lp45-t3 (lp45-shift array (+ 1 index)))
      (lp45-a10-read
       a2 a a1 a9 havoc-start havoc-length
       (lp45-shift array index))))))

(defun-sk lp45-successor-loads-p
    (a2 a a1 a9 havoc-start havoc-length
        item a11 a7 array lower upper x2)
  (forall (index)
    (implies
     (lp45-range-index-p
      :suffix index lower upper x2)
     (lp45-eqs1-loads-p
      :a10 :t3
      a2 a a1 a9 havoc-start havoc-length
      item a11 a7
      (lp45-a10-read
       a2 a a1 a9 havoc-start havoc-length
       (lp45-shift array index))
      (lp45-t3
       (lp45-shift array (+ 1 index)))))))

(defun-sk lp45-t3-range-property-p
    (property item a2 array lower upper a5)
  (forall (index)
    (implies
     (lp45-range-index-p
      :source index lower upper 0)
     (let ((value
            (lp45-t3 (lp45-shift array index))))
       (cond
        ((equal property :separated-a2)
         (lp45-separated-p a2 1 value 4))
        ((equal property :separated-array)
         (lp45-separated-p value 4 a5 2147483646))
        ((equal property :separated-item-if-different)
         (implies
          (not (equal item value))
          (lp45-separated-p item 4 value 4)))
        (t nil))))))

(defun-sk lp45-t3-pair-property-p
    (property array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp45-range-index-p
       :source left-index lower upper 0)
      (lp45-range-index-p
       :source right-index lower upper 0)
      (not (equal left-index right-index)))
     (let
         ((left
           (lp45-t3 (lp45-shift array left-index)))
          (right
           (lp45-t3 (lp45-shift array right-index))))
       (cond
        ((equal property :distinct)
         (not (equal left right)))
        ((equal property :separated)
         (lp45-separated-p left 4 right 4))
        (t nil))))))

(defun-sk lp45-a14-range-property-p
    (property
     a2 a a1 a9 havoc-start havoc-length
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
           (lp45-a14-read
            a2 a a1 a9 havoc-start havoc-length
            second-havoc-start second-havoc-length
            (lp45-shift array index))))
       (cond
        ((equal property :separated-a2)
         (lp45-separated-p a2 1 value 4))
        ((equal property :separated-array)
         (lp45-separated-p value 4 a5 2147483646))
        (t nil))))))

(defun-sk lp45-a14-pair-property-p
    (property
     a2 a a1 a9 havoc-start havoc-length
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
           (lp45-a14-read
            a2 a a1 a9 havoc-start havoc-length
            second-havoc-start second-havoc-length
            (lp45-shift array left-index)))
          (right
           (lp45-a14-read
            a2 a a1 a9 havoc-start havoc-length
            second-havoc-start second-havoc-length
            (lp45-shift array right-index))))
       (cond
        ((equal property :distinct)
         (not (equal left right)))
        ((equal property :separated)
         (lp45-separated-p left 4 right 4))
        (t nil))))))

(defun-sk lp45-array-swipe-right-p
    (a2 a a1 a9 havoc-start havoc-length
        second-havoc-start second-havoc-length
        array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lp45-a10-read
       a2 a a1 a9 havoc-start havoc-length
       (lp45-shift array (- index 1)))
      (lp45-a14-read
       a2 a a1 a9 havoc-start havoc-length
       second-havoc-start second-havoc-length
       (lp45-shift array index))))))

(defun
    ntp4vc-list-push-stmt-post-part4-goal45-instance-p
    (array i2 i i1 a2 a a1)
  (implies
   (and
    (lp45-environment-types-p)
    (lp45-l-index-of-laws-p)
    (lp45-address-p array)
    (integerp i2)
    (integerp i)
    (integerp i1)
    (lp45-address-p a2)
    (lp45-address-p a)
    (lp45-address-p a1))
   (let*
       ((item (lp45-t3 (lp45-shift array i2)))
        (x (+ i i1))
        (x1 (- i1 1))
        (x2 (lp45-l-index-of item array x1 x))
        (x3 (+ 1 i))
        (a5 (lp45-shift array 0))
        (a6 (lp45-t3 a2))
        (a7 (lp45-shift array x1))
        (x4 (- x2 1))
        (a8 (lp45-shift array x4))
        (a9 (lp45-t3 a8))
        (havoc-start (lp45-shift array x2))
        (havoc-length (- x x2))
        (second-havoc-start (lp45-shift array x1))
        (second-havoc-length (+ 1 i))
        (a11
         (lp45-a10-read
          a2 a a1 a9 havoc-start havoc-length a2))
        (item-in-range
         (lp45-item-in-range-p item array i1 x))
        (no-item-in-range
         (lp45-no-item-in-range-p item array i1 x)))
     (implies
      (and
       (not (equal item (lp45-null-address)))
       (not (equal x x2))
       (< 0 i1)
       (< i2 x)
       (<= (lp45-region (lp45-address-base a2)) 0)
       (<= (lp45-region (lp45-address-base array)) 0)
       (<= (lp45-region (lp45-address-base item)) 0)
       (< x2 x)
       (<= x2 x)
       (<= -1 i)
       (<= i 2147483644)
       (<= x 2147483645)
       (<= i1 (+ 1 i2))
       (<= i1 (+ 1 x2))
       (lp45-framed-p)
       (lp45-linked-p)
       (lp45-is-sint32-p i)
       (lp45-is-sint32-p i1)
       (lp45-valid-rw-p a2 1)
       (lp45-is-sint32-p x1)
       (lp45-is-sint32-p x3)
       (lp45-valid-rw-p a5 2147483646)
       (lp45-valid-rw-p item 4)
       (lp45-separated-p a2 1 a5 2147483646)
       (lp45-separated-p a6 4 a5 2147483646)
       (lp45-separated-p a2 1 item 4)
       (lp45-separated-p item 4 a5 2147483646)
       (lp45-valid-rw-p a7 x3)
       (lp45-p-linked-n-p
        :t3
        a2 a a1 a9 havoc-start havoc-length
        item a11 a7
        a6 array x1 x3 (lp45-null-address))
       (lp45-is-sint32-p x2)
       (lp45-separated-p a11 4 a5 2147483646)
       (lp45-eqs1-loads-p
        :a10 :t3
        a2 a a1 a9 havoc-start havoc-length
        item a11 a7 item item)
       (implies
        (<= i1 x2)
        (implies
         item-in-range
         (equal
          (lp45-a10-read
           a2 a a1 a9 havoc-start havoc-length a8)
          a9)))
       (implies
        item-in-range
        (lp45-array-swipe-left-p
         a2 a a1 a9 havoc-start havoc-length
         array x2 (- x 1)))
       (implies
        no-item-in-range
        (lp45-a10-range-property-p
         :not-item :source
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7 array i1 x x2 a5))
       (implies
        item-in-range
        (lp45-a10-range-property-p
         :not-item :interior
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7 array i1 x x2 a5))
       (implies
        item-in-range
        (lp45-p-linked-n-p
         :a10
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7
         a11 array x1 i (lp45-null-address)))
       (implies
        no-item-in-range
        (lp45-p-linked-n-p
         :a10
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7
         a11 array x1 x3 (lp45-null-address)))
       (implies
        no-item-in-range
        (lp45-unchanged-p
         :a10 :t3
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7 array x1 x))
       (implies
        item-in-range
        (lp45-unchanged-p
         :a10 :t3
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7 array x1 x4))
       (implies
        no-item-in-range
        (lp45-a10-range-property-p
         :separated-a2 :source
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7 array i1 x x2 a5))
       (implies
        item-in-range
        (lp45-a10-range-property-p
         :separated-a2 :interior
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7 array i1 x x2 a5))
       (implies
        no-item-in-range
        (lp45-a10-range-property-p
         :separated-item :source
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7 array i1 x x2 a5))
       (implies
        item-in-range
        (lp45-a10-range-property-p
         :separated-item :interior
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7 array i1 x x2 a5))
       (implies
        no-item-in-range
        (lp45-a10-range-property-p
         :separated-array :source
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7 array i1 x x2 a5))
       (implies
        item-in-range
        (lp45-a10-range-property-p
         :separated-array :interior
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7 array i1 x x2 a5))
       (implies
        item-in-range
        (lp45-successor-loads-p
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7 array i1 x x2))
       (implies
        no-item-in-range
        (lp45-a10-pair-property-p
         :distinct :source
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7 array i1 x x2))
       (implies
        item-in-range
        (lp45-a10-pair-property-p
         :distinct :interior
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7 array i1 x x2))
       (implies
        no-item-in-range
        (lp45-a10-pair-property-p
         :separated :source
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7 array i1 x x2))
       (implies
        item-in-range
        (lp45-a10-pair-property-p
         :separated :interior
         a2 a a1 a9 havoc-start havoc-length
         item a11 a7 array i1 x x2))
       (lp45-t3-range-property-p
        :separated-a2 item a2 array i1 x a5)
       (lp45-t3-range-property-p
        :separated-array item a2 array i1 x a5)
       (lp45-t3-range-property-p
        :separated-item-if-different
        item a2 array i1 x a5)
       (lp45-t3-pair-property-p
        :distinct array i1 x)
       (lp45-t3-pair-property-p
        :separated array i1 x)
       (equal
        (lp45-a14-read
         a2 a a1 a9 havoc-start havoc-length
         second-havoc-start second-havoc-length a2)
        a11)
       (lp45-separated-p
        (lp45-a14-read
         a2 a a1 a9 havoc-start havoc-length
         second-havoc-start second-havoc-length a2)
        4 a5 2147483646)
       (lp45-a14-range-property-p
        :separated-a2
        a2 a a1 a9 havoc-start havoc-length
        second-havoc-start second-havoc-length
        array i1 x a5)
       (lp45-a14-range-property-p
        :separated-array
        a2 a a1 a9 havoc-start havoc-length
        second-havoc-start second-havoc-length
        array i1 x a5)
       (lp45-a14-pair-property-p
        :separated
        a2 a a1 a9 havoc-start havoc-length
        second-havoc-start second-havoc-length
        array i1 x)
       (lp45-a14-pair-property-p
        :distinct
        a2 a a1 a9 havoc-start havoc-length
        second-havoc-start second-havoc-length
        array x1 x)
       (lp45-array-swipe-right-p
        a2 a a1 a9 havoc-start havoc-length
        second-havoc-start second-havoc-length
        array i1 x)
       (lp45-a14-p-linked-n-p
        a2 a a1 a9 havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a11 a7
        a11 array i1 i (lp45-null-address)))
      (lp45-source-unchanged-p
       a2 a a1 a9 havoc-start havoc-length
       second-havoc-start second-havoc-length
       item a11 a7
       array x1 x)))))

(defun-sk
    ntp4vc-list-push-stmt-post-part4-goal45-statement ()
  (forall
   (array i2 i i1 a2 a a1)
   (ntp4vc-list-push-stmt-post-part4-goal45-instance-p
    array i2 i i1 a2 a a1)))

(value-triple :itpeval-statement-checked)

:q
