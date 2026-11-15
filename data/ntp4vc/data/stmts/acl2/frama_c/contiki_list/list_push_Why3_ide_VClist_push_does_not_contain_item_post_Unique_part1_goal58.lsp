;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_push_Why3_ide_VClist_push_does_not_contain_item_post_Unique_part1_goal58:
;; inequality of two final updated linked-list pointers selected at distinct
;; integer array indices, after two pointer-memory havocs and pointer updates,
;; under bounds, validity, framing, linkage, separation, and range-uniqueness
;; hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lp58-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lp58-address-base (address)
  (car address))

(defun lp58-address-offset (address)
  (cdr address))

(defun lp58-shift (address amount)
  (cons
   (lp58-address-base address)
   (+ (lp58-address-offset address) amount)))

(defun lp58-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2, t_3, and t_4, allocation function t, real-valued
;; memory t_1, region and linked operations, and l_index_of specialized to t_3.
;; Values of t_1 are used only through equality. Since the address domain is
;; countable, arbitrary ACL2 values preserve exactly the equality patterns
;; realizable by a real-valued source function.

(defstub lp58-t2 (address) t)
(defstub lp58-t3 (address) t)
(defstub lp58-t4 (address) t)
(defstub lp58-malloc (index) t)
(defstub lp58-t1 (address) t)
(defstub lp58-region (base) t)
(defstub lp58-linked-op () t)
(defstub lp58-l-index-of (item array down up) t)

(defun-sk lp58-environment-types-p ()
  (forall (address index base item array down up)
    (and
     (implies
      (lp58-address-p address)
      (and
       (lp58-address-p (lp58-t2 address))
       (lp58-address-p (lp58-t3 address))
       (lp58-address-p (lp58-t4 address))))
     (implies
      (integerp index)
      (integerp (lp58-malloc index)))
     (implies
      (integerp base)
      (integerp (lp58-region base)))
     (implies
      (and
       (lp58-address-p item)
       (lp58-address-p array)
       (integerp down)
       (integerp up))
      (integerp
       (lp58-l-index-of item array down up))))))

(defun lp58-linked-p ()
  (if (lp58-linked-op) t nil))

(defun lp58-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lp58-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lp58-address-base left)
     (lp58-address-base right)))
   (<=
    (+ (lp58-address-offset right) right-length)
    (lp58-address-offset left))
   (<=
    (+ (lp58-address-offset left) left-length)
    (lp58-address-offset right))))

(defun lp58-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lp58-address-base address))
    (<= 0 (lp58-address-offset address))
    (<=
     (+ (lp58-address-offset address) length)
     (lp58-malloc (lp58-address-base address))))))

(defun-sk lp58-framed-p ()
  (forall (address)
    (implies
     (lp58-address-p address)
     (<=
      (lp58-region
       (lp58-address-base (lp58-t3 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lp58-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lp58-address-p item)
      (lp58-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lp58-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lp58-t3 (lp58-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lp58-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lp58-t3 (lp58-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lp58-l-index-of item array (+ 1 down) up)
        (lp58-l-index-of item array down up)))))))

;; M is the two successive source functional updates of t_3. The second
;; update has precedence even when the update addresses alias.

(defun lp58-m-read
    (a2 a a1 update-target address)
  (cond
   ((equal address update-target) a1)
   ((equal address a2) a)
   (t (lp58-t3 address))))

;; A8 is the source havoc: outside the possibly modified interval it reads M,
;; and inside that interval it reads the arbitrary prior memory t_2.

(defun lp58-a8-read
    (a2 a a1 update-target
        havoc-start havoc-length address)
  (if
      (lp58-separated-p address 1 havoc-start havoc-length)
      (lp58-m-read a2 a a1 update-target address)
    (lp58-t2 address)))

;; A13 is the second source havoc: outside its interval it reads A8, and
;; inside it reads the arbitrary t_4. A10 and A11 are the subsequent source
;; functional updates, with the later update taking precedence.

(defun lp58-a13-read
    (a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length address)
  (if
      (lp58-separated-p
       address 1 second-havoc-start second-havoc-length)
      (lp58-a8-read
       a2 a a1 update-target havoc-start havoc-length address)
    (lp58-t4 address)))

(defun lp58-a10-read
    (a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a9 a7 address)
  (cond
   ((equal address a7) item)
   ((equal address (lp58-shift item 0)) a9)
   (t
    (lp58-a13-read
     a2 a a1 update-target
     havoc-start havoc-length
     second-havoc-start second-havoc-length address))))

(defun lp58-a11-read
    (a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a9 a7 address)
  (if (equal address a2)
      item
    (lp58-a10-read
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7 address)))

(defun lp58-mptr-read
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7 address)
  (declare (ignore item a9 a7))
  (cond
   ((equal memory-kind :t3)
    (lp58-t3 address))
   ((equal memory-kind :a8)
    (lp58-a8-read
     a2 a a1 update-target havoc-start havoc-length address))
   (t nil)))

(defun lp58-source-mptr-read
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7 address)
  (cond
   ((equal memory-kind :a13)
    (lp58-a13-read
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length address))
   ((equal memory-kind :a10)
    (lp58-a10-read
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7 address))
   ((equal memory-kind :a11)
    (lp58-a11-read
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7 address))
   (t nil)))

;; A true list of N successive roots is constructor evidence for the source
;; inductive p_linked_n relation. The empty witness is its bound constructor;
;; every cons cell is one cons constructor.

(defun lp58-linked-steps-p
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     roots root array index bound)
  (if (consp roots)
      (and
       (lp58-address-p root)
       (equal (car roots) root)
       (equal
        (lp58-mptr-read
         memory-kind
         a2 a a1 update-target havoc-start havoc-length
         item a9 a7
         (lp58-shift array index))
        root)
       (lp58-valid-rw-p root 4)
       (lp58-linked-steps-p
        memory-kind
        a2 a a1 update-target havoc-start havoc-length
        item a9 a7
        (cdr roots)
        (lp58-mptr-read
         memory-kind
         a2 a a1 update-target havoc-start havoc-length
         item a9 a7
         (lp58-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lp58-p-linked-n-p
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:t3 :a8))
     (lp58-address-p root)
     (lp58-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lp58-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lp58-linked-steps-p
      memory-kind
      a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     roots root array index bound))))

(defun lp58-source-linked-steps-p
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     roots root array index bound)
  (if (consp roots)
      (and
       (lp58-address-p root)
       (equal (car roots) root)
       (equal
        (lp58-source-mptr-read
         memory-kind
         a2 a a1 update-target havoc-start havoc-length
         second-havoc-start second-havoc-length
         item a9 a7
         (lp58-shift array index))
        root)
       (lp58-valid-rw-p root 4)
       (lp58-source-linked-steps-p
        memory-kind
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a9 a7
        (cdr roots)
        (lp58-source-mptr-read
         memory-kind
         a2 a a1 update-target havoc-start havoc-length
         second-havoc-start second-havoc-length
         item a9 a7
         (lp58-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lp58-source-p-linked-n-p
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:a13 :a11))
     (lp58-address-p root)
     (lp58-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lp58-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lp58-source-linked-steps-p
      memory-kind
      a2 a a1 update-target havoc-start havoc-length
      second-havoc-start second-havoc-length
      item a9 a7
      roots root array index bound))))

;; This unfolds load_s1_list and eqs1_list.

(defun lp58-eqs1-loads-p
    (left-kind right-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     left-root right-root)
  (and
   (equal
    (lp58-mptr-read
     right-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     (lp58-shift right-root 0))
    (lp58-mptr-read
     left-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     (lp58-shift left-root 0)))
   (equal
    (lp58-t1 (lp58-shift right-root 1))
    (lp58-t1 (lp58-shift left-root 1)))
   (equal
    (lp58-t1 (lp58-shift right-root 2))
    (lp58-t1 (lp58-shift left-root 2)))
   (equal
    (lp58-t1 (lp58-shift right-root 3))
    (lp58-t1 (lp58-shift left-root 3)))))

(defun-sk lp58-unchanged-p
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
         ((slot (lp58-shift array index))
          (left-address
           (lp58-mptr-read
            left-kind
            a2 a a1 update-target havoc-start havoc-length
            item a9 a7 slot))
          (right-address
           (lp58-mptr-read
            right-kind
            a2 a a1 update-target havoc-start havoc-length
            item a9 a7 slot)))
       (and
        (equal left-address right-address)
        (lp58-eqs1-loads-p
         left-kind right-kind
         a2 a a1 update-target havoc-start havoc-length
         item a9 a7
         left-address right-address)
        (implies
         (lp58-valid-rw-p right-address 4)
         (lp58-valid-rw-p left-address 4)))))))

(defun lp58-source-eqs1-loads-p
    (left-kind right-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     left-root right-root)
  (and
   (equal
    (lp58-source-mptr-read
     right-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     (lp58-shift right-root 0))
    (lp58-source-mptr-read
     left-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     (lp58-shift left-root 0)))
   (equal
    (lp58-t1 (lp58-shift right-root 1))
    (lp58-t1 (lp58-shift left-root 1)))
   (equal
    (lp58-t1 (lp58-shift right-root 2))
    (lp58-t1 (lp58-shift left-root 2)))
   (equal
    (lp58-t1 (lp58-shift right-root 3))
    (lp58-t1 (lp58-shift left-root 3)))))

(defun-sk lp58-source-unchanged-p
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
         ((slot (lp58-shift array index))
          (left-address
           (lp58-source-mptr-read
            left-kind
            a2 a a1 update-target havoc-start havoc-length
            second-havoc-start second-havoc-length
            item a9 a7 slot))
          (right-address
           (lp58-source-mptr-read
            right-kind
            a2 a a1 update-target havoc-start havoc-length
            second-havoc-start second-havoc-length
            item a9 a7 slot)))
       (and
        (equal left-address right-address)
        (lp58-source-eqs1-loads-p
         left-kind right-kind
         a2 a a1 update-target havoc-start havoc-length
         second-havoc-start second-havoc-length
         item a9 a7
         left-address right-address)
        (implies
         (lp58-valid-rw-p right-address 4)
         (lp58-valid-rw-p left-address 4)))))))

(defun lp58-range-index-p (index lower upper)
  (and
   (integerp index)
   (<= lower (+ 1 index))
   (<= (+ 2 index) upper)))

;; Universal quantification distributes over conjunction, so these two
;; predicates package, without changing scope, the source's nine one-index
;; hypotheses and four two-index hypotheses.

(defun-sk lp58-one-index-hypotheses-p
    (a2 a a1 update-target havoc-start havoc-length
        item array lower upper a5)
  (forall (index)
    (let*
        ((in-range
          (lp58-range-index-p index lower upper))
         (t3-value
          (lp58-t3 (lp58-shift array index)))
         (a8-value
          (lp58-a8-read
           a2 a a1 update-target havoc-start havoc-length
           (lp58-shift array index))))
      (and
       (implies
        in-range
        (not (equal t3-value item)))
       (implies
        (and in-range (lp58-is-sint32-p index))
        (not (equal t3-value item)))
       (implies
        in-range
        (lp58-separated-p a2 1 t3-value 4))
       (implies
        in-range
        (lp58-separated-p
         t3-value 4 a5 2147483646))
       (implies
        (and in-range (not (equal t3-value item)))
        (lp58-separated-p item 4 t3-value 4))
       (implies
        in-range
        (not (equal a8-value item)))
       (implies
        in-range
        (lp58-separated-p a2 1 a8-value 4))
       (implies
        in-range
        (lp58-separated-p item 4 a8-value 4))
       (implies
        in-range
        (lp58-separated-p
         a8-value 4 a5 2147483646))))))

(defun-sk lp58-two-index-hypotheses-p
    (a2 a a1 update-target havoc-start havoc-length
        array lower upper)
  (forall (left-index right-index)
    (let*
        ((both-distinct-in-range
          (and
           (lp58-range-index-p left-index lower upper)
           (lp58-range-index-p right-index lower upper)
           (not (equal left-index right-index))))
         (t3-left
          (lp58-t3 (lp58-shift array left-index)))
         (t3-right
          (lp58-t3 (lp58-shift array right-index)))
         (a8-left
          (lp58-a8-read
           a2 a a1 update-target havoc-start havoc-length
           (lp58-shift array left-index)))
         (a8-right
          (lp58-a8-read
           a2 a a1 update-target havoc-start havoc-length
           (lp58-shift array right-index))))
      (and
       (implies
        both-distinct-in-range
        (not (equal t3-left t3-right)))
       (implies
        both-distinct-in-range
        (lp58-separated-p t3-left 4 t3-right 4))
       (implies
        both-distinct-in-range
        (not (equal a8-left a8-right)))
       (implies
        both-distinct-in-range
        (lp58-separated-p a8-left 4 a8-right 4))))))

(defun-sk lp58-a13-range-property-p
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
           (lp58-a13-read
            a2 a a1 update-target havoc-start havoc-length
            second-havoc-start second-havoc-length
            (lp58-shift array index))))
       (cond
        ((equal property :separated-a2)
         (lp58-separated-p a2 1 value 4))
        ((equal property :separated-array)
         (lp58-separated-p value 4 a5 2147483646))
        (t nil))))))

(defun-sk lp58-a13-pair-property-p
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
           (lp58-a13-read
            a2 a a1 update-target havoc-start havoc-length
            second-havoc-start second-havoc-length
            (lp58-shift array left-index)))
          (right
           (lp58-a13-read
            a2 a a1 update-target havoc-start havoc-length
            second-havoc-start second-havoc-length
            (lp58-shift array right-index))))
       (cond
        ((equal property :distinct)
         (not (equal left right)))
        ((equal property :separated)
         (lp58-separated-p left 4 right 4))
        (t nil))))))

(defun-sk lp58-a13-array-swipe-right-p
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
      (lp58-a8-read
       a2 a a1 update-target havoc-start havoc-length
       (lp58-shift array (- index 1)))
      (lp58-a13-read
       a2 a a1 update-target havoc-start havoc-length
       second-havoc-start second-havoc-length
       (lp58-shift array index))))))

(defun
    ntp4vc-list-push-does-not-contain-item-post-unique-part1-goal58-instance-p
    (i i1 item array a2 a a1 i3 i2)
  (implies
   (and
    (lp58-environment-types-p)
    (lp58-l-index-of-laws-p)
    (integerp i)
    (integerp i1)
    (integerp i3)
    (integerp i2)
    (lp58-address-p item)
    (lp58-address-p array)
    (lp58-address-p a2)
    (lp58-address-p a)
    (lp58-address-p a1))
   (let*
       ((x (- i 1))
        (x1 (- (+ i i1) 1))
        (x2 (lp58-l-index-of item array x x1))
        (x3 (+ 1 x2))
        (x4 (+ i i1))
        (a5 (lp58-shift array 0))
        (a6 (lp58-t3 a2))
        (a7 (lp58-shift array x))
        (update-target
         (lp58-shift
          (lp58-t3
           (lp58-shift array (- x2 1)))
          0))
        (havoc-start (lp58-shift array x2))
        (havoc-length (- x1 x2))
        (second-havoc-start (lp58-shift array x))
        (second-havoc-length (+ 1 i1))
        (a9
         (lp58-a8-read
          a2 a a1 update-target
          havoc-start havoc-length a2)))
     (implies
      (and
       (not (equal i3 i2))
       (not (equal (lp58-null-address) item))
       (equal x3 x4)
       (< 0 i)
       (<= 0 i1)
       (< i2 x4)
       (< i3 x4)
       (<= (lp58-region (lp58-address-base a2)) 0)
       (<= (lp58-region (lp58-address-base item)) 0)
       (<= (lp58-region (lp58-address-base array)) 0)
       (< x2 x4)
       (<= i1 2147483645)
       (<= x4 2147483646)
       (<= i (+ 1 i2))
       (<= i (+ 1 i3))
       (<= i x3)
       (lp58-framed-p)
       (lp58-linked-p)
       (lp58-is-sint32-p i)
       (lp58-is-sint32-p i1)
       (lp58-valid-rw-p a2 1)
       (lp58-valid-rw-p item 4)
       (lp58-separated-p a2 1 item 4)
       (lp58-is-sint32-p x)
       (lp58-valid-rw-p a5 2147483646)
       (lp58-separated-p a2 1 a5 2147483646)
       (lp58-separated-p item 4 a5 2147483646)
       (lp58-separated-p a6 4 a5 2147483646)
       (lp58-valid-rw-p a7 i1)
       (lp58-p-linked-n-p
        :t3
        a2 a a1 update-target havoc-start havoc-length
        item a9 a7
        a6 array x i1 (lp58-null-address))
       (lp58-is-sint32-p x2)
       (lp58-separated-p a9 4 a5 2147483646)
       (lp58-eqs1-loads-p
        :a8 :t3
        a2 a a1 update-target havoc-start havoc-length
        item a9 a7
        item item)
       (lp58-p-linked-n-p
        :a8
        a2 a a1 update-target havoc-start havoc-length
        item a9 a7
        a9 array x i1 (lp58-null-address))
       (lp58-unchanged-p
        :a8 :t3
        a2 a a1 update-target havoc-start havoc-length
        item a9 a7
        array x x1)
       (lp58-source-unchanged-p
        :a11 :a10
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a9 a7
        array x x4)
       (lp58-one-index-hypotheses-p
        a2 a a1 update-target havoc-start havoc-length
        item array i x4 a5)
       (lp58-two-index-hypotheses-p
        a2 a a1 update-target havoc-start havoc-length
        array i x4)
       (equal
        (lp58-a13-read
         a2 a a1 update-target havoc-start havoc-length
         second-havoc-start second-havoc-length a2)
        a9)
       (lp58-separated-p
        (lp58-a13-read
         a2 a a1 update-target havoc-start havoc-length
         second-havoc-start second-havoc-length a2)
        4 a5 2147483646)
       (lp58-a13-range-property-p
        :separated-a2
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        array i x4 a5)
       (lp58-a13-range-property-p
        :separated-array
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        array i x4 a5)
       (lp58-a13-pair-property-p
        :separated
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        array i x4)
       (lp58-a13-pair-property-p
        :distinct
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        array x x4)
       (lp58-a13-array-swipe-right-p
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        array i x4)
       (lp58-source-p-linked-n-p
        :a13
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a9 a7
        a9 array i i1 (lp58-null-address)))
      (not
       (equal
        (lp58-a11-read
         a2 a a1 update-target havoc-start havoc-length
         second-havoc-start second-havoc-length
         item a9 a7
         (lp58-shift array i3))
        (lp58-a11-read
         a2 a a1 update-target havoc-start havoc-length
         second-havoc-start second-havoc-length
         item a9 a7
         (lp58-shift array i2))))))))

(defun-sk
    ntp4vc-list-push-does-not-contain-item-post-unique-part1-goal58-statement ()
  (forall
   (i i1 item array a2 a a1 i3 i2)
   (ntp4vc-list-push-does-not-contain-item-post-unique-part1-goal58-instance-p
    i i1 item array a2 a a1 i3 i2)))

(value-triple :itpeval-statement-checked)

:q
