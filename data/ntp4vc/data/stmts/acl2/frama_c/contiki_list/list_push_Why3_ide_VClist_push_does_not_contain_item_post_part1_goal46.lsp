;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_push_Why3_ide_VClist_push_does_not_contain_item_post_part1_goal46:
;; preservation of a linked-list array segment after two pointer-memory havocs
;; and pointer updates, under integer bounds, memory validity, framing,
;; separation, unchanged-memory, non-membership, and uniqueness hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lp46-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lp46-address-base (address)
  (car address))

(defun lp46-address-offset (address)
  (cdr address))

(defun lp46-shift (address amount)
  (cons
   (lp46-address-base address)
   (+ (lp46-address-offset address) amount)))

(defun lp46-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2, t_3, and t_4, allocation function t, real-valued
;; memory t_1, region and linked operations, and l_index_of specialized to t_3.
;; Values of t_1 are used only through equality. Since the address domain is
;; countable, arbitrary ACL2 values preserve exactly the equality patterns
;; realizable by a real-valued source function.

(defstub lp46-t2 (address) t)
(defstub lp46-t3 (address) t)
(defstub lp46-t4 (address) t)
(defstub lp46-malloc (index) t)
(defstub lp46-t1 (address) t)
(defstub lp46-region (base) t)
(defstub lp46-linked-op () t)
(defstub lp46-l-index-of (item array down up) t)

(defun-sk lp46-environment-types-p ()
  (forall (address index base item array down up)
    (and
     (implies
      (lp46-address-p address)
      (and
       (lp46-address-p (lp46-t2 address))
       (lp46-address-p (lp46-t3 address))
       (lp46-address-p (lp46-t4 address))))
     (implies
      (integerp index)
      (integerp (lp46-malloc index)))
     (implies
      (integerp base)
      (integerp (lp46-region base)))
     (implies
      (and
       (lp46-address-p item)
       (lp46-address-p array)
       (integerp down)
       (integerp up))
      (integerp
       (lp46-l-index-of item array down up))))))

(defun lp46-linked-p ()
  (if (lp46-linked-op) t nil))

(defun lp46-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lp46-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lp46-address-base left)
     (lp46-address-base right)))
   (<=
    (+ (lp46-address-offset right) right-length)
    (lp46-address-offset left))
   (<=
    (+ (lp46-address-offset left) left-length)
    (lp46-address-offset right))))

(defun lp46-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lp46-address-base address))
    (<= 0 (lp46-address-offset address))
    (<=
     (+ (lp46-address-offset address) length)
     (lp46-malloc (lp46-address-base address))))))

(defun-sk lp46-framed-p ()
  (forall (address)
    (implies
     (lp46-address-p address)
     (<=
      (lp46-region
       (lp46-address-base (lp46-t3 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lp46-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lp46-address-p item)
      (lp46-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lp46-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lp46-t3 (lp46-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lp46-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lp46-t3 (lp46-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lp46-l-index-of item array (+ 1 down) up)
        (lp46-l-index-of item array down up)))))))

;; M is the two successive source functional updates of t_3. The second
;; update has precedence even when the update addresses alias.

(defun lp46-m-read
    (a2 a a1 update-target address)
  (cond
   ((equal address update-target) a1)
   ((equal address a2) a)
   (t (lp46-t3 address))))

;; A8 is the source havoc: outside the possibly modified interval it reads M,
;; and inside that interval it reads the arbitrary prior memory t_2.

(defun lp46-a8-read
    (a2 a a1 update-target
        havoc-start havoc-length address)
  (if
      (lp46-separated-p address 1 havoc-start havoc-length)
      (lp46-m-read a2 a a1 update-target address)
    (lp46-t2 address)))

;; A13 is the second source havoc: outside its interval it reads A8, and
;; inside it reads the arbitrary t_4. A10 and A11 are the subsequent source
;; functional updates, with the later update taking precedence.

(defun lp46-a13-read
    (a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length address)
  (if
      (lp46-separated-p
       address 1 second-havoc-start second-havoc-length)
      (lp46-a8-read
       a2 a a1 update-target havoc-start havoc-length address)
    (lp46-t4 address)))

(defun lp46-a10-read
    (a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a9 a7 address)
  (cond
   ((equal address a7) item)
   ((equal address (lp46-shift item 0)) a9)
   (t
    (lp46-a13-read
     a2 a a1 update-target
     havoc-start havoc-length
     second-havoc-start second-havoc-length address))))

(defun lp46-a11-read
    (a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a9 a7 address)
  (if (equal address a2)
      item
    (lp46-a10-read
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7 address)))

(defun lp46-mptr-read
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7 address)
  (declare (ignore item a9 a7))
  (cond
   ((equal memory-kind :t3)
    (lp46-t3 address))
   ((equal memory-kind :a8)
    (lp46-a8-read
     a2 a a1 update-target havoc-start havoc-length address))
   (t nil)))

(defun lp46-source-mptr-read
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7 address)
  (cond
   ((equal memory-kind :a13)
    (lp46-a13-read
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length address))
   ((equal memory-kind :a10)
    (lp46-a10-read
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7 address))
   ((equal memory-kind :a11)
    (lp46-a11-read
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7 address))
   (t nil)))

;; A true list of N successive roots is constructor evidence for the source
;; inductive p_linked_n relation. The empty witness is exactly its bound
;; constructor; every cons cell is one cons constructor and advances both the
;; array index and next pointer.

(defun lp46-linked-steps-p
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     roots root array index bound)
  (if (consp roots)
      (and
       (lp46-address-p root)
       (equal (car roots) root)
       (equal
        (lp46-mptr-read
         memory-kind
         a2 a a1 update-target havoc-start havoc-length
         item a9 a7
         (lp46-shift array index))
        root)
       (lp46-valid-rw-p root 4)
       (lp46-linked-steps-p
        memory-kind
        a2 a a1 update-target havoc-start havoc-length
        item a9 a7
        (cdr roots)
        (lp46-mptr-read
         memory-kind
         a2 a a1 update-target havoc-start havoc-length
         item a9 a7
         (lp46-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lp46-p-linked-n-p
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:t3 :a8))
     (lp46-address-p root)
     (lp46-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lp46-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lp46-linked-steps-p
      memory-kind
      a2 a a1 update-target havoc-start havoc-length
      item a9 a7
      roots root array index bound))))

(defun lp46-source-linked-steps-p
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     roots root array index bound)
  (if (consp roots)
      (and
       (lp46-address-p root)
       (equal (car roots) root)
       (equal
        (lp46-source-mptr-read
         memory-kind
         a2 a a1 update-target havoc-start havoc-length
         second-havoc-start second-havoc-length
         item a9 a7
         (lp46-shift array index))
        root)
       (lp46-valid-rw-p root 4)
       (lp46-source-linked-steps-p
        memory-kind
        a2 a a1 update-target havoc-start havoc-length
        second-havoc-start second-havoc-length
        item a9 a7
        (cdr roots)
        (lp46-source-mptr-read
         memory-kind
         a2 a a1 update-target havoc-start havoc-length
         second-havoc-start second-havoc-length
         item a9 a7
         (lp46-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lp46-source-p-linked-n-p
    (memory-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:a13 :a11))
     (lp46-address-p root)
     (lp46-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lp46-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lp46-source-linked-steps-p
      memory-kind
      a2 a a1 update-target havoc-start havoc-length
      second-havoc-start second-havoc-length
      item a9 a7
      roots root array index bound))))

;; This unfolds load_s1_list and eqs1_list. Pointer fields are read through
;; the selected pointer memories and the three scalar fields through t_1.

(defun lp46-eqs1-loads-p
    (left-kind right-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     left-root right-root)
  (and
   (equal
    (lp46-mptr-read
     right-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     (lp46-shift right-root 0))
    (lp46-mptr-read
     left-kind
     a2 a a1 update-target havoc-start havoc-length
     item a9 a7
     (lp46-shift left-root 0)))
   (equal
    (lp46-t1 (lp46-shift right-root 1))
    (lp46-t1 (lp46-shift left-root 1)))
   (equal
    (lp46-t1 (lp46-shift right-root 2))
    (lp46-t1 (lp46-shift left-root 2)))
   (equal
    (lp46-t1 (lp46-shift right-root 3))
    (lp46-t1 (lp46-shift left-root 3)))))

;; This is p_unchanged with the common malloc and real-valued memories
;; specialized to t and t_1, but with both pointer memories left explicit.

(defun-sk lp46-unchanged-p
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
         ((slot (lp46-shift array index))
          (left-address
           (lp46-mptr-read
            left-kind
            a2 a a1 update-target havoc-start havoc-length
            item a9 a7 slot))
          (right-address
           (lp46-mptr-read
            right-kind
            a2 a a1 update-target havoc-start havoc-length
            item a9 a7 slot)))
       (and
        (equal left-address right-address)
        (lp46-eqs1-loads-p
         left-kind right-kind
         a2 a a1 update-target havoc-start havoc-length
         item a9 a7
         left-address right-address)
        (implies
         (lp46-valid-rw-p right-address 4)
         (lp46-valid-rw-p left-address 4)))))))

(defun lp46-source-eqs1-loads-p
    (left-kind right-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     left-root right-root)
  (and
   (equal
    (lp46-source-mptr-read
     right-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     (lp46-shift right-root 0))
    (lp46-source-mptr-read
     left-kind
     a2 a a1 update-target havoc-start havoc-length
     second-havoc-start second-havoc-length
     item a9 a7
     (lp46-shift left-root 0)))
   (equal
    (lp46-t1 (lp46-shift right-root 1))
    (lp46-t1 (lp46-shift left-root 1)))
   (equal
    (lp46-t1 (lp46-shift right-root 2))
    (lp46-t1 (lp46-shift left-root 2)))
   (equal
    (lp46-t1 (lp46-shift right-root 3))
    (lp46-t1 (lp46-shift left-root 3)))))

(defun-sk lp46-source-unchanged-p
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
         ((slot (lp46-shift array index))
          (left-address
           (lp46-source-mptr-read
            left-kind
            a2 a a1 update-target havoc-start havoc-length
            second-havoc-start second-havoc-length
            item a9 a7 slot))
          (right-address
           (lp46-source-mptr-read
            right-kind
            a2 a a1 update-target havoc-start havoc-length
            second-havoc-start second-havoc-length
            item a9 a7 slot)))
       (and
        (equal left-address right-address)
        (lp46-source-eqs1-loads-p
         left-kind right-kind
         a2 a a1 update-target havoc-start havoc-length
         second-havoc-start second-havoc-length
         item a9 a7
         left-address right-address)
        (implies
         (lp46-valid-rw-p right-address 4)
         (lp46-valid-rw-p left-address 4)))))))

(defun lp46-range-index-p (index lower upper)
  (and
   (integerp index)
   (<= lower (+ 1 index))
   (<= (+ 2 index) upper)))

;; Universal quantification distributes over conjunction, so these two
;; predicates package, without changing scope, the source's nine one-index
;; hypotheses and four two-index hypotheses.

(defun-sk lp46-one-index-hypotheses-p
    (a2 a a1 update-target havoc-start havoc-length
        item array lower upper a5)
  (forall (index)
    (let*
        ((in-range
          (lp46-range-index-p index lower upper))
         (t3-value
          (lp46-t3 (lp46-shift array index)))
         (a8-value
          (lp46-a8-read
           a2 a a1 update-target havoc-start havoc-length
           (lp46-shift array index))))
      (and
       (implies
        in-range
        (not (equal t3-value item)))
       (implies
        (and in-range (lp46-is-sint32-p index))
        (not (equal t3-value item)))
       (implies
        in-range
        (lp46-separated-p a2 1 t3-value 4))
       (implies
        in-range
        (lp46-separated-p
         t3-value 4 a5 2147483646))
       (implies
        (and in-range (not (equal t3-value item)))
        (lp46-separated-p item 4 t3-value 4))
       (implies
        in-range
        (not (equal a8-value item)))
       (implies
        in-range
        (lp46-separated-p a2 1 a8-value 4))
       (implies
        in-range
        (lp46-separated-p item 4 a8-value 4))
       (implies
        in-range
        (lp46-separated-p
         a8-value 4 a5 2147483646))))))

(defun-sk lp46-two-index-hypotheses-p
    (a2 a a1 update-target havoc-start havoc-length
        array lower upper)
  (forall (left-index right-index)
    (let*
        ((both-distinct-in-range
          (and
           (lp46-range-index-p left-index lower upper)
           (lp46-range-index-p right-index lower upper)
           (not (equal left-index right-index))))
         (t3-left
          (lp46-t3 (lp46-shift array left-index)))
         (t3-right
          (lp46-t3 (lp46-shift array right-index)))
         (a8-left
          (lp46-a8-read
           a2 a a1 update-target havoc-start havoc-length
           (lp46-shift array left-index)))
         (a8-right
          (lp46-a8-read
           a2 a a1 update-target havoc-start havoc-length
           (lp46-shift array right-index))))
      (and
       (implies
        both-distinct-in-range
        (not (equal t3-left t3-right)))
       (implies
        both-distinct-in-range
        (lp46-separated-p t3-left 4 t3-right 4))
       (implies
        both-distinct-in-range
        (not (equal a8-left a8-right)))
       (implies
        both-distinct-in-range
        (lp46-separated-p a8-left 4 a8-right 4))))))

(defun-sk lp46-a13-range-property-p
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
           (lp46-a13-read
            a2 a a1 update-target havoc-start havoc-length
            second-havoc-start second-havoc-length
            (lp46-shift array index))))
       (cond
        ((equal property :separated-a2)
         (lp46-separated-p a2 1 value 4))
        ((equal property :separated-array)
         (lp46-separated-p value 4 a5 2147483646))
        (t nil))))))

(defun-sk lp46-a13-pair-property-p
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
           (lp46-a13-read
            a2 a a1 update-target havoc-start havoc-length
            second-havoc-start second-havoc-length
            (lp46-shift array left-index)))
          (right
           (lp46-a13-read
            a2 a a1 update-target havoc-start havoc-length
            second-havoc-start second-havoc-length
            (lp46-shift array right-index))))
       (cond
        ((equal property :distinct)
         (not (equal left right)))
        ((equal property :separated)
         (lp46-separated-p left 4 right 4))
        (t nil))))))

(defun-sk lp46-array-swipe-right-p
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
      (lp46-a8-read
       a2 a a1 update-target havoc-start havoc-length
       (lp46-shift array (- index 1)))
      (lp46-a13-read
       a2 a a1 update-target havoc-start havoc-length
       second-havoc-start second-havoc-length
       (lp46-shift array index))))))

(defun
    ntp4vc-list-push-does-not-contain-item-post-part1-goal46-instance-p
    (i i1 item array a2 a a1)
  (implies
   (and
    (lp46-environment-types-p)
    (lp46-l-index-of-laws-p)
    (integerp i)
    (integerp i1)
    (lp46-address-p item)
    (lp46-address-p array)
    (lp46-address-p a2)
    (lp46-address-p a)
    (lp46-address-p a1))
   (let*
       ((x (- i 1))
        (x1 (- (+ i i1) 1))
        (x2 (lp46-l-index-of item array x x1))
        (x3 (+ 1 x2))
        (x4 (+ i i1))
        (a5 (lp46-shift array 0))
        (a6 (lp46-t3 a2))
        (a7 (lp46-shift array x))
        (update-target
         (lp46-shift
          (lp46-t3
           (lp46-shift array (- x2 1)))
	          0))
	        (havoc-start (lp46-shift array x2))
	        (havoc-length (- x1 x2))
	        (second-havoc-start (lp46-shift array x))
	        (second-havoc-length (+ 1 i1))
	        (a9
	         (lp46-a8-read
	          a2 a a1 update-target
          havoc-start havoc-length a2)))
     (implies
      (and
       (not (equal (lp46-null-address) item))
       (equal x3 x4)
       (< 0 i)
       (<= 0 i1)
       (<= (lp46-region (lp46-address-base a2)) 0)
       (<= (lp46-region (lp46-address-base item)) 0)
       (<= (lp46-region (lp46-address-base array)) 0)
       (< x2 x4)
       (<= i1 2147483645)
       (<= x4 2147483646)
       (<= i x3)
       (lp46-framed-p)
       (lp46-linked-p)
       (lp46-is-sint32-p i)
       (lp46-is-sint32-p i1)
       (lp46-valid-rw-p a2 1)
       (lp46-valid-rw-p item 4)
       (lp46-separated-p a2 1 item 4)
       (lp46-is-sint32-p x)
       (lp46-valid-rw-p a5 2147483646)
       (lp46-separated-p a2 1 a5 2147483646)
       (lp46-separated-p item 4 a5 2147483646)
       (lp46-separated-p a6 4 a5 2147483646)
       (lp46-valid-rw-p a7 i1)
       (lp46-p-linked-n-p
        :t3
        a2 a a1 update-target havoc-start havoc-length
        item a9 a7
        a6 array x i1 (lp46-null-address))
       (lp46-is-sint32-p x2)
       (lp46-separated-p a9 4 a5 2147483646)
       (lp46-eqs1-loads-p
        :a8 :t3
        a2 a a1 update-target havoc-start havoc-length
        item a9 a7
        item item)
       (lp46-p-linked-n-p
        :a8
        a2 a a1 update-target havoc-start havoc-length
        item a9 a7
        a9 array x i1 (lp46-null-address))
	       (lp46-unchanged-p
	        :a8 :t3
	        a2 a a1 update-target havoc-start havoc-length
	        item a9 a7
	        array x x1)
	       (lp46-source-unchanged-p
	        :a11 :a10
	        a2 a a1 update-target havoc-start havoc-length
	        second-havoc-start second-havoc-length
	        item a9 a7
	        array x x4)
	       (lp46-one-index-hypotheses-p
        a2 a a1 update-target havoc-start havoc-length
        item array i x4 a5)
	       (lp46-two-index-hypotheses-p
	        a2 a a1 update-target havoc-start havoc-length
	        array i x4)
	       (equal
	        (lp46-a13-read
	         a2 a a1 update-target havoc-start havoc-length
	         second-havoc-start second-havoc-length a2)
	        a9)
	       (lp46-separated-p
	        (lp46-a13-read
	         a2 a a1 update-target havoc-start havoc-length
	         second-havoc-start second-havoc-length a2)
	        4 a5 2147483646)
	       (lp46-a13-range-property-p
	        :separated-a2
	        a2 a a1 update-target havoc-start havoc-length
	        second-havoc-start second-havoc-length
	        array i x4 a5)
	       (lp46-a13-range-property-p
	        :separated-array
	        a2 a a1 update-target havoc-start havoc-length
	        second-havoc-start second-havoc-length
	        array i x4 a5)
	       (lp46-a13-pair-property-p
	        :separated
	        a2 a a1 update-target havoc-start havoc-length
	        second-havoc-start second-havoc-length
	        array i x4)
	       (lp46-a13-pair-property-p
	        :distinct
	        a2 a a1 update-target havoc-start havoc-length
	        second-havoc-start second-havoc-length
	        array x x4)
	       (lp46-array-swipe-right-p
	        a2 a a1 update-target havoc-start havoc-length
	        second-havoc-start second-havoc-length
	        array i x4)
	       (lp46-source-p-linked-n-p
	        :a13
	        a2 a a1 update-target havoc-start havoc-length
	        second-havoc-start second-havoc-length
	        item a9 a7
	        a9 array i i1 (lp46-null-address)))
	      (lp46-source-p-linked-n-p
	       :a11
	        a2 a a1 update-target havoc-start havoc-length
	       second-havoc-start second-havoc-length
	       item a9 a7
	       item array x (+ 1 i1) (lp46-null-address))))))

(defun-sk
    ntp4vc-list-push-does-not-contain-item-post-part1-goal46-statement ()
  (forall
   (i i1 item array a2 a a1)
   (ntp4vc-list-push-does-not-contain-item-post-part1-goal46-instance-p
    i i1 item array a2 a a1)))

(value-triple :itpeval-statement-checked)

:q
