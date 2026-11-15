;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_push_Why3_ide_VClist_push_contains_item_post_part4_goal29:
;; preservation of the linked-list segment after havoc and pointer updates,
;; under the generated integer bounds, memory validity, separation, framing,
;; range, swipe, uniqueness, and unchanged-memory hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lp29-address-p (address)
  (and (consp address)
       (integerp (car address))
       (integerp (cdr address))))

(defun lp29-address-base (address)
  (car address))

(defun lp29-address-offset (address)
  (cdr address))

(defun lp29-shift (address amount)
  (cons (lp29-address-base address)
        (+ (lp29-address-offset address) amount)))

(defun lp29-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2, t_3, and t_4, allocation function t, real-valued
;; memory t_1, region and linked operations, and l_index_of specialized to t_3.
;; Values of t_1 are used only through equality. Since the address domain is
;; countable, arbitrary ACL2 values preserve exactly the equality patterns
;; realizable by a real-valued source function.

(defstub lp29-t2 (address) t)
(defstub lp29-t3 (address) t)
(defstub lp29-t4 (address) t)
(defstub lp29-a16 (address) t)
(defstub lp29-malloc (index) t)
(defstub lp29-t1 (address) t)
(defstub lp29-region (base) t)
(defstub lp29-linked-op () t)
(defstub lp29-l-index-of (item array down up) t)

(defun-sk lp29-pointer-functions-p ()
  (forall (address)
    (implies
     (lp29-address-p address)
     (and (lp29-address-p (lp29-t2 address))
          (lp29-address-p (lp29-t3 address))
          (lp29-address-p (lp29-t4 address))
          (lp29-address-p (lp29-a16 address))))))

(defun-sk lp29-malloc-function-p ()
  (forall (index)
    (implies (integerp index)
             (integerp (lp29-malloc index)))))

(defun-sk lp29-region-function-p ()
  (forall (base)
    (implies (integerp base)
             (integerp (lp29-region base)))))

(defun-sk lp29-l-index-of-type-p ()
  (forall (item array down up)
    (implies
     (and (lp29-address-p item)
          (lp29-address-p array)
          (integerp down)
          (integerp up))
     (integerp (lp29-l-index-of item array down up)))))

(defun lp29-linked-p ()
  (if (lp29-linked-op) t nil))

(defun lp29-is-sint32-p (value)
  (and (integerp value)
       (<= -2147483648 value)
       (< value 2147483648)))

(defun lp29-separated-p (left left-length right right-length)
  (or (<= left-length 0)
      (<= right-length 0)
      (not (equal (lp29-address-base left)
                  (lp29-address-base right)))
      (<= (+ (lp29-address-offset right) right-length)
          (lp29-address-offset left))
      (<= (+ (lp29-address-offset left) left-length)
          (lp29-address-offset right))))

(defun lp29-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and (< 0 (lp29-address-base address))
        (<= 0 (lp29-address-offset address))
        (<= (+ (lp29-address-offset address) length)
            (lp29-malloc (lp29-address-base address))))))

(defun-sk lp29-framed-p ()
  (forall (address)
    (implies
     (lp29-address-p address)
     (<= (lp29-region
          (lp29-address-base (lp29-t3 address)))
         0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lp29-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and (lp29-address-p item)
          (lp29-address-p array)
          (integerp down)
          (integerp up))
     (and
      (implies
       (and (<= up down) (<= 0 up))
       (equal (lp29-l-index-of item array down up) up))
      (implies
       (and (equal (lp29-t3 (lp29-shift array down)) item)
            (<= 0 down)
            (< down up))
       (equal (lp29-l-index-of item array down up) down))
      (implies
       (and (not (equal (lp29-t3 (lp29-shift array down)) item))
            (<= 0 down)
            (< down up))
       (equal (lp29-l-index-of item array (+ 1 down) up)
              (lp29-l-index-of item array down up)))))))

;; M is the two successive source functional updates of t_3. The later
;; update has precedence even when the update addresses alias.

(defun lp29-m-read (a2 a a1 a10 address)
  (cond ((equal address (lp29-shift a10 0)) a1)
        ((equal address a2) a)
        (t (lp29-t3 address))))

;; A11 is the source havoc: outside the possibly modified interval it reads M,
;; and inside that interval it reads the arbitrary prior memory t_2.

(defun lp29-a11-read
    (a2 a a1 a10 havoc-start havoc-length address)
  (if (lp29-separated-p address 1 havoc-start havoc-length)
      (lp29-m-read a2 a a1 a10 address)
    (lp29-t2 address)))

;; A16 is the second source havoc. This extensional constraint makes the
;; conservative function symbol lp29-a16 exactly that let-bound map.

(defun-sk lp29-a16-definition-p
    (a2 a a1 a10 havoc-start havoc-length
        second-havoc-start second-havoc-length)
  (forall (address)
    (implies
     (lp29-address-p address)
     (equal
      (lp29-a16 address)
      (if
          (lp29-separated-p
           address 1 second-havoc-start second-havoc-length)
          (lp29-a11-read
           a2 a a1 a10 havoc-start havoc-length address)
        (lp29-t4 address))))))

(defun lp29-a13-read
    (a2 a a1 a10 havoc-start havoc-length a4 a12 a8 address)
  (declare
   (ignore a2 a a1 a10 havoc-start havoc-length))
  (cond
   ((equal address a8) a4)
   ((equal address (lp29-shift a4 0)) a12)
   (t (lp29-a16 address))))

(defun lp29-a14-read
    (a2 a a1 a10 havoc-start havoc-length a4 a12 a8 address)
  (if (equal address a2)
      a4
    (lp29-a13-read
     a2 a a1 a10 havoc-start havoc-length a4 a12 a8 address)))

(defun lp29-mptr-read
    (memory-kind a2 a a1 a10 havoc-start havoc-length
                 a4 a12 a8 address)
  (cond
   ((equal memory-kind :t3)
    (lp29-t3 address))
   ((equal memory-kind :a11)
    (lp29-a11-read
     a2 a a1 a10 havoc-start havoc-length address))
   ((equal memory-kind :a16)
    (lp29-a16 address))
   ((equal memory-kind :a13)
    (lp29-a13-read
     a2 a a1 a10 havoc-start havoc-length a4 a12 a8 address))
   ((equal memory-kind :a14)
    (lp29-a14-read
     a2 a a1 a10 havoc-start havoc-length a4 a12 a8 address))
   (t nil)))

;; A true list of N successive roots is constructor evidence for the source
;; inductive p_linked_n relation. The empty witness is exactly its bound
;; constructor; every cons cell is one cons constructor.

(defun lp29-linked-steps-p
    (memory-kind a2 a a1 a10 havoc-start havoc-length
                 a4 a12 a8 roots root array index bound)
  (if (consp roots)
      (and
       (lp29-address-p root)
       (equal (car roots) root)
       (equal
        (lp29-mptr-read
         memory-kind a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8 (lp29-shift array index))
        root)
       (lp29-valid-rw-p root 4)
       (lp29-linked-steps-p
        memory-kind a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 (cdr roots)
        (lp29-mptr-read
         memory-kind a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8 (lp29-shift root 0))
        array (+ 1 index) bound))
    (and (equal roots nil)
         (equal root bound))))

(defun-sk lp29-p-linked-n-p
    (memory-kind a2 a a1 a10 havoc-start havoc-length
                 a4 a12 a8 root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:t3 :a11 :a16 :a14))
     (lp29-address-p root)
     (lp29-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lp29-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lp29-linked-steps-p
      memory-kind a2 a a1 a10 havoc-start havoc-length
      a4 a12 a8 roots root array index bound))))

;; This unfolds load_s1_list and eqs1_list. Pointer fields are read through
;; the selected pointer memories and the three scalar fields through t_1.

(defun lp29-eqs1-loads-p
    (left-kind right-kind a2 a a1 a10 havoc-start havoc-length
               a4 a12 a8 left-root right-root)
  (and
   (equal
    (lp29-mptr-read
     right-kind a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 (lp29-shift right-root 0))
    (lp29-mptr-read
     left-kind a2 a a1 a10 havoc-start havoc-length
     a4 a12 a8 (lp29-shift left-root 0)))
   (equal (lp29-t1 (lp29-shift right-root 1))
          (lp29-t1 (lp29-shift left-root 1)))
   (equal (lp29-t1 (lp29-shift right-root 2))
          (lp29-t1 (lp29-shift left-root 2)))
   (equal (lp29-t1 (lp29-shift right-root 3))
          (lp29-t1 (lp29-shift left-root 3)))))

(defun-sk lp29-unchanged-p
    (left-kind right-kind a2 a a1 a10 havoc-start havoc-length
               a4 a12 a8 array down up)
  (forall (index)
    (implies
     (and (integerp index) (<= down index) (< index up))
     (let*
         ((slot (lp29-shift array index))
          (left-address
           (lp29-mptr-read
            left-kind a2 a a1 a10 havoc-start havoc-length
            a4 a12 a8 slot))
          (right-address
           (lp29-mptr-read
            right-kind a2 a a1 a10 havoc-start havoc-length
            a4 a12 a8 slot)))
       (and
        (equal left-address right-address)
        (lp29-eqs1-loads-p
         left-kind right-kind a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8 left-address right-address)
        (implies (lp29-valid-rw-p right-address 4)
                 (lp29-valid-rw-p left-address 4)))))))

(defun-sk lp29-a4-in-t3-range-p (a4 array lower upper)
  (exists (index)
    (and
     (integerp index)
     (equal a4 (lp29-t3 (lp29-shift array index)))
     (< index upper)
     (<= lower (+ 1 index)))))

(defun-sk lp29-a4-not-in-t3-range-p (a4 array lower upper)
  (forall (index)
    (implies
     (and (integerp index)
          (< index upper)
          (<= lower (+ 1 index)))
     (not (equal a4 (lp29-t3 (lp29-shift array index)))))))

(defun-sk lp29-array-swipe-left-p
    (a2 a a1 a10 havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and (integerp index) (<= down index) (< index up))
     (equal
      (lp29-t3 (lp29-shift array (+ 1 index)))
      (lp29-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp29-shift array index))))))

;; SHIFTEDP selects the source branch 2+i <= upper instead of i < upper.

(defun lp29-range-index-p (index lower upper shiftedp)
  (and (integerp index)
       (<= lower (+ 1 index))
       (if shiftedp
           (<= (+ 2 index) upper)
         (< index upper))))

;; The four property tags package source universal hypotheses with identical
;; integer ranges without changing their quantifier scopes.

(defun-sk lp29-a11-range-property-p
    (property a2 a a1 a10 havoc-start havoc-length
              a4 array lower upper array-base shiftedp)
  (forall (index)
    (implies
     (lp29-range-index-p index lower upper shiftedp)
     (let ((value
            (lp29-a11-read
             a2 a a1 a10 havoc-start havoc-length
             (lp29-shift array index))))
       (cond
        ((equal property :not-a4)
         (not (equal value a4)))
        ((equal property :separated-a2)
         (lp29-separated-p a2 1 value 4))
        ((equal property :separated-a4)
         (lp29-separated-p a4 4 value 4))
        ((equal property :separated-array)
         (lp29-separated-p value 4 array-base 2147483646))
        (t nil))))))

(defun-sk lp29-a11-loads-equal-t3-successors-p
    (a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 array lower upper)
  (forall (index)
    (implies
     (and (integerp index)
          (<= lower index)
          (<= (+ 2 index) upper))
     (lp29-eqs1-loads-p
      :a11 :t3 a2 a a1 a10 havoc-start havoc-length
      a4 a12 a8
      (lp29-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp29-shift array index))
      (lp29-t3 (lp29-shift array (+ 1 index)))))))

(defun-sk lp29-a11-pair-property-p
    (property a2 a a1 a10 havoc-start havoc-length
              array lower upper shiftedp)
  (forall (left-index right-index)
    (implies
     (and
      (lp29-range-index-p left-index lower upper shiftedp)
      (lp29-range-index-p right-index lower upper shiftedp)
      (not (equal left-index right-index)))
     (let ((left
            (lp29-a11-read
             a2 a a1 a10 havoc-start havoc-length
             (lp29-shift array left-index)))
           (right
            (lp29-a11-read
             a2 a a1 a10 havoc-start havoc-length
             (lp29-shift array right-index))))
       (cond
        ((equal property :distinct)
         (not (equal left right)))
        ((equal property :separated)
         (lp29-separated-p left 4 right 4))
        (t nil))))))

(defun-sk lp29-t3-range-property-p
    (property a2 a4 a5 array lower upper array-base)
  (forall (index)
    (implies
     (lp29-range-index-p index lower upper nil)
     (let ((value (lp29-t3 (lp29-shift array index))))
       (cond
        ((equal property :separated-a2)
         (lp29-separated-p a2 1 value 4))
        ((equal property :separated-array)
         (lp29-separated-p value 4 array-base 2147483646))
        ((equal property :separated-a5)
         (implies (not (equal a5 value))
                  (lp29-separated-p a5 4 value 4)))
        ((equal property :separated-a4)
         (implies (not (equal a4 value))
                  (lp29-separated-p a4 4 value 4)))
        (t nil))))))

(defun-sk lp29-t3-pair-property-p
    (property array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (lp29-range-index-p left-index lower upper nil)
      (lp29-range-index-p right-index lower upper nil)
      (not (equal left-index right-index)))
     (let ((left (lp29-t3 (lp29-shift array left-index)))
           (right (lp29-t3 (lp29-shift array right-index))))
       (cond
        ((equal property :distinct)
         (not (equal left right)))
        ((equal property :separated)
         (lp29-separated-p left 4 right 4))
        (t nil))))))

(defun-sk lp29-a2-separated-a16-range-p
    (a2 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lp29-separated-p
      a2 1
      (lp29-a16 (lp29-shift array index))
      4))))

(defun-sk lp29-a16-range-separated-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lp29-separated-p
      (lp29-a16 (lp29-shift array index))
      4
      array-base
      2147483646))))

(defun-sk lp29-a16-range-separated-p
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
     (lp29-separated-p
      (lp29-a16 (lp29-shift array left-index))
      4
      (lp29-a16 (lp29-shift array right-index))
      4))))

(defun-sk lp29-a16-range-distinct-p
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
       (lp29-a16 (lp29-shift array left-index))
       (lp29-a16 (lp29-shift array right-index)))))))

(defun-sk lp29-array-swipe-right-a16-a11-p
    (a2 a a1 a10 havoc-start havoc-length
        array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lp29-a11-read
       a2 a a1 a10 havoc-start havoc-length
       (lp29-shift array (- index 1)))
      (lp29-a16 (lp29-shift array index))))))

(defun lp29-goal29-instance-p (a3 i3 i2 i1 i a2 a a1)
  (implies
   (and
    (lp29-pointer-functions-p)
    (lp29-malloc-function-p)
    (lp29-region-function-p)
    (lp29-l-index-of-type-p)
    (lp29-l-index-of-laws-p)
    (lp29-address-p a3)
    (integerp i3)
    (integerp i2)
    (integerp i1)
    (integerp i)
    (lp29-address-p a2)
    (lp29-address-p a)
    (lp29-address-p a1))
   (let*
       ((a4 (lp29-t3 (lp29-shift a3 i3)))
        (a5 (lp29-t3 (lp29-shift a3 i2)))
        (x (- i1 1))
        (x1 (+ i i1))
        (x2 (lp29-l-index-of a4 a3 x x1))
        (x3 (+ 1 i))
        (a6 (lp29-shift a3 0))
        (a7 (lp29-t3 a2))
        (a8 (lp29-shift a3 x))
        (x4 (- x2 1))
        (a9 (lp29-shift a3 x4))
        (a10 (lp29-t3 a9))
        (havoc-start (lp29-shift a3 x2))
        (havoc-length (- (+ i i1) x2))
        (a12
         (lp29-a11-read
          a2 a a1 a10 havoc-start havoc-length a2))
        (in-range
         (lp29-a4-in-t3-range-p a4 a3 i1 x1))
        (not-in-range
         (lp29-a4-not-in-t3-range-p a4 a3 i1 x1)))
     (implies
      (and
       (lp29-a16-definition-p
        a2 a a1 a10 havoc-start havoc-length
        a8 x3)
       (not (equal a4 (lp29-null-address)))
       (equal a4 a5)
       (equal x2 (lp29-l-index-of a5 a3 x x1))
       (not (equal x1 x2))
       (< 0 i1)
       (< i2 x1)
       (< i3 x1)
       (<= (lp29-region (lp29-address-base a2)) 0)
       (<= (lp29-region (lp29-address-base a3)) 0)
       (<= (lp29-region (lp29-address-base a4)) 0)
       (< x2 x1)
       (<= x2 x1)
       (<= -1 i)
       (<= i 2147483644)
       (<= x1 2147483645)
       (<= i1 (+ 1 i2))
       (<= i1 (+ 1 i3))
       (<= i1 (+ 1 x2))
       (lp29-framed-p)
       (lp29-linked-p)
       (lp29-is-sint32-p i)
       (lp29-is-sint32-p i1)
       (lp29-valid-rw-p a2 1)
       (lp29-is-sint32-p x)
       (lp29-is-sint32-p x3)
       (lp29-valid-rw-p a6 2147483646)
       (lp29-valid-rw-p a5 4)
       (lp29-separated-p a2 1 a6 2147483646)
       (lp29-separated-p a7 4 a6 2147483646)
       (lp29-separated-p a2 1 a5 4)
       (lp29-separated-p a5 4 a6 2147483646)
       (lp29-valid-rw-p a8 x3)
       (lp29-p-linked-n-p
        :t3 a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 a7 a3 x x3 (lp29-null-address))
       (lp29-is-sint32-p x2)
       (lp29-separated-p a12 4 a6 2147483646)
       (lp29-eqs1-loads-p
        :a11 :t3 a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 a4 a4)
       (lp29-unchanged-p
        :a14 :a13 a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 a3 x x1)
       (implies
        (and (<= i1 x2) in-range)
        (equal
         (lp29-a11-read
          a2 a a1 a10 havoc-start havoc-length a9)
         a10))
       (implies
        in-range
        (lp29-array-swipe-left-p
         a2 a a1 a10 havoc-start havoc-length
         a3 x2 (- (+ i i1) 1)))
       (implies
        not-in-range
        (lp29-a11-range-property-p
         :not-a4 a2 a a1 a10 havoc-start havoc-length
         a4 a3 i1 x1 a6 nil))
       (implies
        in-range
        (lp29-a11-range-property-p
         :not-a4 a2 a a1 a10 havoc-start havoc-length
         a4 a3 i1 x1 a6 t))
       (implies
        in-range
        (lp29-p-linked-n-p
         :a11 a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8 a12 a3 x i (lp29-null-address)))
       (implies
        not-in-range
        (lp29-p-linked-n-p
         :a11 a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8 a12 a3 x x3 (lp29-null-address)))
       (implies
        not-in-range
        (lp29-unchanged-p
         :a11 :t3 a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8 a3 x x1))
       (implies
        in-range
        (lp29-unchanged-p
         :a11 :t3 a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8 a3 x x4))
       (implies
        not-in-range
        (lp29-a11-range-property-p
         :separated-a2 a2 a a1 a10 havoc-start havoc-length
         a4 a3 i1 x1 a6 nil))
       (implies
        in-range
        (lp29-a11-range-property-p
         :separated-a2 a2 a a1 a10 havoc-start havoc-length
         a4 a3 i1 x1 a6 t))
       (implies
        not-in-range
        (lp29-a11-range-property-p
         :separated-a4 a2 a a1 a10 havoc-start havoc-length
         a4 a3 i1 x1 a6 nil))
       (implies
        in-range
        (lp29-a11-range-property-p
         :separated-a4 a2 a a1 a10 havoc-start havoc-length
         a4 a3 i1 x1 a6 t))
       (implies
        not-in-range
        (lp29-a11-range-property-p
         :separated-array a2 a a1 a10 havoc-start havoc-length
         a4 a3 i1 x1 a6 nil))
       (implies
        in-range
        (lp29-a11-range-property-p
         :separated-array a2 a a1 a10 havoc-start havoc-length
         a4 a3 i1 x1 a6 t))
       (implies
        in-range
        (lp29-a11-loads-equal-t3-successors-p
         a2 a a1 a10 havoc-start havoc-length
         a4 a12 a8 a3 x2 x1))
       (implies
        not-in-range
        (lp29-a11-pair-property-p
         :distinct a2 a a1 a10 havoc-start havoc-length
         a3 i1 x1 nil))
       (implies
        in-range
        (lp29-a11-pair-property-p
         :distinct a2 a a1 a10 havoc-start havoc-length
         a3 i1 x1 t))
       (implies
        not-in-range
        (lp29-a11-pair-property-p
         :separated a2 a a1 a10 havoc-start havoc-length
         a3 i1 x1 nil))
       (implies
        in-range
        (lp29-a11-pair-property-p
         :separated a2 a a1 a10 havoc-start havoc-length
         a3 i1 x1 t))
       (lp29-t3-range-property-p
        :separated-a2 a2 a4 a5 a3 i1 x1 a6)
       (lp29-t3-range-property-p
        :separated-array a2 a4 a5 a3 i1 x1 a6)
       (lp29-t3-range-property-p
        :separated-a5 a2 a4 a5 a3 i1 x1 a6)
       (lp29-t3-range-property-p
        :separated-a4 a2 a4 a5 a3 i1 x1 a6)
       (lp29-t3-pair-property-p :distinct a3 i1 x1)
       (lp29-t3-pair-property-p :separated a3 i1 x1)
       (equal (lp29-a16 a2) a12)
       (lp29-separated-p
        (lp29-a16 a2) 4 a6 2147483646)
       (lp29-a2-separated-a16-range-p
        a2 a3 i1 x1)
       (lp29-a16-range-separated-array-p
        a3 i1 x1 a6)
       (lp29-a16-range-separated-p
        a3 i1 x1)
       (lp29-a16-range-distinct-p
        a3 x x1)
       (lp29-array-swipe-right-a16-a11-p
        a2 a a1 a10 havoc-start havoc-length
        a3 i1 x1)
       (lp29-p-linked-n-p
        :a16 a2 a a1 a10 havoc-start havoc-length
        a4 a12 a8 a12 a3 i1 i (lp29-null-address)))
      (lp29-p-linked-n-p
       :a14 a2 a a1 a10 havoc-start havoc-length
       a4 a12 a8 a4 a3 x x3 (lp29-null-address))))))

(defun-sk
    ntp4vc-list-push-contains-item-post-part4-goal29-statement ()
  (forall (a3 i3 i2 i1 i a2 a a1)
    (lp29-goal29-instance-p a3 i3 i2 i1 i a2 a a1)))

(value-triple :itpeval-statement-checked)

:q
