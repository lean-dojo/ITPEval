;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_add_Why3_ide_VClist_add_call_list_final_add_pre_Separation_2_part4_goal54:
;; separation of two distinct updated list elements after a range havoc and
;; pointer update in the final list-add verification condition. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lag54-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lag54-address-base (address)
  (car address))

(defun lag54-address-offset (address)
  (cdr address))

(defun lag54-shift (address amount)
  (cons
   (lag54-address-base address)
   (+ (lag54-address-offset address) amount)))

(defun lag54-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2 and t_3, allocation function t, real-valued memory
;; t_1, region and linked operations, and l_index_of specialized to t_3.
;; Values of t_1 are only compared for equality in this VC.  Since the
;; address domain is countable, arbitrary ACL2 values preserve exactly the
;; equality patterns realizable by a real-valued function.

(defstub lag54-t2 (address) t)
(defstub lag54-t3 (address) t)
(defstub lag54-malloc (index) t)
(defstub lag54-t1 (address) t)
(defstub lag54-region (base) t)
(defstub lag54-linked-op () t)
(defstub lag54-l-index-of (item array down up) t)

(defun-sk lag54-pointer-functions-p ()
  (forall (address)
    (implies
     (lag54-address-p address)
     (and
      (lag54-address-p (lag54-t2 address))
      (lag54-address-p (lag54-t3 address))))))

(defun-sk lag54-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lag54-malloc index)))))

(defun-sk lag54-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lag54-region base)))))

(defun-sk lag54-l-index-of-type-p ()
  (forall (item array down up)
    (implies
     (and
      (lag54-address-p item)
      (lag54-address-p array)
      (integerp down)
      (integerp up))
     (integerp
      (lag54-l-index-of item array down up)))))

(defun lag54-linked-p ()
  (if (lag54-linked-op) t nil))

(defun lag54-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lag54-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lag54-address-base left)
     (lag54-address-base right)))
   (<=
    (+ (lag54-address-offset right) right-length)
    (lag54-address-offset left))
   (<=
    (+ (lag54-address-offset left) left-length)
    (lag54-address-offset right))))

(defun lag54-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lag54-address-base address))
    (<= 0 (lag54-address-offset address))
    (<=
     (+ (lag54-address-offset address) length)
     (lag54-malloc (lag54-address-base address))))))

;; These are exactly the three source axioms characterizing l_index_of for
;; the arbitrary pointer function t_3.

(defun-sk lag54-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lag54-address-p item)
      (lag54-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lag54-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lag54-t3 (lag54-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lag54-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lag54-t3 (lag54-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lag54-l-index-of item array (+ 1 down) up)
        (lag54-l-index-of item array down up)))))))

;; M is the two successive source functional updates of t_3.  The second
;; update has precedence even when the update addresses alias.

(defun lag54-m-read
    (a2 a a1 a5 address)
  (let ((second-update-address
         (lag54-shift (lag54-t3 a5) 0)))
    (cond
     ((equal address second-update-address) a1)
     ((equal address a2) a)
     (t (lag54-t3 address)))))

;; A7 is the source havoc: outside the possibly modified interval it reads M,
;; and inside that interval it reads the arbitrary prior memory t_2.

(defun lag54-a7-read
    (a2 a a1 a5 havoc-start havoc-length address)
  (if
      (lag54-separated-p address 1 havoc-start havoc-length)
      (lag54-m-read a2 a a1 a5 address)
    (lag54-t2 address)))

;; A8 is the exact functional update of A7 at shift(a4,0) with null.

(defun lag54-a8-read
    (a2 a a1 a5 havoc-start havoc-length a4 address)
  (if (equal address (lag54-shift a4 0))
      (lag54-null-address)
    (lag54-a7-read
     a2 a a1 a5 havoc-start havoc-length address)))

(defun lag54-mptr-read
    (memory-kind a2 a a1 a5 havoc-start havoc-length a4 address)
  (cond
   ((equal memory-kind :t3)
    (lag54-t3 address))
   ((equal memory-kind :a7)
    (lag54-a7-read
     a2 a a1 a5 havoc-start havoc-length address))
   ((equal memory-kind :a8)
    (lag54-a8-read
     a2 a a1 a5 havoc-start havoc-length a4 address))
   (t nil)))

;; A list of N successive roots is constructor evidence for the source
;; inductive p_linked_n relation.  The empty witness is exactly its bound
;; constructor; every cons cell is one cons constructor and advances both
;; the array index and next pointer.

(defun lag54-linked-steps-p
    (memory-kind a2 a a1 a5 havoc-start havoc-length a4
                 roots root array index bound)
  (if (consp roots)
      (and
       (lag54-address-p root)
       (equal (car roots) root)
       (equal
        (lag54-mptr-read
         memory-kind a2 a a1 a5 havoc-start havoc-length a4
         (lag54-shift array index))
        root)
       (lag54-valid-rw-p root 4)
       (lag54-linked-steps-p
        memory-kind a2 a a1 a5 havoc-start havoc-length a4
        (cdr roots)
        (lag54-mptr-read
         memory-kind a2 a a1 a5 havoc-start havoc-length a4
         (lag54-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lag54-p-linked-n-p
    (memory-kind a2 a a1 a5 havoc-start havoc-length a4
                 root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:t3 :a7 :a8))
     (lag54-address-p root)
     (lag54-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lag54-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lag54-linked-steps-p
      memory-kind a2 a a1 a5 havoc-start havoc-length a4
      roots root array index bound))))

(defun-sk lag54-framed-p ()
  (forall (address)
    (implies
     (lag54-address-p address)
     (<=
      (lag54-region
       (lag54-address-base (lag54-t3 address)))
      0))))

;; This unfolds load_s1_list and eqs1_list.  Pointer fields are read through
;; the selected pointer memories and the three scalar fields through t_1.

(defun lag54-eqs1-loads-p
    (left-kind right-kind
               a2 a a1 a5 havoc-start havoc-length a4
               left-root right-root)
  (and
   (equal
    (lag54-mptr-read
     right-kind a2 a a1 a5 havoc-start havoc-length a4
     (lag54-shift right-root 0))
    (lag54-mptr-read
     left-kind a2 a a1 a5 havoc-start havoc-length a4
     (lag54-shift left-root 0)))
   (equal
    (lag54-t1 (lag54-shift right-root 1))
    (lag54-t1 (lag54-shift left-root 1)))
   (equal
    (lag54-t1 (lag54-shift right-root 2))
    (lag54-t1 (lag54-shift left-root 2)))
   (equal
    (lag54-t1 (lag54-shift right-root 3))
    (lag54-t1 (lag54-shift left-root 3)))))

(defun-sk lag54-a4-in-t3-closed-range-p
    (a4 array lower upper)
  (exists (index)
    (and
     (integerp index)
     (equal
      a4
      (lag54-t3 (lag54-shift array index)))
     (<= lower index)
     (<= index upper))))

(defun-sk lag54-a4-not-in-t3-closed-range-p
    (a4 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (not
      (equal
       a4
       (lag54-t3 (lag54-shift array index)))))))

(defun-sk lag54-array-swipe-left-p
    (a2 a a1 a5 havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lag54-t3 (lag54-shift array (+ 1 index)))
      (lag54-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag54-shift array index))))))

;; In p_unchanged both real-valued memories are t_1.  Once the selected
;; addresses are equal, the three scalar-field equalities are reflexive.  The
;; next-pointer equality and valid_rw implication remain explicit.

(defun-sk lag54-unchanged-p
    (a2 a a1 a5 havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lag54-shift array index))
          (left-address
           (lag54-a7-read
            a2 a a1 a5 havoc-start havoc-length slot))
          (right-address (lag54-t3 slot)))
       (and
        (equal left-address right-address)
        (equal
         (lag54-t3 (lag54-shift right-address 0))
         (lag54-a7-read
          a2 a a1 a5 havoc-start havoc-length
          (lag54-shift left-address 0)))
        (implies
         (lag54-valid-rw-p right-address 4)
         (lag54-valid-rw-p left-address 4)))))))

(defun lag54-range-index-p (index lower upper closedp)
  (and
   (integerp index)
   (<= lower index)
   (if closedp
       (<= index upper)
     (< index upper))))

(defun-sk lag54-a7-not-a4-range-p
    (a2 a a1 a5 havoc-start havoc-length
        a4 array lower upper closedp)
  (forall (index)
    (implies
     (lag54-range-index-p index lower upper closedp)
     (not
      (equal
       (lag54-a7-read
        a2 a a1 a5 havoc-start havoc-length
        (lag54-shift array index))
       a4)))))

(defun-sk lag54-a2-separated-a7-range-p
    (a2 a a1 a5 havoc-start havoc-length
        array lower upper closedp)
  (forall (index)
    (implies
     (lag54-range-index-p index lower upper closedp)
     (lag54-separated-p
      a2 1
      (lag54-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag54-shift array index))
      4))))

(defun-sk lag54-a4-separated-a7-range-p
    (a2 a a1 a5 havoc-start havoc-length
        a4 array lower upper closedp)
  (forall (index)
    (implies
     (lag54-range-index-p index lower upper closedp)
     (lag54-separated-p
      a4 4
      (lag54-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag54-shift array index))
      4))))

(defun-sk lag54-a7-range-separated-array-p
    (a2 a a1 a5 havoc-start havoc-length
        array lower upper array-base closedp)
  (forall (index)
    (implies
     (lag54-range-index-p index lower upper closedp)
     (lag54-separated-p
      (lag54-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag54-shift array index))
      4 array-base 2147483646))))

(defun-sk lag54-a7-loads-equal-t3-successors-p
    (a2 a a1 a5 havoc-start havoc-length a4 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< index upper)
      (<= lower index))
     (lag54-eqs1-loads-p
      :a7 :t3
      a2 a a1 a5 havoc-start havoc-length a4
      (lag54-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag54-shift array index))
      (lag54-t3
       (lag54-shift array (+ 1 index)))))))

(defun-sk lag54-a7-range-distinct-p
    (a2 a a1 a5 havoc-start havoc-length
        array lower upper closedp)
  (forall (left-index right-index)
    (implies
     (and
      (lag54-range-index-p left-index lower upper closedp)
      (lag54-range-index-p right-index lower upper closedp)
      (not (equal left-index right-index)))
     (not
      (equal
       (lag54-a7-read
        a2 a a1 a5 havoc-start havoc-length
        (lag54-shift array left-index))
       (lag54-a7-read
        a2 a a1 a5 havoc-start havoc-length
        (lag54-shift array right-index)))))))

(defun-sk lag54-a7-range-separated-p
    (a2 a a1 a5 havoc-start havoc-length
        array lower upper closedp)
  (forall (left-index right-index)
    (implies
     (and
      (lag54-range-index-p left-index lower upper closedp)
      (lag54-range-index-p right-index lower upper closedp)
      (not (equal left-index right-index)))
     (lag54-separated-p
      (lag54-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag54-shift array left-index))
      4
      (lag54-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag54-shift array right-index))
      4))))

(defun-sk lag54-a2-separated-t3-closed-range-p
    (a2 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (lag54-separated-p
      a2 1
      (lag54-t3 (lag54-shift array index))
      4))))

(defun-sk lag54-t3-closed-range-separated-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (lag54-separated-p
      (lag54-t3 (lag54-shift array index))
      4 array-base 2147483646))))

(defun-sk lag54-a4-separated-t3-closed-range-p
    (a4 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        a4
        (lag54-t3 (lag54-shift array index))))
      (<= lower index)
      (<= index upper))
     (lag54-separated-p
      a4 4
      (lag54-t3 (lag54-shift array index))
      4))))

(defun-sk lag54-t3-closed-range-distinct-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (<= lower right-index)
      (<= lower left-index)
      (<= right-index upper)
      (<= left-index upper))
     (not
      (equal
       (lag54-t3 (lag54-shift array left-index))
       (lag54-t3 (lag54-shift array right-index)))))))

(defun-sk lag54-t3-closed-range-separated-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (<= lower right-index)
      (<= lower left-index)
      (<= right-index upper)
      (<= left-index upper))
     (lag54-separated-p
      (lag54-t3 (lag54-shift array left-index))
      4
      (lag54-t3 (lag54-shift array right-index))
      4))))

(defun
    ntp4vc-list-add-call-list-final-add-pre-separation-2-part4-goal54-statement
    (a3 i2 i i1 a2 a a1 i4 i3)
   (implies
    (and
     (lag54-pointer-functions-p)
     (lag54-malloc-function-p)
     (lag54-region-function-p)
     (lag54-l-index-of-type-p)
     (lag54-l-index-of-laws-p)
     (lag54-address-p a3)
     (integerp i2)
     (integerp i)
     (integerp i1)
     (lag54-address-p a2)
     (lag54-address-p a)
     (lag54-address-p a1)
     (integerp i4)
     (integerp i3))
    (let*
        ((a4 (lag54-t3 (lag54-shift a3 i2)))
         (x (+ 1 i i1))
         (x1 (lag54-l-index-of a4 a3 i1 x))
         (x2 (- x1 1))
         (a5 (lag54-shift a3 x2))
         (a6 (lag54-t3 a5))
         (havoc-start (lag54-shift a3 x1))
         (havoc-length (- x x1))
         (a9
          (lag54-a8-read
           a2 a a1 a5 havoc-start havoc-length a4 a2))
         (a10
          (lag54-a8-read
           a2 a a1 a5 havoc-start havoc-length a4
           (lag54-shift a3 (- (+ i i1) 1))))
         (x3 (+ i i1))
         (x4 (+ 1 i))
         (a11 (lag54-shift a3 0))
         (a12 (lag54-t3 a2))
         (a13
          (lag54-a7-read
           a2 a a1 a5 havoc-start havoc-length a2))
         (in-range
          (lag54-a4-in-t3-closed-range-p
           a4 a3 i1 x3))
         (not-in-range
          (lag54-a4-not-in-t3-closed-range-p
           a4 a3 i1 x3)))
      (implies
       (and
        (not (equal i4 i3))
        (not (equal a4 (lag54-null-address)))
        (not (equal x x1))
        (not (equal a9 (lag54-null-address)))
        (not (equal a10 (lag54-null-address)))
        (<= 0 i1)
        (<= i1 i2)
        (<= i1 i3)
        (<= i1 i4)
        (< i3 x3)
        (< i4 x3)
        (<= i2 x3)
        (<= (lag54-region (lag54-address-base a2)) 0)
        (<= (lag54-region (lag54-address-base a3)) 0)
        (<= (lag54-region (lag54-address-base a4)) 0)
        (<= i1 x1)
        (<= x1 x3)
        (<= -1 i)
        (<= i 2147483644)
        (<= i1 2147483645)
        (<= x3 2147483644)
        (<= x1 x)
        (lag54-framed-p)
        (lag54-linked-p)
        (lag54-is-sint32-p i)
        (lag54-is-sint32-p i1)
        (lag54-valid-rw-p a2 1)
        (lag54-is-sint32-p x4)
        (lag54-valid-rw-p a11 2147483646)
        (lag54-valid-rw-p (lag54-shift a3 i1) x4)
        (lag54-valid-rw-p a4 4)
        (lag54-separated-p a2 1 a11 2147483646)
        (lag54-separated-p a12 4 a11 2147483646)
        (lag54-separated-p a2 1 a4 4)
        (lag54-separated-p a4 4 a11 2147483646)
        (lag54-p-linked-n-p
         :t3 a2 a a1 a5 havoc-start havoc-length a4
         a12 a3 i1 x4 (lag54-null-address))
        (lag54-is-sint32-p x1)
        (lag54-separated-p a13 4 a11 2147483646)
        (lag54-eqs1-loads-p
         :a7 :t3
         a2 a a1 a5 havoc-start havoc-length a4
         a4 a4)
        (lag54-p-linked-n-p
         :a8 a2 a a1 a5 havoc-start havoc-length a4
         a9 a3 i1 i (lag54-null-address))
        (lag54-p-linked-n-p
         :a8 a2 a a1 a5 havoc-start havoc-length a4
         a9 a3 i1 (- i 1) a10)
        (implies
         (and (< i1 x1) in-range)
         (equal
          (lag54-a7-read
           a2 a a1 a5 havoc-start havoc-length a5)
          a6))
        (implies
         in-range
         (lag54-array-swipe-left-p
          a2 a a1 a5 havoc-start havoc-length
          a3 x1 x3))
        (implies
         in-range
         (lag54-a7-not-a4-range-p
          a2 a a1 a5 havoc-start havoc-length
          a4 a3 i1 x3 nil))
        (implies
         not-in-range
         (lag54-a7-not-a4-range-p
          a2 a a1 a5 havoc-start havoc-length
          a4 a3 i1 x3 t))
        (implies
         in-range
         (lag54-p-linked-n-p
          :a7 a2 a a1 a5 havoc-start havoc-length a4
          a13 a3 i1 i (lag54-null-address)))
        (implies
         not-in-range
         (lag54-p-linked-n-p
          :a7 a2 a a1 a5 havoc-start havoc-length a4
          a13 a3 i1 x4 (lag54-null-address)))
        (implies
         not-in-range
         (lag54-unchanged-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x))
        (implies
         in-range
         (lag54-unchanged-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x2))
        (implies
         in-range
         (lag54-a2-separated-a7-range-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 nil))
        (implies
         not-in-range
         (lag54-a2-separated-a7-range-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 t))
        (implies
         in-range
         (lag54-a4-separated-a7-range-p
          a2 a a1 a5 havoc-start havoc-length
          a4 a3 i1 x3 nil))
        (implies
         not-in-range
         (lag54-a4-separated-a7-range-p
          a2 a a1 a5 havoc-start havoc-length
          a4 a3 i1 x3 t))
        (implies
         in-range
         (lag54-a7-range-separated-array-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 a11 nil))
        (implies
         not-in-range
         (lag54-a7-range-separated-array-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 a11 t))
        (implies
         in-range
         (lag54-a7-loads-equal-t3-successors-p
          a2 a a1 a5 havoc-start havoc-length
          a4 a3 x1 x3))
        (implies
         in-range
         (lag54-a7-range-distinct-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 nil))
        (implies
         not-in-range
         (lag54-a7-range-distinct-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 t))
        (implies
         in-range
         (lag54-a7-range-separated-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 nil))
        (implies
         not-in-range
         (lag54-a7-range-separated-p
          a2 a a1 a5 havoc-start havoc-length
          a3 i1 x3 t))
        (lag54-a2-separated-t3-closed-range-p
         a2 a3 i1 x3)
        (lag54-t3-closed-range-separated-array-p
         a3 i1 x3 a11)
        (lag54-a4-separated-t3-closed-range-p
         a4 a3 i1 x3)
        (lag54-t3-closed-range-distinct-p
         a3 i1 x3)
        (lag54-t3-closed-range-separated-p
         a3 i1 x3))
       (lag54-separated-p
        (lag54-a8-read
         a2 a a1 a5 havoc-start havoc-length a4
         (lag54-shift a3 i4))
        4
        (lag54-a8-read
         a2 a a1 a5 havoc-start havoc-length a4
         (lag54-shift a3 i3))
        4)))))

(value-triple :itpeval-statement-checked)

:q
