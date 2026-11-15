;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_add_Why3_ide_VClist_add_call_list_final_add_pre_Linked_2_part1_goal43:
;; preservation of a linked-list segment after pointer-memory updates in the
;; final list-add verification condition. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lag43-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lag43-address-base (address)
  (car address))

(defun lag43-address-offset (address)
  (cdr address))

(defun lag43-shift (address amount)
  (cons
   (lag43-address-base address)
   (+ (lag43-address-offset address) amount)))

(defun lag43-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2 and t_3, integer memory-size function t, region and
;; linked operations, and l_index_of specialized to t_3.

(defstub lag43-t2 (address) t)
(defstub lag43-t3 (address) t)
(defstub lag43-malloc (index) t)
(defstub lag43-region (base) t)
(defstub lag43-linked-op () t)
(defstub lag43-l-index-of (item array down up) t)

(defun-sk lag43-function-types-p ()
  (forall (address index base item array down up)
    (implies
     (and
      (lag43-address-p address)
      (integerp index)
      (integerp base)
      (lag43-address-p item)
      (lag43-address-p array)
      (integerp down)
      (integerp up))
     (and
      (lag43-address-p (lag43-t2 address))
      (lag43-address-p (lag43-t3 address))
      (integerp (lag43-malloc index))
      (integerp (lag43-region base))
      (integerp
       (lag43-l-index-of item array down up))))))

(defun lag43-linked-p ()
  (if (lag43-linked-op) t nil))

(defun lag43-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lag43-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lag43-address-base left)
     (lag43-address-base right)))
   (<=
    (+ (lag43-address-offset right) right-length)
    (lag43-address-offset left))
   (<=
    (+ (lag43-address-offset left) left-length)
    (lag43-address-offset right))))

(defun lag43-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lag43-address-base address))
    (<= 0 (lag43-address-offset address))
    (<=
     (+ (lag43-address-offset address) length)
     (lag43-malloc (lag43-address-base address))))))

;; These are exactly the three source axioms characterizing l_index_of for
;; the arbitrary pointer function t_3.

(defun-sk lag43-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lag43-address-p item)
      (lag43-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lag43-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lag43-t3 (lag43-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lag43-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lag43-t3 (lag43-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lag43-l-index-of item array (+ 1 down) up)
        (lag43-l-index-of item array down up)))))))

;; M is the two source functional updates of t_3, in update order.

(defun lag43-m-read
    (a2 a a1 a5 address)
  (let ((second-update-address
         (lag43-shift (lag43-t3 a5) 0)))
    (cond
     ((equal address second-update-address) a1)
     ((equal address a2) a)
     (t (lag43-t3 address)))))

;; HAVOC is the source memory-theory operation: at every address separated
;; from the possibly modified interval it reads its second memory, and
;; otherwise it reads its first memory.

(defun lag43-a6-read
    (a2 a a1 a5 havoc-start address)
  (if
      (lag43-separated-p address 1 havoc-start 0)
      (lag43-m-read a2 a a1 a5 address)
    (lag43-t2 address)))

;; A7 is the exact functional update of A6 at shift(a3,0) with null.

(defun lag43-a7-read
    (a2 a a1 a5 havoc-start a3 address)
  (if (equal address (lag43-shift a3 0))
      (lag43-null-address)
    (lag43-a6-read a2 a a1 a5 havoc-start address)))

(defun lag43-mptr-read
    (memory-kind a2 a a1 a5 havoc-start a3 address)
  (cond
   ((equal memory-kind :t3)
    (lag43-t3 address))
   ((equal memory-kind :a6)
    (lag43-a6-read a2 a a1 a5 havoc-start address))
   ((equal memory-kind :a7)
    (lag43-a7-read
     a2 a a1 a5 havoc-start a3 address))
   (t nil)))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is its bound constructor, while n > 0 is its cons constructor
;; followed by the unique recursive predecessor at n - 1.

(defun lag43-p-linked-n-p
    (memory-kind a2 a a1 a5 havoc-start a3
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:t3 :a6 :a7))
   (lag43-address-p root)
   (lag43-address-p array)
   (integerp index)
   (integerp n)
   (lag43-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lag43-mptr-read
        memory-kind a2 a a1 a5 havoc-start a3
        (lag43-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lag43-valid-rw-p root 4)
      (lag43-p-linked-n-p
       memory-kind a2 a a1 a5 havoc-start a3
       (lag43-mptr-read
        memory-kind a2 a a1 a5 havoc-start a3
        (lag43-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lag43-framed-p ()
  (forall (address)
    (implies
     (lag43-address-p address)
     (<=
      (lag43-region
       (lag43-address-base (lag43-t3 address)))
      0))))

;; In p_unchanged, both real-valued memories are the same t_1. Unfolding
;; load_s1_list and eqs1_list makes the three real-field equalities reflexive;
;; the address equality, next-pointer equality, and valid_rw implication remain.

(defun-sk lag43-unchanged-p
    (a2 a a1 a5 havoc-start array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lag43-shift array index))
          (left-address
           (lag43-a6-read
            a2 a a1 a5 havoc-start slot))
          (right-address (lag43-t3 slot)))
       (and
        (equal left-address right-address)
        (equal
         (lag43-t3 (lag43-shift right-address 0))
         (lag43-a6-read
          a2 a a1 a5 havoc-start
          (lag43-shift left-address 0)))
        (implies
         (lag43-valid-rw-p right-address 4)
         (lag43-valid-rw-p left-address 4)))))))

(defun-sk lag43-t3-not-a3-range-p
    (a3 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (not
      (equal
       (lag43-t3 (lag43-shift array index))
       a3)))))

(defun-sk lag43-a2-separated-t3-range-p
    (a2 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lag43-separated-p
      a2 1
      (lag43-t3 (lag43-shift array index))
      4))))

(defun-sk lag43-t3-range-separated-array-p
    (array-base array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lag43-separated-p
      (lag43-t3 (lag43-shift array index))
      4 array-base 2147483646))))

(defun-sk lag43-a3-separated-t3-range-p
    (a3 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        (lag43-t3 (lag43-shift array index))
        a3))
      (<= lower index)
      (< index upper))
     (lag43-separated-p
      a3 4
      (lag43-t3 (lag43-shift array index))
      4))))

(defun-sk lag43-t3-range-distinct-p
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
       (lag43-t3 (lag43-shift array left-index))
       (lag43-t3 (lag43-shift array right-index)))))))

(defun-sk lag43-m-not-a3-range-p
    (a2 a a1 a5 a3 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (not
      (equal
       (lag43-m-read
        a2 a a1 a5 (lag43-shift array index))
       a3)))))

(defun-sk lag43-t3-range-separated-p
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
     (lag43-separated-p
      (lag43-t3 (lag43-shift array left-index))
      4
      (lag43-t3 (lag43-shift array right-index))
      4))))

(defun-sk lag43-a2-separated-m-range-p
    (a2 a a1 a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lag43-separated-p
      a2 1
      (lag43-m-read
       a2 a a1 a5 (lag43-shift array index))
      4))))

(defun-sk lag43-a3-separated-m-range-p
    (a2 a a1 a5 a3 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lag43-separated-p
      a3 4
      (lag43-m-read
       a2 a a1 a5 (lag43-shift array index))
      4))))

(defun-sk lag43-m-range-separated-array-p
    (a2 a a1 a5 array-base array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lag43-separated-p
      (lag43-m-read
       a2 a a1 a5 (lag43-shift array index))
      4 array-base 2147483646))))

(defun-sk lag43-m-range-distinct-p
    (a2 a a1 a5 array lower upper)
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
       (lag43-m-read
        a2 a a1 a5 (lag43-shift array left-index))
       (lag43-m-read
        a2 a a1 a5 (lag43-shift array right-index)))))))

(defun-sk lag43-m-range-separated-p
    (a2 a a1 a5 array lower upper)
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
     (lag43-separated-p
      (lag43-m-read
       a2 a a1 a5 (lag43-shift array left-index))
      4
      (lag43-m-read
       a2 a a1 a5 (lag43-shift array right-index))
      4))))

(defun-sk
    ntp4vc-list-add-call-list-final-add-pre-linked-2-part1-goal43-statement ()
  (forall
   (i i1 a4 a2 a a1 a3)
   (implies
    (and
     (lag43-function-types-p)
     (lag43-l-index-of-laws-p)
     (integerp i)
     (integerp i1)
     (lag43-address-p a4)
     (lag43-address-p a2)
     (lag43-address-p a)
     (lag43-address-p a1)
     (lag43-address-p a3))
    (let*
        ((x (+ i i1))
         (x1 (- x 1))
         (a5 (lag43-shift a4 x1))
         (havoc-start (lag43-shift a4 x))
         (a8
          (lag43-a7-read
           a2 a a1 a5 havoc-start a3 a2))
         (a9
          (lag43-a7-read
           a2 a a1 a5 havoc-start a3 a5))
         (a10 (lag43-shift a4 0))
         (a11 (lag43-t3 a2))
         (a12 (lag43-m-read a2 a a1 a5 a2)))
      (implies
       (and
        (not (equal (lag43-null-address) a3))
        (equal
         x
         (lag43-l-index-of a3 a4 i1 x))
        (not (equal a8 (lag43-null-address)))
        (not (equal a9 (lag43-null-address)))
        (<= 0 i)
        (<= 0 i1)
        (<= (lag43-region (lag43-address-base a2)) 0)
        (<= (lag43-region (lag43-address-base a3)) 0)
        (<= (lag43-region (lag43-address-base a4)) 0)
        (<= i 2147483645)
        (<= i1 2147483645)
        (<= x 2147483645)
        (lag43-framed-p)
        (lag43-linked-p)
        (lag43-is-sint32-p i)
        (lag43-is-sint32-p i1)
        (lag43-valid-rw-p a2 1)
        (lag43-valid-rw-p a3 4)
        (lag43-separated-p a2 1 a3 4)
        (lag43-is-sint32-p x)
        (lag43-valid-rw-p a10 2147483646)
        (lag43-valid-rw-p (lag43-shift a4 i1) i)
        (lag43-separated-p a2 1 a10 2147483646)
        (lag43-separated-p a3 4 a10 2147483646)
        (lag43-separated-p a11 4 a10 2147483646)
        (lag43-p-linked-n-p
         :t3 a2 a a1 a5 havoc-start a3
         a11 a4 i1 i (lag43-null-address))
        (lag43-separated-p a12 4 a10 2147483646)
        (equal
         (lag43-a6-read
          a2 a a1 a5 havoc-start (lag43-shift a3 0))
         (lag43-t3 (lag43-shift a3 0)))
        (lag43-p-linked-n-p
         :a6 a2 a a1 a5 havoc-start a3
         a12 a4 i1 i (lag43-null-address))
        (lag43-p-linked-n-p
         :a7 a2 a a1 a5 havoc-start a3
         a8 a4 i1 i (lag43-null-address))
        (lag43-p-linked-n-p
         :a7 a2 a a1 a5 havoc-start a3
         a8 a4 i1 (- i 1) a9)
        (lag43-unchanged-p
         a2 a a1 a5 havoc-start a4 i1 x)
        (lag43-t3-not-a3-range-p a3 a4 i1 x)
        (lag43-a2-separated-t3-range-p a2 a4 i1 x)
        (lag43-t3-range-separated-array-p
         a10 a4 i1 x)
        (lag43-a3-separated-t3-range-p a3 a4 i1 x)
        (lag43-t3-range-distinct-p a4 i1 x)
        (lag43-m-not-a3-range-p
         a2 a a1 a5 a3 a4 i1 x)
        (lag43-t3-range-separated-p a4 i1 x)
        (lag43-a2-separated-m-range-p
         a2 a a1 a5 a4 i1 x)
        (lag43-a3-separated-m-range-p
         a2 a a1 a5 a3 a4 i1 x)
        (lag43-m-range-separated-array-p
         a2 a a1 a5 a10 a4 i1 x)
        (lag43-m-range-distinct-p
         a2 a a1 a5 a4 i1 x)
        (lag43-m-range-separated-p
         a2 a a1 a5 a4 i1 x))
       (lag43-p-linked-n-p
        :a7 a2 a a1 a5 havoc-start a3
        a9 a4 x1 1
        (lag43-a7-read
         a2 a a1 a5 havoc-start a3
         (lag43-shift a9 0))))))))

(value-triple :itpeval-statement-checked)

:q
