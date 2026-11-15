;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_Swiped_part5_goal64:
;; preservation of the pointer-array left-swipe relation after removing a
;; located linked-list item by a single pointer-memory update, under the stated
;; integer bounds, validity, framing, linked-segment, unchanged-memory,
;; separation, and uniqueness hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lr64-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lr64-address-base (address)
  (car address))

(defun lr64-address-offset (address)
  (cdr address))

(defun lr64-shift (address amount)
  (cons
   (lr64-address-base address)
   (+ (lr64-address-offset address) amount)))

(defun lr64-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2, t_3, and t_4, allocation function t,
;; real-valued memory t_1,
;; fixed region operation, linked proposition specialized to t, and imported
;; l_index_of operation specialized to t_2.
;;
;; Values of t_1 are observed only by reflexive equalities in the specialized
;; p_unchanged premise. An arbitrary ACL2 codomain therefore preserves exactly
;; every observation of the source real-valued function in this statement.

(defstub lr64-t2 (address) t)
(defstub lr64-t3 (address) t)
(defstub lr64-t4 (address) t)
(defstub lr64-t (index) t)
(defstub lr64-t1 (address) t)
(defstub lr64-region (base) t)
(defstub lr64-linked-op () t)
(defstub lr64-l-index-of (item array down up) t)

(defun-sk lr64-function-types-p ()
  (forall (address index base item array down up)
    (implies
     (and
      (lr64-address-p address)
      (integerp index)
      (integerp base)
      (lr64-address-p item)
      (lr64-address-p array)
      (integerp down)
      (integerp up))
     (and
      (lr64-address-p (lr64-t2 address))
      (lr64-address-p (lr64-t3 address))
      (lr64-address-p (lr64-t4 address))
      (integerp (lr64-t index))
      (integerp (lr64-region base))
      (integerp
       (lr64-l-index-of item array down up))))))

(defun lr64-linked-p ()
  (if (lr64-linked-op) t nil))

(defun lr64-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lr64-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lr64-address-base address))
    (<= 0 (lr64-address-offset address))
    (<=
     (+ (lr64-address-offset address) length)
     (lr64-t (lr64-address-base address))))))

(defun lr64-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lr64-address-base left)
     (lr64-address-base right)))
   (<=
    (+ (lr64-address-offset right) right-length)
    (lr64-address-offset left))
   (<=
    (+ (lr64-address-offset left) left-length)
    (lr64-address-offset right))))

(defun-sk lr64-framed-p ()
  (forall (address)
    (implies
     (lr64-address-p address)
     (<=
      (lr64-region
       (lr64-address-base (lr64-t2 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lr64-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lr64-address-p item)
      (lr64-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lr64-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lr64-t2 (lr64-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lr64-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lr64-t2 (lr64-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lr64-l-index-of item array (+ 1 down) up)
        (lr64-l-index-of item array down up)))))))

;; This recursion is logically equivalent to the source inductive p_linked_n
;; relation: n = 0 is its bound constructor, and n > 0 is its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lr64-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lr64-address-p root)
   (lr64-address-p array)
   (integerp index)
   (integerp n)
   (lr64-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lr64-t2 (lr64-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lr64-valid-rw-p root 4)
      (lr64-p-linked-n-p
       (lr64-t2 (lr64-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

;; This unfolds the source p_unchanged premise at identical old and new
;; allocation, pointer, and scalar memories.

(defun-sk lr64-reflexive-unchanged-p (array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lr64-shift array index))
          (left-address (lr64-t2 slot))
          (right-address (lr64-t2 slot)))
       (and
        (equal left-address right-address)
        (equal
         (lr64-t2 (lr64-shift right-address 0))
         (lr64-t2 (lr64-shift left-address 0)))
        (equal
         (lr64-t1 (lr64-shift right-address 1))
         (lr64-t1 (lr64-shift left-address 1)))
        (equal
         (lr64-t1 (lr64-shift right-address 2))
         (lr64-t1 (lr64-shift left-address 2)))
        (equal
         (lr64-t1 (lr64-shift right-address 3))
         (lr64-t1 (lr64-shift left-address 3)))
        (implies
         (lr64-valid-rw-p right-address 4)
         (lr64-valid-rw-p left-address 4)))))))

(defun-sk lr64-a5-absent-through-i3-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (not
      (equal
       (lr64-t2 (lr64-shift array index))
       a5)))))

(defun-sk lr64-a1-separated-from-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr64-separated-p
      a1 1
      (lr64-t2 (lr64-shift array index)) 4))))

(defun-sk lr64-a5-separated-from-prefix-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr64-separated-p
      a5 4
      (lr64-t2 (lr64-shift array index)) 4))))

(defun-sk lr64-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr64-separated-p
      (lr64-t2 (lr64-shift array index)) 4
      array-base 2147483646))))

(defun-sk lr64-a6-separated-from-other-range-p
    (a6 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        a6
        (lr64-t2 (lr64-shift array index))))
      (<= lower index)
      (< index upper))
     (lr64-separated-p
      a6 4
      (lr64-t2 (lr64-shift array index)) 4))))

(defun-sk lr64-range-addresses-distinct-p
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
       (lr64-t2 (lr64-shift array left-index))
       (lr64-t2 (lr64-shift array right-index)))))))

(defun-sk lr64-range-addresses-separated-p
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
     (lr64-separated-p
      (lr64-t2 (lr64-shift array left-index)) 4
      (lr64-t2 (lr64-shift array right-index)) 4))))

;; This is the exact source equality
;; havoc t_4 t_2 (shift a_2 (1 + i_3)) (i + i_1 - 2 - i_3) = t_3.

(defun-sk lr64-havoc-state-p
    (array upper i3)
  (forall (address)
    (implies
     (lr64-address-p address)
     (equal
      (lr64-t3 address)
      (if
       (lr64-separated-p
        address 1
        (lr64-shift array (+ 1 i3))
        (- (- upper 2) i3))
       (lr64-t2 address)
       (lr64-t4 address))))))

;; This is the prerequisite source p_array_swipe_left relation between the
;; post-havoc map t_3 and the original map t_2.

(defun-sk lr64-array-swipe-left-before-update-p
    (array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lr64-t2 (lr64-shift array (+ 1 index)))
      (lr64-t3 (lr64-shift array index))))))

;; UPDATED-READ is the exact source functional update of t_3 at
;; update-address.

(defun lr64-updated-read
    (update-address update-value address)
  (if (equal address update-address)
      update-value
    (lr64-t3 address)))

;; This is exactly p_array_swipe_left with the updated pointer memory as its
;; first function argument and the original pointer memory as its second.

(defun-sk lr64-array-swipe-left-after-update-p
    (array down up update-address update-value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lr64-t2 (lr64-shift array (+ 1 index)))
      (lr64-updated-read
       update-address update-value
       (lr64-shift array index))))))

(defun-sk
    ntp4vc-list-remove-contains-item-swiped-part5-goal64-statement ()
  (forall
   (a1 a a2 i2 i i1 i3)
   (implies
    (and
     (lr64-function-types-p)
     (lr64-l-index-of-laws-p)
     (lr64-address-p a1)
     (lr64-address-p a)
     (lr64-address-p a2)
     (integerp i2)
     (integerp i)
     (integerp i1)
     (integerp i3))
    (let*
        ((a3 (lr64-t2 a1))
         (a4 (lr64-shift a 0))
         (a5 (lr64-t2 a4))
         (a6 (lr64-t2 (lr64-shift a2 i2)))
         (x (+ i i1))
         (a7 (lr64-shift a2 0))
         (x1 (lr64-l-index-of a6 a2 i1 x)))
      (implies
       (and
        (not (equal a3 (lr64-null-address)))
        (not (equal a5 a3))
        (not (equal a6 (lr64-null-address)))
        (equal a6 a5)
        (<= 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= i1 i3)
        (< i2 x)
        (<= i3 x)
        (<= (lr64-region (lr64-address-base a1)) 0)
        (<= (lr64-region (lr64-address-base a2)) 0)
        (<= (lr64-region (lr64-address-base a5)) 0)
        (<= i 2147483645)
        (lr64-framed-p)
        (lr64-linked-p)
        (lr64-is-sint32-p i)
        (lr64-is-sint32-p i1)
        (lr64-is-sint32-p i3)
        (lr64-valid-rw-p a1 1)
        (lr64-valid-rw-p a7 2147483646)
        (lr64-separated-p a1 1 a7 2147483646)
        (lr64-separated-p a3 4 a7 2147483646)
        (lr64-p-linked-n-p
         a3 a2 i1 i (lr64-null-address))
        (lr64-reflexive-unchanged-p a2 i1 i3)
        (lr64-p-linked-n-p
         a a2 i3 1 a5)
        (lr64-is-sint32-p x1)
        (lr64-p-linked-n-p
         a3 a2 i1 (- i3 i1) a)
        (lr64-p-linked-n-p
         a5 a2 (+ 1 i3)
         (- (- (+ i i1) 1) i3)
         (lr64-null-address))
        (lr64-a5-absent-through-i3-p
         a5 a2 i1 i3)
        (lr64-a1-separated-from-range-p
         a1 a2 i1 x)
        (lr64-a5-separated-from-prefix-p
         a5 a2 i1 i3)
        (lr64-range-separated-from-array-p
         a2 i1 x a7)
        (lr64-a6-separated-from-other-range-p
         a6 a2 i1 x)
        (lr64-range-addresses-distinct-p
         a2 i1 x)
        (lr64-range-addresses-separated-p
         a2 i1 x)
        (lr64-havoc-state-p a2 (+ i i1) i3)
        (lr64-array-swipe-left-before-update-p
         a2 (+ 1 i3) (- (+ i i1) 1)))
       (lr64-array-swipe-left-after-update-p
        a2 x1 (- (+ i i1) 1)
        a4
        (lr64-t2 (lr64-shift a5 0))))))))

(value-triple :itpeval-statement-checked)

:q
