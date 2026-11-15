;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_PrevItem_part5_goal66:
;; preservation of the pointer-array entry preceding the located removed item
;; under integer bounds, memory validity, framing, linked-segment,
;; unchanged-memory, separation, and uniqueness hypotheses. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lr66-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lr66-address-base (address)
  (car address))

(defun lr66-address-offset (address)
  (cdr address))

(defun lr66-shift (address amount)
  (cons
   (lr66-address-base address)
   (+ (lr66-address-offset address) amount)))

(defun lr66-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_2, allocation function t, real-valued memory t_1,
;; fixed region operation, linked proposition specialized to t, and imported
;; l_index_of operation specialized to t_2.
;;
;; Values of t_1 are observed only by reflexive equalities in the specialized
;; p_unchanged premise. An arbitrary ACL2 codomain therefore preserves exactly
;; every observation of the source real-valued function in this statement.

(defstub lr66-t2 (address) t)
(defstub lr66-t (index) t)
(defstub lr66-t1 (address) t)
(defstub lr66-region (base) t)
(defstub lr66-linked-op () t)
(defstub lr66-l-index-of (item array down up) t)

(defun-sk lr66-function-types-p ()
  (forall (address index base item array down up)
    (implies
     (and
      (lr66-address-p address)
      (integerp index)
      (integerp base)
      (lr66-address-p item)
      (lr66-address-p array)
      (integerp down)
      (integerp up))
     (and
      (lr66-address-p (lr66-t2 address))
      (integerp (lr66-t index))
      (integerp (lr66-region base))
      (integerp
       (lr66-l-index-of item array down up))))))

(defun lr66-linked-p ()
  (if (lr66-linked-op) t nil))

(defun lr66-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lr66-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lr66-address-base address))
    (<= 0 (lr66-address-offset address))
    (<=
     (+ (lr66-address-offset address) length)
     (lr66-t (lr66-address-base address))))))

(defun lr66-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lr66-address-base left)
     (lr66-address-base right)))
   (<=
    (+ (lr66-address-offset right) right-length)
    (lr66-address-offset left))
   (<=
    (+ (lr66-address-offset left) left-length)
    (lr66-address-offset right))))

(defun-sk lr66-framed-p ()
  (forall (address)
    (implies
     (lr66-address-p address)
     (<=
      (lr66-region
       (lr66-address-base (lr66-t2 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lr66-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lr66-address-p item)
      (lr66-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lr66-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lr66-t2 (lr66-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lr66-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lr66-t2 (lr66-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lr66-l-index-of item array (+ 1 down) up)
        (lr66-l-index-of item array down up)))))))

;; This recursion is logically equivalent to the source inductive p_linked_n
;; relation: n = 0 is its bound constructor, and n > 0 is its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lr66-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lr66-address-p root)
   (lr66-address-p array)
   (integerp index)
   (integerp n)
   (lr66-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lr66-t2 (lr66-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lr66-valid-rw-p root 4)
      (lr66-p-linked-n-p
       (lr66-t2 (lr66-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

;; This unfolds the source p_unchanged premise at identical old and new
;; allocation, pointer, and scalar memories.

(defun-sk lr66-reflexive-unchanged-p (array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lr66-shift array index))
          (left-address (lr66-t2 slot))
          (right-address (lr66-t2 slot)))
       (and
        (equal left-address right-address)
        (equal
         (lr66-t2 (lr66-shift right-address 0))
         (lr66-t2 (lr66-shift left-address 0)))
        (equal
         (lr66-t1 (lr66-shift right-address 1))
         (lr66-t1 (lr66-shift left-address 1)))
        (equal
         (lr66-t1 (lr66-shift right-address 2))
         (lr66-t1 (lr66-shift left-address 2)))
        (equal
         (lr66-t1 (lr66-shift right-address 3))
         (lr66-t1 (lr66-shift left-address 3)))
        (implies
         (lr66-valid-rw-p right-address 4)
         (lr66-valid-rw-p left-address 4)))))))

(defun-sk lr66-a5-absent-through-i3-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (not
      (equal
       (lr66-t2 (lr66-shift array index))
       a5)))))

(defun-sk lr66-a1-separated-from-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr66-separated-p
      a1 1
      (lr66-t2 (lr66-shift array index)) 4))))

(defun-sk lr66-a5-separated-from-prefix-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr66-separated-p
      a5 4
      (lr66-t2 (lr66-shift array index)) 4))))

(defun-sk lr66-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr66-separated-p
      (lr66-t2 (lr66-shift array index)) 4
      array-base 2147483646))))

(defun-sk lr66-a6-separated-from-other-range-p
    (a6 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        a6
        (lr66-t2 (lr66-shift array index))))
      (<= lower index)
      (< index upper))
     (lr66-separated-p
      a6 4
      (lr66-t2 (lr66-shift array index)) 4))))

(defun-sk lr66-range-addresses-distinct-p
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
       (lr66-t2 (lr66-shift array left-index))
       (lr66-t2 (lr66-shift array right-index)))))))

(defun-sk lr66-range-addresses-separated-p
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
     (lr66-separated-p
      (lr66-t2 (lr66-shift array left-index)) 4
      (lr66-t2 (lr66-shift array right-index)) 4))))

;; UPDATED-READ is the exact functional update of t_2 at update-address.

(defun lr66-updated-read
    (update-address update-value address)
  (if (equal address update-address)
      update-value
    (lr66-t2 address)))

(defun-sk
    ntp4vc-list-remove-contains-item-previtem-part5-goal66-statement ()
  (forall
   (a1 a a2 i2 i i1 i3)
   (implies
    (and
     (lr66-function-types-p)
     (lr66-l-index-of-laws-p)
     (lr66-address-p a1)
     (lr66-address-p a)
     (lr66-address-p a2)
     (integerp i2)
     (integerp i)
     (integerp i1)
     (integerp i3))
    (let*
        ((a3 (lr66-t2 a1))
         (a4 (lr66-shift a 0))
         (a5 (lr66-t2 a4))
         (a6 (lr66-t2 (lr66-shift a2 i2)))
         (x (+ i i1))
         (x1 (lr66-l-index-of a6 a2 i1 x))
         (a7 (lr66-shift a2 0))
         (a8 (lr66-shift a2 (- x1 1))))
      (implies
       (and
        (not (equal a3 (lr66-null-address)))
        (not (equal a5 a3))
        (not (equal a6 (lr66-null-address)))
        (equal a6 a5)
        (<= 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= i1 i3)
        (< i2 x)
        (<= i3 x)
        (<= (lr66-region (lr66-address-base a1)) 0)
        (<= (lr66-region (lr66-address-base a2)) 0)
        (<= (lr66-region (lr66-address-base a5)) 0)
        (< i1 x1)
        (<= i 2147483645)
        (lr66-framed-p)
        (lr66-linked-p)
        (lr66-is-sint32-p i)
        (lr66-is-sint32-p i1)
        (lr66-is-sint32-p i3)
        (lr66-valid-rw-p a1 1)
        (lr66-valid-rw-p a7 2147483646)
        (lr66-separated-p a1 1 a7 2147483646)
        (lr66-separated-p a3 4 a7 2147483646)
        (lr66-p-linked-n-p
         a3 a2 i1 i (lr66-null-address))
        (lr66-reflexive-unchanged-p a2 i1 i3)
        (lr66-p-linked-n-p
         a a2 i3 1 a5)
        (lr66-is-sint32-p x1)
        (lr66-p-linked-n-p
         a3 a2 i1 (- i3 i1) a)
        (lr66-p-linked-n-p
         a5 a2 (+ 1 i3)
         (- (- (+ i i1) 1) i3)
         (lr66-null-address))
        (lr66-a5-absent-through-i3-p
         a5 a2 i1 i3)
        (lr66-a1-separated-from-range-p
         a1 a2 i1 x)
        (lr66-a5-separated-from-prefix-p
         a5 a2 i1 i3)
        (lr66-range-separated-from-array-p
         a2 i1 x a7)
        (lr66-a6-separated-from-other-range-p
         a6 a2 i1 x)
        (lr66-range-addresses-distinct-p
         a2 i1 x)
        (lr66-range-addresses-separated-p
         a2 i1 x))
       (equal
        (lr66-updated-read
         a4
         (lr66-t2 (lr66-shift a5 0))
         a8)
        (lr66-t2 a8)))))))

(value-triple :itpeval-statement-checked)

:q
