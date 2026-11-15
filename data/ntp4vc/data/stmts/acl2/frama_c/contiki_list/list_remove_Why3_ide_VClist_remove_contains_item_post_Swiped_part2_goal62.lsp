;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_Swiped_part2_goal62:
;; preservation of the pointer-array left-swipe relation after removing a
;; located list item by a single pointer-memory update, under the stated
;; integer bounds, validity, framing, linked-segment, separation, and
;; uniqueness hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lr62-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lr62-address-base (address)
  (car address))

(defun lr62-address-offset (address)
  (cdr address))

(defun lr62-shift (address amount)
  (cons
   (lr62-address-base address)
   (+ (lr62-address-offset address) amount)))

(defun lr62-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_1, t_2, and t_3, allocation function t, fixed region
;; operation, linked proposition specialized to t, and imported l_index_of
;; operation specialized to t_1.

(defstub lr62-t1 (address) t)
(defstub lr62-t2 (address) t)
(defstub lr62-t3 (address) t)
(defstub lr62-t (index) t)
(defstub lr62-region (base) t)
(defstub lr62-linked-op () t)
(defstub lr62-l-index-of (item array down up) t)

(defun-sk lr62-pointer-function-p ()
  (forall (address)
    (implies
     (lr62-address-p address)
     (and
      (lr62-address-p (lr62-t1 address))
      (lr62-address-p (lr62-t2 address))
      (lr62-address-p (lr62-t3 address))))))

(defun-sk lr62-integer-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lr62-t index)))))

(defun-sk lr62-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lr62-region base)))))

(defun-sk lr62-l-index-of-type-p ()
  (forall (item array down up)
    (implies
     (and
      (lr62-address-p item)
      (lr62-address-p array)
      (integerp down)
      (integerp up))
     (integerp
      (lr62-l-index-of item array down up)))))

(defun lr62-linked-p ()
  (if (lr62-linked-op) t nil))

(defun lr62-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lr62-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lr62-address-base address))
    (<= 0 (lr62-address-offset address))
    (<=
     (+ (lr62-address-offset address) length)
     (lr62-t (lr62-address-base address))))))

(defun lr62-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lr62-address-base left)
     (lr62-address-base right)))
   (<=
    (+ (lr62-address-offset right) right-length)
    (lr62-address-offset left))
   (<=
    (+ (lr62-address-offset left) left-length)
    (lr62-address-offset right))))

(defun-sk lr62-framed-p ()
  (forall (address)
    (implies
     (lr62-address-p address)
     (<=
      (lr62-region
       (lr62-address-base (lr62-t1 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lr62-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lr62-address-p item)
      (lr62-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lr62-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lr62-t1 (lr62-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lr62-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lr62-t1 (lr62-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lr62-l-index-of item array (+ 1 down) up)
        (lr62-l-index-of item array down up)))))))

;; This recursion is logically equivalent to the source inductive
;; p_linked_n relation: n = 0 is exactly the bound constructor, while n > 0
;; is exactly the cons constructor followed by its predecessor at n - 1.

(defun lr62-p-linked-n-p
    (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lr62-address-p root)
   (lr62-address-p array)
   (integerp index)
   (integerp n)
   (lr62-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lr62-t1 (lr62-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lr62-valid-rw-p root 4)
      (lr62-p-linked-n-p
       (lr62-t1 (lr62-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lr62-a-separated-from-range-p
    (a array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr62-separated-p
      a 1
      (lr62-t1 (lr62-shift array index)) 4))))

(defun-sk lr62-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr62-separated-p
      (lr62-t1 (lr62-shift array index)) 4
      array-base 2147483646))))

(defun-sk lr62-item-separated-from-other-range-p
    (item array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        item
        (lr62-t1 (lr62-shift array index))))
      (<= lower index)
      (< index upper))
     (lr62-separated-p
      item 4
      (lr62-t1 (lr62-shift array index)) 4))))

(defun-sk lr62-range-addresses-distinct-p
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
       (lr62-t1 (lr62-shift array left-index))
       (lr62-t1 (lr62-shift array right-index)))))))

(defun-sk lr62-range-addresses-separated-p
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
     (lr62-separated-p
      (lr62-t1 (lr62-shift array left-index)) 4
      (lr62-t1 (lr62-shift array right-index)) 4))))

;; This is the exact source equality
;; havoc t_3 t_1 (shift array lower) (length - 1) = t_2.

(defun-sk lr62-havoc-state-p
    (array lower length)
  (forall (address)
    (implies
     (lr62-address-p address)
     (equal
      (lr62-t2 address)
      (if
       (lr62-separated-p
        address 1
        (lr62-shift array lower)
        (- length 1))
       (lr62-t1 address)
       (lr62-t3 address))))))

;; This is the prerequisite source p_array_swipe_left relation between the
;; post-havoc map t_2 and the original map t_1.

(defun-sk lr62-array-swipe-left-before-update-p
    (array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lr62-t1 (lr62-shift array (+ 1 index)))
      (lr62-t2 (lr62-shift array index))))))

;; UPDATED-READ is the exact source functional update of t_2 at
;; update-address.

(defun lr62-updated-read
    (update-address update-value address)
  (if (equal address update-address)
      update-value
    (lr62-t2 address)))

;; This is exactly p_array_swipe_left with the updated pointer memory as its
;; first function argument and the original pointer memory as its second.

(defun-sk lr62-array-swipe-left-after-update-p
    (array down up update-address update-value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lr62-t1 (lr62-shift array (+ 1 index)))
      (lr62-updated-read
       update-address update-value
       (lr62-shift array index))))))

(defun-sk
    ntp4vc-list-remove-contains-item-swiped-part2-goal62-statement ()
  (forall
   (a a1 i2 i i1)
   (implies
    (and
     (lr62-pointer-function-p)
     (lr62-integer-function-p)
     (lr62-region-function-p)
     (lr62-l-index-of-type-p)
     (lr62-l-index-of-laws-p)
     (lr62-address-p a)
     (lr62-address-p a1)
     (integerp i2)
     (integerp i)
     (integerp i1))
    (let*
        ((a2 (lr62-t1 a))
         (a3 (lr62-t1 (lr62-shift a1 i2)))
         (x (+ i i1))
         (a4 (lr62-shift a1 0))
         (x1 (lr62-l-index-of a3 a1 i1 x)))
      (implies
       (and
        (not (equal a2 (lr62-null-address)))
        (not (equal a3 (lr62-null-address)))
        (equal a3 a2)
        (<= 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (< i2 x)
        (<= (lr62-region (lr62-address-base a)) 0)
        (<= (lr62-region (lr62-address-base a1)) 0)
        (<= (lr62-region (lr62-address-base a2)) 0)
        (<= i 2147483645)
        (lr62-framed-p)
        (lr62-linked-p)
        (lr62-is-sint32-p i)
        (lr62-is-sint32-p i1)
        (lr62-valid-rw-p a 1)
        (lr62-valid-rw-p a4 2147483646)
        (lr62-separated-p a 1 a4 2147483646)
        (lr62-separated-p a2 4 a4 2147483646)
        (lr62-p-linked-n-p
         a2 a1 i1 i (lr62-null-address))
        (lr62-is-sint32-p x1)
        (lr62-a-separated-from-range-p
         a a1 i1 x)
        (lr62-range-separated-from-array-p
         a1 i1 x a4)
        (lr62-item-separated-from-other-range-p
         a3 a1 i1 x)
        (lr62-range-addresses-distinct-p
         a1 i1 x)
        (lr62-range-addresses-separated-p
         a1 i1 x)
        (lr62-havoc-state-p a1 i1 i)
        (lr62-array-swipe-left-before-update-p
         a1 i1 (- (+ i i1) 1)))
       (lr62-array-swipe-left-after-update-p
        a1 x1 (- (+ i i1) 1)
        a
        (lr62-t1 (lr62-shift a2 0))))))))

(value-triple :itpeval-statement-checked)

:q
