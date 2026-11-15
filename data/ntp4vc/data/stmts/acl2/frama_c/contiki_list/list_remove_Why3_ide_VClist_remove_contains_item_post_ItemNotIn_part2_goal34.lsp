;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_ItemNotIn_part2_goal34:
;; exclusion of the removed linked-list item from an updated pointer-array
;; position, under integer bounds, memory validity, framing, linked-segment,
;; separation, and uniqueness hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lr34-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lr34-address-base (address)
  (car address))

(defun lr34-address-offset (address)
  (cdr address))

(defun lr34-shift (address amount)
  (cons
   (lr34-address-base address)
   (+ (lr34-address-offset address) amount)))

(defun lr34-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_1 and t_2, allocation function t, fixed region operation,
;; linked proposition specialized to t, and imported l_index_of operation
;; specialized to t_1.

(defstub lr34-t1 (address) t)
(defstub lr34-t2 (address) t)
(defstub lr34-t (index) t)
(defstub lr34-region (base) t)
(defstub lr34-linked-op () t)
(defstub lr34-l-index-of (item array down up) t)

(defun-sk lr34-pointer-function-p ()
  (forall (address)
    (implies
     (lr34-address-p address)
     (and
      (lr34-address-p (lr34-t1 address))
      (lr34-address-p (lr34-t2 address))))))

(defun-sk lr34-integer-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lr34-t index)))))

(defun-sk lr34-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lr34-region base)))))

(defun-sk lr34-l-index-of-type-p ()
  (forall (item array down up)
    (implies
     (and
      (lr34-address-p item)
      (lr34-address-p array)
      (integerp down)
      (integerp up))
     (integerp
      (lr34-l-index-of item array down up)))))

(defun lr34-linked-p ()
  (if (lr34-linked-op) t nil))

(defun lr34-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lr34-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lr34-address-base address))
    (<= 0 (lr34-address-offset address))
    (<=
     (+ (lr34-address-offset address) length)
     (lr34-t (lr34-address-base address))))))

(defun lr34-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lr34-address-base left)
     (lr34-address-base right)))
   (<=
    (+ (lr34-address-offset right) right-length)
    (lr34-address-offset left))
   (<=
    (+ (lr34-address-offset left) left-length)
    (lr34-address-offset right))))

(defun-sk lr34-framed-p ()
  (forall (address)
    (implies
     (lr34-address-p address)
     (<=
      (lr34-region
       (lr34-address-base (lr34-t1 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lr34-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lr34-address-p item)
      (lr34-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lr34-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lr34-t1 (lr34-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lr34-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lr34-t1 (lr34-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lr34-l-index-of item array (+ 1 down) up)
        (lr34-l-index-of item array down up)))))))

;; This recursion is logically equivalent to the source inductive
;; p_linked_n relation: n = 0 is exactly the bound constructor, while n > 0
;; is exactly the cons constructor followed by its predecessor at n - 1.

(defun lr34-p-linked-n-p
    (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lr34-address-p root)
   (lr34-address-p array)
   (integerp index)
   (integerp n)
   (lr34-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lr34-t1 (lr34-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lr34-valid-rw-p root 4)
      (lr34-p-linked-n-p
       (lr34-t1 (lr34-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lr34-a-separated-from-range-p
    (a array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr34-separated-p
      a 1
      (lr34-t1 (lr34-shift array index)) 4))))

(defun-sk lr34-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr34-separated-p
      (lr34-t1 (lr34-shift array index)) 4
      array-base 2147483646))))

(defun-sk lr34-item-separated-from-other-range-p
    (item array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        item
        (lr34-t1 (lr34-shift array index))))
      (<= lower index)
      (< index upper))
     (lr34-separated-p
      item 4
      (lr34-t1 (lr34-shift array index)) 4))))

(defun-sk lr34-range-addresses-distinct-p
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
       (lr34-t1 (lr34-shift array left-index))
       (lr34-t1 (lr34-shift array right-index)))))))

(defun-sk lr34-range-addresses-separated-p
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
     (lr34-separated-p
      (lr34-t1 (lr34-shift array left-index)) 4
      (lr34-t1 (lr34-shift array right-index)) 4))))

(defun-sk lr34-t2-range-excludes-item-p
    (item array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (not
      (equal
       (lr34-t2 (lr34-shift array index))
       item)))))

;; UPDATED-READ is the exact functional update of t_2 at update-address.

(defun lr34-updated-read
    (update-address update-value address)
  (if (equal address update-address)
      update-value
    (lr34-t2 address)))

(defun-sk
    ntp4vc-list-remove-contains-item-itemnotin-part2-goal34-statement ()
  (forall
   (a a1 i2 i i1 i3)
   (implies
    (and
     (lr34-pointer-function-p)
     (lr34-integer-function-p)
     (lr34-region-function-p)
     (lr34-l-index-of-type-p)
     (lr34-l-index-of-laws-p)
     (lr34-address-p a)
     (lr34-address-p a1)
     (integerp i2)
     (integerp i)
     (integerp i1)
     (integerp i3))
    (let*
        ((a2 (lr34-t1 a))
         (a3 (lr34-t1 (lr34-shift a1 i2)))
         (x (+ i i1))
         (a4 (lr34-shift a1 0)))
      (implies
       (and
        (not (equal a2 (lr34-null-address)))
        (not (equal a3 (lr34-null-address)))
        (equal a3 a2)
        (<= 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= i1 i3)
        (< i2 x)
        (<= (lr34-region (lr34-address-base a)) 0)
        (<= (lr34-region (lr34-address-base a1)) 0)
        (<= (lr34-region (lr34-address-base a2)) 0)
        (<= i 2147483645)
        (<= (+ 2 i3) x)
        (lr34-framed-p)
        (lr34-linked-p)
        (lr34-is-sint32-p i)
        (lr34-is-sint32-p i1)
        (lr34-valid-rw-p a 1)
        (lr34-valid-rw-p a4 2147483646)
        (lr34-separated-p a 1 a4 2147483646)
        (lr34-separated-p a2 4 a4 2147483646)
        (lr34-p-linked-n-p
         a2 a1 i1 i (lr34-null-address))
        (lr34-is-sint32-p
         (lr34-l-index-of a3 a1 i1 x))
        (lr34-a-separated-from-range-p
         a a1 i1 x)
        (lr34-range-separated-from-array-p
         a1 i1 x a4)
        (lr34-item-separated-from-other-range-p
         a3 a1 i1 x)
        (lr34-range-addresses-distinct-p
         a1 i1 x)
        (lr34-range-addresses-separated-p
         a1 i1 x)
        (lr34-t2-range-excludes-item-p
         a3 a1 i1 (- x 1)))
       (not
        (equal
         (lr34-updated-read
          a
          (lr34-t1 (lr34-shift a2 0))
          (lr34-shift a1 i3))
         a3)))))))

(value-triple :itpeval-statement-checked)

:q
