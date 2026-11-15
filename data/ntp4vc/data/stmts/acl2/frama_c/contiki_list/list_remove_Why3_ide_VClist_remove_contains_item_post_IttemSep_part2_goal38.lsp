;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_IttemSep_part2_goal38:
;; separation of the removed list item from the pointer stored by the
;; functional update, under the linked-list, memory-validity, framing,
;; range-separation, and uniqueness hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lr38-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lr38-address-base (address)
  (car address))

(defun lr38-address-offset (address)
  (cdr address))

(defun lr38-shift (address amount)
  (cons
   (lr38-address-base address)
   (+ (lr38-address-offset address) amount)))

(defun lr38-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_1, t_2, and t_3, allocation function t,
;; fixed region operation,
;; linked proposition specialized to t, and imported l_index_of operation
;; specialized to t_1.

(defstub lr38-t1 (address) t)
(defstub lr38-t2 (address) t)
(defstub lr38-t3 (address) t)
(defstub lr38-t (index) t)
(defstub lr38-region (base) t)
(defstub lr38-linked-op () t)
(defstub lr38-l-index-of (item array down up) t)

(defun-sk lr38-pointer-function-p ()
  (forall (address)
    (implies
     (lr38-address-p address)
     (and
      (lr38-address-p (lr38-t1 address))
      (lr38-address-p (lr38-t2 address))
      (lr38-address-p (lr38-t3 address))))))

(defun-sk lr38-integer-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lr38-t index)))))

(defun-sk lr38-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lr38-region base)))))

(defun-sk lr38-l-index-of-type-p ()
  (forall (item array down up)
    (implies
     (and
      (lr38-address-p item)
      (lr38-address-p array)
      (integerp down)
      (integerp up))
     (integerp
      (lr38-l-index-of item array down up)))))

(defun lr38-linked-p ()
  (if (lr38-linked-op) t nil))

(defun lr38-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lr38-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lr38-address-base address))
    (<= 0 (lr38-address-offset address))
    (<=
     (+ (lr38-address-offset address) length)
     (lr38-t (lr38-address-base address))))))

(defun lr38-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lr38-address-base left)
     (lr38-address-base right)))
   (<=
    (+ (lr38-address-offset right) right-length)
    (lr38-address-offset left))
   (<=
    (+ (lr38-address-offset left) left-length)
    (lr38-address-offset right))))

(defun-sk lr38-framed-p ()
  (forall (address)
    (implies
     (lr38-address-p address)
     (<=
      (lr38-region
       (lr38-address-base (lr38-t1 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lr38-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lr38-address-p item)
      (lr38-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lr38-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lr38-t1 (lr38-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lr38-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lr38-t1 (lr38-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lr38-l-index-of item array (+ 1 down) up)
        (lr38-l-index-of item array down up)))))))

;; This recursion is logically equivalent to the source inductive
;; p_linked_n relation: n = 0 is exactly the bound constructor, while n > 0
;; is exactly the cons constructor followed by its predecessor at n - 1.

(defun lr38-p-linked-n-p
    (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lr38-address-p root)
   (lr38-address-p array)
   (integerp index)
   (integerp n)
   (lr38-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lr38-t1 (lr38-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lr38-valid-rw-p root 4)
      (lr38-p-linked-n-p
       (lr38-t1 (lr38-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lr38-a-separated-from-range-p
    (a array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr38-separated-p
      a 1
      (lr38-t1 (lr38-shift array index)) 4))))

(defun-sk lr38-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr38-separated-p
      (lr38-t1 (lr38-shift array index)) 4
      array-base 2147483646))))

(defun-sk lr38-item-separated-from-other-range-p
    (item array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        item
        (lr38-t1 (lr38-shift array index))))
      (<= lower index)
      (< index upper))
     (lr38-separated-p
      item 4
      (lr38-t1 (lr38-shift array index)) 4))))

(defun-sk lr38-range-addresses-distinct-p
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
       (lr38-t1 (lr38-shift array left-index))
       (lr38-t1 (lr38-shift array right-index)))))))

(defun-sk lr38-range-addresses-separated-p
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
     (lr38-separated-p
     (lr38-t1 (lr38-shift array left-index)) 4
     (lr38-t1 (lr38-shift array right-index)) 4))))

;; This is the pointwise form of
;;   havoc t_3 t_1 (shift a_1 i_1) (i - 1) = t_2.

(defun-sk lr38-havoc-state-p (start length)
  (forall (address)
    (implies
     (lr38-address-p address)
     (equal
      (lr38-t2 address)
      (if (lr38-separated-p address 1 start length)
          (lr38-t1 address)
        (lr38-t3 address))))))

(defun-sk lr38-post-havoc-root-separated-p
    (root array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr38-separated-p
      root 4
      (lr38-t2 (lr38-shift array index)) 4))))

;; UPDATED-READ is the exact source functional update of t_2 at
;; update-address.

(defun lr38-updated-read
    (update-address update-value address)
  (if (equal address update-address)
      update-value
    (lr38-t2 address)))

(defun-sk
    ntp4vc-list-remove-contains-item-ittemsep-part2-goal38-statement ()
  (forall
   (a a1 i2 i i1 i3)
   (implies
    (and
     (lr38-pointer-function-p)
     (lr38-integer-function-p)
     (lr38-region-function-p)
     (lr38-l-index-of-type-p)
     (lr38-l-index-of-laws-p)
     (lr38-address-p a)
     (lr38-address-p a1)
     (integerp i2)
     (integerp i)
     (integerp i1)
     (integerp i3))
    (let*
        ((a2 (lr38-t1 a))
         (a3 (lr38-t1 (lr38-shift a1 i2)))
         (x (+ i i1))
         (a4 (lr38-shift a1 0)))
      (implies
       (and
        (not (equal a2 (lr38-null-address)))
        (not (equal a3 (lr38-null-address)))
        (equal a3 a2)
        (<= 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= i1 i3)
        (< i2 x)
        (<= (lr38-region (lr38-address-base a)) 0)
        (<= (lr38-region (lr38-address-base a1)) 0)
        (<= (lr38-region (lr38-address-base a2)) 0)
        (<= i 2147483645)
        (<= (+ 2 i3) x)
        (lr38-framed-p)
        (lr38-linked-p)
        (lr38-is-sint32-p i)
        (lr38-is-sint32-p i1)
        (lr38-valid-rw-p a 1)
        (lr38-valid-rw-p a4 2147483646)
        (lr38-separated-p a 1 a4 2147483646)
        (lr38-separated-p a2 4 a4 2147483646)
        (lr38-p-linked-n-p
         a2 a1 i1 i (lr38-null-address))
        (lr38-is-sint32-p
         (lr38-l-index-of a3 a1 i1 x))
        (lr38-a-separated-from-range-p
         a a1 i1 x)
        (lr38-range-separated-from-array-p
         a1 i1 x a4)
        (lr38-item-separated-from-other-range-p
         a3 a1 i1 x)
        (lr38-range-addresses-distinct-p
         a1 i1 x)
        (lr38-range-addresses-separated-p
         a1 i1 x)
        (lr38-havoc-state-p
         (lr38-shift a1 i1)
         (- i 1))
        (lr38-post-havoc-root-separated-p
         a2 a1 i1 (- x 1)))
       (lr38-separated-p
        a3
        4
        (lr38-updated-read
         a
         (lr38-t1 (lr38-shift a2 0))
         (lr38-shift a1 i3))
        4))))))

(value-triple :itpeval-statement-checked)

:q
