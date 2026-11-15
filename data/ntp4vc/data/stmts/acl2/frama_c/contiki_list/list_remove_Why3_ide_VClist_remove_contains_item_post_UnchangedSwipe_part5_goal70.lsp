;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_UnchangedSwipe_part5_goal70:
;; equality of the s1_list records loaded from an updated pointer-array entry
;; and its original successor, under the stated integer bounds, validity,
;; framing, linked-segment, unchanged-memory, separation, and uniqueness
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lr70-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lr70-address-base (address)
  (car address))

(defun lr70-address-offset (address)
  (cdr address))

(defun lr70-shift (address amount)
  (cons
   (lr70-address-base address)
   (+ (lr70-address-offset address) amount)))

(defun lr70-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2, t_3, and t_4, allocation function t, real-valued
;; memory t_1, fixed region operation, linked proposition specialized to t,
;; and imported l_index_of operation specialized to t_2.
;;
;; The values of t_1 are observed only by equality. Keeping its ACL2 codomain
;; arbitrary preserves every equality pattern of the source real-valued
;; function without narrowing the real domain.

(defstub lr70-t2 (address) t)
(defstub lr70-t3 (address) t)
(defstub lr70-t4 (address) t)
(defstub lr70-t (index) t)
(defstub lr70-t1 (address) t)
(defstub lr70-region (base) t)
(defstub lr70-linked-op () t)
(defstub lr70-l-index-of (item array down up) t)

(defun-sk lr70-function-types-p ()
  (forall (address index base item array down up)
    (implies
     (and
      (lr70-address-p address)
      (integerp index)
      (integerp base)
      (lr70-address-p item)
      (lr70-address-p array)
      (integerp down)
      (integerp up))
     (and
      (lr70-address-p (lr70-t2 address))
      (lr70-address-p (lr70-t3 address))
      (lr70-address-p (lr70-t4 address))
      (integerp (lr70-t index))
      (integerp (lr70-region base))
      (integerp
       (lr70-l-index-of item array down up))))))

(defun lr70-linked-p ()
  (if (lr70-linked-op) t nil))

(defun lr70-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lr70-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lr70-address-base address))
    (<= 0 (lr70-address-offset address))
    (<=
     (+ (lr70-address-offset address) length)
     (lr70-t (lr70-address-base address))))))

(defun lr70-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lr70-address-base left)
     (lr70-address-base right)))
   (<=
    (+ (lr70-address-offset right) right-length)
    (lr70-address-offset left))
   (<=
    (+ (lr70-address-offset left) left-length)
    (lr70-address-offset right))))

(defun-sk lr70-framed-p ()
  (forall (address)
    (implies
     (lr70-address-p address)
     (<=
      (lr70-region
       (lr70-address-base (lr70-t2 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lr70-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lr70-address-p item)
      (lr70-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lr70-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lr70-t2 (lr70-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lr70-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lr70-t2 (lr70-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lr70-l-index-of item array (+ 1 down) up)
        (lr70-l-index-of item array down up)))))))

;; This recursion is logically equivalent to the source inductive p_linked_n
;; relation: n = 0 is its bound constructor, and n > 0 is its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lr70-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lr70-address-p root)
   (lr70-address-p array)
   (integerp index)
   (integerp n)
   (lr70-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lr70-t2 (lr70-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lr70-valid-rw-p root 4)
      (lr70-p-linked-n-p
       (lr70-t2 (lr70-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

;; This unfolds the source p_unchanged premise at identical old and new
;; allocation, pointer, and scalar memories.

(defun-sk lr70-reflexive-unchanged-p (array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lr70-shift array index))
          (left-address (lr70-t2 slot))
          (right-address (lr70-t2 slot)))
       (and
        (equal left-address right-address)
        (equal
         (lr70-t2 (lr70-shift right-address 0))
         (lr70-t2 (lr70-shift left-address 0)))
        (equal
         (lr70-t1 (lr70-shift right-address 1))
         (lr70-t1 (lr70-shift left-address 1)))
        (equal
         (lr70-t1 (lr70-shift right-address 2))
         (lr70-t1 (lr70-shift left-address 2)))
        (equal
         (lr70-t1 (lr70-shift right-address 3))
         (lr70-t1 (lr70-shift left-address 3)))
        (implies
         (lr70-valid-rw-p right-address 4)
         (lr70-valid-rw-p left-address 4)))))))

(defun-sk lr70-a5-absent-through-i3-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (not
      (equal
       (lr70-t2 (lr70-shift array index))
       a5)))))

(defun-sk lr70-a1-separated-from-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr70-separated-p
      a1 1
      (lr70-t2 (lr70-shift array index)) 4))))

(defun-sk lr70-a5-separated-from-prefix-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr70-separated-p
      a5 4
      (lr70-t2 (lr70-shift array index)) 4))))

(defun-sk lr70-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr70-separated-p
      (lr70-t2 (lr70-shift array index)) 4
      array-base 2147483646))))

(defun-sk lr70-a6-separated-from-other-range-p
    (a6 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        a6
        (lr70-t2 (lr70-shift array index))))
      (<= lower index)
      (< index upper))
     (lr70-separated-p
      a6 4
      (lr70-t2 (lr70-shift array index)) 4))))

(defun-sk lr70-range-addresses-distinct-p
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
       (lr70-t2 (lr70-shift array left-index))
       (lr70-t2 (lr70-shift array right-index)))))))

(defun-sk lr70-range-addresses-separated-p
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
     (lr70-separated-p
      (lr70-t2 (lr70-shift array left-index)) 4
      (lr70-t2 (lr70-shift array right-index)) 4))))

;; These are the two post-havoc separation premises, both read from t_3.

(defun-sk lr70-post-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr70-separated-p
      (lr70-t3 (lr70-shift array index)) 4
      array-base 2147483646))))

(defun-sk lr70-post-range-addresses-separated-p
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
     (lr70-separated-p
      (lr70-t3 (lr70-shift array left-index)) 4
      (lr70-t3 (lr70-shift array right-index)) 4))))

;; This is the exact source equality
;; havoc t_4 t_2 (shift a_2 (1 + i_3))
;;   (i + i_1 - 2 - i_3) = t_3.

(defun-sk lr70-havoc-state-p
    (array lower length)
  (forall (address)
    (implies
     (lr70-address-p address)
     (equal
      (lr70-t3 address)
      (if
       (lr70-separated-p
        address 1
        (lr70-shift array lower)
        length)
       (lr70-t2 address)
       (lr70-t4 address))))))

;; This is the source p_array_swipe_left relation between the post-havoc map
;; t_3 and the original map t_2.

(defun-sk lr70-array-swipe-left-before-update-p
    (array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (lr70-t2 (lr70-shift array (+ 1 index)))
      (lr70-t3 (lr70-shift array index))))))

;; UPDATED-READ is the exact source functional update of t_3 at
;; update-address.

(defun lr70-updated-read
    (update-address update-value address)
  (if (equal address update-address)
      update-value
    (lr70-t3 address)))

;; The source s1_list record is the product of one address and three scalar
;; fields. LOAD-S1-LIST and EQS1-LIST-P are direct unfoldings of the source
;; definitions; :UPDATED selects m and :BASE selects t_2.

(defun lr70-s1-list (next x y z)
  (list next x y z))

(defun lr70-pointer-read
    (memory-kind update-address update-value address)
  (if (equal memory-kind :updated)
      (lr70-updated-read update-address update-value address)
    (lr70-t2 address)))

(defun lr70-load-s1-list
    (memory-kind update-address update-value address)
  (lr70-s1-list
   (lr70-pointer-read
    memory-kind update-address update-value
    (lr70-shift address 0))
   (lr70-t1 (lr70-shift address 1))
   (lr70-t1 (lr70-shift address 2))
   (lr70-t1 (lr70-shift address 3))))

(defun lr70-eqs1-list-p (left right)
  (and
   (equal (nth 0 right) (nth 0 left))
   (equal (nth 1 right) (nth 1 left))
   (equal (nth 2 right) (nth 2 left))
   (equal (nth 3 right) (nth 3 left))))

(defun-sk
    ntp4vc-list-remove-contains-item-unchanged-swipe-part5-goal70-statement
    ()
  (forall
   (a1 a a2 i2 i i1 i3 i4)
   (implies
    (and
     (lr70-function-types-p)
     (lr70-l-index-of-laws-p)
     (lr70-address-p a1)
     (lr70-address-p a)
     (lr70-address-p a2)
     (integerp i2)
     (integerp i)
     (integerp i1)
     (integerp i3)
     (integerp i4))
    (let*
        ((a3 (lr70-t2 a1))
         (a4 (lr70-shift a 0))
         (a5 (lr70-t2 a4))
         (a6 (lr70-t2 (lr70-shift a2 i2)))
         (x (+ i i1))
         (x1 (lr70-l-index-of a6 a2 i1 x))
         (a7 (lr70-shift a2 0))
         (update-value
          (lr70-t2 (lr70-shift a5 0))))
      (implies
       (and
        (not (equal a3 (lr70-null-address)))
        (not (equal a5 a3))
        (not (equal a6 (lr70-null-address)))
        (equal a6 a5)
        (<= 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= i1 i3)
        (< i2 x)
        (<= i3 x)
        (<= (lr70-region (lr70-address-base a1)) 0)
        (<= (lr70-region (lr70-address-base a2)) 0)
        (<= (lr70-region (lr70-address-base a5)) 0)
        (<= x1 i4)
        (<= i 2147483645)
        (<= (+ 2 i4) x)
        (lr70-framed-p)
        (lr70-linked-p)
        (lr70-is-sint32-p i)
        (lr70-is-sint32-p i1)
        (lr70-is-sint32-p i3)
        (lr70-valid-rw-p a1 1)
        (lr70-valid-rw-p a7 2147483646)
        (lr70-separated-p a1 1 a7 2147483646)
        (lr70-separated-p a3 4 a7 2147483646)
        (lr70-p-linked-n-p
         a3 a2 i1 i (lr70-null-address))
        (lr70-reflexive-unchanged-p a2 i1 i3)
        (lr70-p-linked-n-p
         a a2 i3 1 a5)
        (lr70-is-sint32-p x1)
        (lr70-p-linked-n-p
         a3 a2 i1 (- i3 i1) a)
        (lr70-p-linked-n-p
         a5 a2 (+ 1 i3)
         (- (- (+ i i1) 1) i3)
         (lr70-null-address))
        (lr70-a5-absent-through-i3-p
         a5 a2 i1 i3)
        (lr70-a1-separated-from-range-p
         a1 a2 i1 x)
        (lr70-a5-separated-from-prefix-p
         a5 a2 i1 i3)
        (lr70-range-separated-from-array-p
         a2 i1 x a7)
        (lr70-a6-separated-from-other-range-p
         a6 a2 i1 x)
        (lr70-range-addresses-distinct-p
         a2 i1 x)
        (lr70-range-addresses-separated-p
         a2 i1 x)
        (lr70-havoc-state-p
         a2 (+ 1 i3)
         (- (- (+ i i1) 2) i3))
        (lr70-array-swipe-left-before-update-p
         a2 (+ 1 i3) (- (+ i i1) 1))
        (lr70-post-range-separated-from-array-p
         a2 i1 (- (+ i i1) 1) a7)
        (lr70-post-range-addresses-separated-p
         a2 i1 (- (+ i i1) 1)))
       (lr70-eqs1-list-p
        (lr70-load-s1-list
         :updated a4 update-value
         (lr70-updated-read
          a4 update-value
          (lr70-shift a2 i4)))
        (lr70-load-s1-list
         :base a4 update-value
         (lr70-t2
          (lr70-shift a2 (+ 1 i4))))))))))

(value-triple :itpeval-statement-checked)

:q
