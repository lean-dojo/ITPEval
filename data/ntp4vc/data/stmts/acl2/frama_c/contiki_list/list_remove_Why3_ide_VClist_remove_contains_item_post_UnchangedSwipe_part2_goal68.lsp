;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_UnchangedSwipe_part2_goal68:
;; equality of the s1_list records loaded from adjacent pointer-array entries
;; after a single pointer-memory update, under the stated integer bounds,
;; validity, framing, linked-segment, separation, and uniqueness hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lr68-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lr68-address-base (address)
  (car address))

(defun lr68-address-offset (address)
  (cdr address))

(defun lr68-shift (address amount)
  (cons
   (lr68-address-base address)
   (+ (lr68-address-offset address) amount)))

(defun lr68-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2, t_3, and t_4, allocation function t, real-valued
;; memory t_1, fixed region operation, linked proposition specialized to t,
;; and imported l_index_of operation specialized to t_2.
;;
;; The values of t_1 are observed only by equality in the conclusion.
;; Keeping its ACL2 codomain arbitrary preserves every equality pattern of
;; the source real-valued function without narrowing the real domain.

(defstub lr68-t2 (address) t)
(defstub lr68-t3 (address) t)
(defstub lr68-t4 (address) t)
(defstub lr68-t (index) t)
(defstub lr68-t1 (address) t)
(defstub lr68-region (base) t)
(defstub lr68-linked-op () t)
(defstub lr68-l-index-of (item array down up) t)

(defun-sk lr68-function-types-p ()
  (forall (address index base item array down up)
    (implies
     (and
      (lr68-address-p address)
      (integerp index)
      (integerp base)
      (lr68-address-p item)
      (lr68-address-p array)
      (integerp down)
      (integerp up))
     (and
      (lr68-address-p (lr68-t2 address))
      (lr68-address-p (lr68-t3 address))
      (lr68-address-p (lr68-t4 address))
      (integerp (lr68-t index))
      (integerp (lr68-region base))
      (integerp
       (lr68-l-index-of item array down up))))))

(defun lr68-linked-p ()
  (if (lr68-linked-op) t nil))

(defun lr68-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lr68-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lr68-address-base address))
    (<= 0 (lr68-address-offset address))
    (<=
     (+ (lr68-address-offset address) length)
     (lr68-t (lr68-address-base address))))))

(defun lr68-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lr68-address-base left)
     (lr68-address-base right)))
   (<=
    (+ (lr68-address-offset right) right-length)
    (lr68-address-offset left))
   (<=
    (+ (lr68-address-offset left) left-length)
    (lr68-address-offset right))))

(defun-sk lr68-framed-p ()
  (forall (address)
    (implies
     (lr68-address-p address)
     (<=
      (lr68-region
       (lr68-address-base (lr68-t2 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lr68-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lr68-address-p item)
      (lr68-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lr68-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lr68-t2 (lr68-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lr68-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lr68-t2 (lr68-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lr68-l-index-of item array (+ 1 down) up)
        (lr68-l-index-of item array down up)))))))

;; This recursion is logically equivalent to the source inductive p_linked_n
;; relation: n = 0 is its bound constructor, and n > 0 is its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lr68-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lr68-address-p root)
   (lr68-address-p array)
   (integerp index)
   (integerp n)
   (lr68-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lr68-t2 (lr68-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lr68-valid-rw-p root 4)
      (lr68-p-linked-n-p
       (lr68-t2 (lr68-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lr68-a-separated-from-range-p
    (a array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr68-separated-p
      a 1
      (lr68-t2 (lr68-shift array index)) 4))))

(defun-sk lr68-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr68-separated-p
      (lr68-t2 (lr68-shift array index)) 4
      array-base 2147483646))))

(defun-sk lr68-item-separated-from-other-range-p
    (item array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        item
        (lr68-t2 (lr68-shift array index))))
      (<= lower index)
      (< index upper))
     (lr68-separated-p
      item 4
      (lr68-t2 (lr68-shift array index)) 4))))

(defun-sk lr68-range-addresses-distinct-p
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
       (lr68-t2 (lr68-shift array left-index))
       (lr68-t2 (lr68-shift array right-index)))))))

(defun-sk lr68-range-addresses-separated-p
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
     (lr68-separated-p
      (lr68-t2 (lr68-shift array left-index)) 4
      (lr68-t2 (lr68-shift array right-index)) 4))))

;; These are the two post-havoc separation premises, both read from t_3.

(defun-sk lr68-post-a-separated-from-range-p
    (a array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr68-separated-p
      a 1
      (lr68-t3 (lr68-shift array index)) 4))))

(defun-sk lr68-post-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr68-separated-p
      (lr68-t3 (lr68-shift array index)) 4
      array-base 2147483646))))

;; This is the exact source equality
;; havoc t_4 t_2 (shift a_1 i_1) (i - 1) = t_3.

(defun-sk lr68-havoc-state-p
    (array lower length)
  (forall (address)
    (implies
     (lr68-address-p address)
     (equal
      (lr68-t3 address)
      (if
       (lr68-separated-p
        address 1
        (lr68-shift array lower)
        (- length 1))
       (lr68-t2 address)
       (lr68-t4 address))))))

;; This is the source p_array_swipe_left relation between the post-havoc map
;; t_3 and the original map t_2.

(defun-sk lr68-array-swipe-left-before-update-p
    (array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (lr68-t2 (lr68-shift array (+ 1 index)))
      (lr68-t3 (lr68-shift array index))))))

;; UPDATED-READ is the exact functional update of t_3 at update-address.

(defun lr68-updated-read
    (update-address update-value address)
  (if (equal address update-address)
      update-value
    (lr68-t3 address)))

;; The source s1_list record is the product of one address and three scalar
;; fields. LOAD-S1-LIST and EQS1-LIST-P are direct unfoldings of the source
;; definitions; :UPDATED selects m and :BASE selects t_2.

(defun lr68-s1-list (next x y z)
  (list next x y z))

(defun lr68-pointer-read
    (memory-kind update-address update-value address)
  (if (equal memory-kind :updated)
      (lr68-updated-read update-address update-value address)
    (lr68-t2 address)))

(defun lr68-load-s1-list
    (memory-kind update-address update-value address)
  (lr68-s1-list
   (lr68-pointer-read
    memory-kind update-address update-value
    (lr68-shift address 0))
   (lr68-t1 (lr68-shift address 1))
   (lr68-t1 (lr68-shift address 2))
   (lr68-t1 (lr68-shift address 3))))

(defun lr68-eqs1-list-p (left right)
  (and
   (equal (nth 0 right) (nth 0 left))
   (equal (nth 1 right) (nth 1 left))
   (equal (nth 2 right) (nth 2 left))
   (equal (nth 3 right) (nth 3 left))))

(defun-sk
    ntp4vc-list-remove-contains-item-unchanged-swipe-part2-goal68-statement
    ()
  (forall
   (a a1 i2 i i1 i3)
   (implies
    (and
     (lr68-function-types-p)
     (lr68-l-index-of-laws-p)
     (lr68-address-p a)
     (lr68-address-p a1)
     (integerp i2)
     (integerp i)
     (integerp i1)
     (integerp i3))
    (let*
        ((a2 (lr68-t2 a))
         (a3 (lr68-t2 (lr68-shift a1 i2)))
         (x (+ i i1))
         (x1 (lr68-l-index-of a3 a1 i1 x))
         (a4 (lr68-shift a1 0))
         (update-value
          (lr68-t2 (lr68-shift a2 0))))
      (implies
       (and
        (not (equal a2 (lr68-null-address)))
        (not (equal a3 (lr68-null-address)))
        (equal a3 a2)
        (<= 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (< i2 x)
        (<= (lr68-region (lr68-address-base a)) 0)
        (<= (lr68-region (lr68-address-base a1)) 0)
        (<= (lr68-region (lr68-address-base a2)) 0)
        (<= x1 i3)
        (<= i 2147483645)
        (<= (+ 2 i3) x)
        (lr68-framed-p)
        (lr68-linked-p)
        (lr68-is-sint32-p i)
        (lr68-is-sint32-p i1)
        (lr68-valid-rw-p a 1)
        (lr68-valid-rw-p a4 2147483646)
        (lr68-separated-p a 1 a4 2147483646)
        (lr68-separated-p a2 4 a4 2147483646)
        (lr68-p-linked-n-p
         a2 a1 i1 i (lr68-null-address))
        (lr68-is-sint32-p x1)
        (lr68-a-separated-from-range-p
         a a1 i1 x)
        (lr68-range-separated-from-array-p
         a1 i1 x a4)
        (lr68-item-separated-from-other-range-p
         a3 a1 i1 x)
        (lr68-range-addresses-distinct-p
         a1 i1 x)
        (lr68-range-addresses-separated-p
         a1 i1 x)
        (lr68-havoc-state-p a1 i1 i)
        (lr68-array-swipe-left-before-update-p
         a1 i1 (- (+ i i1) 1))
        (lr68-post-a-separated-from-range-p
         a a1 i1 (- (+ i i1) 1))
        (lr68-post-range-separated-from-array-p
         a1 i1 (- (+ i i1) 1) a4))
       (lr68-eqs1-list-p
        (lr68-load-s1-list
         :updated a update-value
         (lr68-updated-read
          a update-value
          (lr68-shift a1 i3)))
        (lr68-load-s1-list
         :base a update-value
         (lr68-t2
          (lr68-shift a1 (+ 1 i3))))))))))

(value-triple :itpeval-statement-checked)

:q
