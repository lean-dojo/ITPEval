;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_Unchanged_part5_goal60:
;; preservation of the unchanged-memory relation on the prefix preceding the
;; removed list item after a single pointer-memory update, under the stated
;; integer bounds, validity, framing, linked-segment, separation, and
;; uniqueness hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lr60-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lr60-address-base (address)
  (car address))

(defun lr60-address-offset (address)
  (cdr address))

(defun lr60-shift (address amount)
  (cons
   (lr60-address-base address)
   (+ (lr60-address-offset address) amount)))

(defun lr60-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_2, allocation function t, real-valued memory t_1,
;; fixed region operation, linked proposition specialized to t, and imported
;; l_index_of operation specialized to t_2.
;;
;; Values of t_1 are observed only by equality. Since the address domain is
;; countable, every possible equality pattern of a real-valued source memory
;; has an equivalent arbitrary-codomain ACL2 representation, and conversely
;; every such pattern can be represented by real values.

(defstub lr60-t2 (address) t)
(defstub lr60-t (index) t)
(defstub lr60-t1 (address) t)
(defstub lr60-region (base) t)
(defstub lr60-linked-op () t)
(defstub lr60-l-index-of (item array down up) t)

(defun-sk lr60-function-types-p ()
  (forall (address index base item array down up)
    (implies
     (and
      (lr60-address-p address)
      (integerp index)
      (integerp base)
      (lr60-address-p item)
      (lr60-address-p array)
      (integerp down)
      (integerp up))
     (and
      (lr60-address-p (lr60-t2 address))
      (integerp (lr60-t index))
      (integerp (lr60-region base))
      (integerp
       (lr60-l-index-of item array down up))))))

(defun lr60-linked-p ()
  (if (lr60-linked-op) t nil))

(defun lr60-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lr60-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lr60-address-base address))
    (<= 0 (lr60-address-offset address))
    (<=
     (+ (lr60-address-offset address) length)
     (lr60-t (lr60-address-base address))))))

(defun lr60-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lr60-address-base left)
     (lr60-address-base right)))
   (<=
    (+ (lr60-address-offset right) right-length)
    (lr60-address-offset left))
   (<=
    (+ (lr60-address-offset left) left-length)
    (lr60-address-offset right))))

(defun-sk lr60-framed-p ()
  (forall (address)
    (implies
     (lr60-address-p address)
     (<=
      (lr60-region
       (lr60-address-base (lr60-t2 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lr60-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lr60-address-p item)
      (lr60-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lr60-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lr60-t2 (lr60-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lr60-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lr60-t2 (lr60-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lr60-l-index-of item array (+ 1 down) up)
        (lr60-l-index-of item array down up)))))))

;; This recursion is logically equivalent to the source inductive p_linked_n
;; relation: n = 0 is its bound constructor, and n > 0 is its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lr60-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lr60-address-p root)
   (lr60-address-p array)
   (integerp index)
   (integerp n)
   (lr60-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lr60-t2 (lr60-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lr60-valid-rw-p root 4)
      (lr60-p-linked-n-p
       (lr60-t2 (lr60-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

;; This unfolds the source p_unchanged premise at identical old and new
;; allocation, pointer, and scalar memories.

(defun-sk lr60-reflexive-unchanged-p (array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lr60-shift array index))
          (left-address (lr60-t2 slot))
          (right-address (lr60-t2 slot)))
       (and
        (equal left-address right-address)
        (equal
         (lr60-t2 (lr60-shift right-address 0))
         (lr60-t2 (lr60-shift left-address 0)))
        (equal
         (lr60-t1 (lr60-shift right-address 1))
         (lr60-t1 (lr60-shift left-address 1)))
        (equal
         (lr60-t1 (lr60-shift right-address 2))
         (lr60-t1 (lr60-shift left-address 2)))
        (equal
         (lr60-t1 (lr60-shift right-address 3))
         (lr60-t1 (lr60-shift left-address 3)))
        (implies
         (lr60-valid-rw-p right-address 4)
         (lr60-valid-rw-p left-address 4)))))))

(defun-sk lr60-a5-absent-through-i3-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (not
      (equal
       (lr60-t2 (lr60-shift array index))
       a5)))))

(defun-sk lr60-a1-separated-from-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr60-separated-p
      a1 1
      (lr60-t2 (lr60-shift array index)) 4))))

(defun-sk lr60-a5-separated-from-prefix-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr60-separated-p
      a5 4
      (lr60-t2 (lr60-shift array index)) 4))))

(defun-sk lr60-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr60-separated-p
      (lr60-t2 (lr60-shift array index)) 4
      array-base 2147483646))))

(defun-sk lr60-a6-separated-from-other-range-p
    (a6 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        a6
        (lr60-t2 (lr60-shift array index))))
      (<= lower index)
      (< index upper))
     (lr60-separated-p
      a6 4
      (lr60-t2 (lr60-shift array index)) 4))))

(defun-sk lr60-range-addresses-distinct-p
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
       (lr60-t2 (lr60-shift array left-index))
       (lr60-t2 (lr60-shift array right-index)))))))

(defun-sk lr60-range-addresses-separated-p
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
     (lr60-separated-p
      (lr60-t2 (lr60-shift array left-index)) 4
      (lr60-t2 (lr60-shift array right-index)) 4))))

;; UPDATED-READ is the exact source functional update of t_2 at
;; update-address.

(defun lr60-updated-read
    (update-address update-value address)
  (if (equal address update-address)
      update-value
    (lr60-t2 address)))

;; This directly unfolds the source conclusion
;; p_unchanged t updated-t_2 t_1 t t_2 t_1 array down up.

(defun-sk lr60-unchanged-after-update-p
    (array down up update-address update-value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lr60-shift array index))
          (updated-address
           (lr60-updated-read
            update-address update-value slot))
          (original-address (lr60-t2 slot)))
       (and
        (equal updated-address original-address)
        (equal
         (lr60-updated-read
          update-address update-value
          (lr60-shift updated-address 0))
         (lr60-t2 (lr60-shift original-address 0)))
        (equal
         (lr60-t1 (lr60-shift updated-address 1))
         (lr60-t1 (lr60-shift original-address 1)))
        (equal
         (lr60-t1 (lr60-shift updated-address 2))
         (lr60-t1 (lr60-shift original-address 2)))
        (equal
         (lr60-t1 (lr60-shift updated-address 3))
         (lr60-t1 (lr60-shift original-address 3)))
        (implies
         (lr60-valid-rw-p original-address 4)
         (lr60-valid-rw-p updated-address 4)))))))

(defun-sk
    ntp4vc-list-remove-contains-item-unchanged-part5-goal60-statement
    ()
  (forall
   (a1 a a2 i2 i i1 i3)
   (implies
    (and
     (lr60-function-types-p)
     (lr60-l-index-of-laws-p)
     (lr60-address-p a1)
     (lr60-address-p a)
     (lr60-address-p a2)
     (integerp i2)
     (integerp i)
     (integerp i1)
     (integerp i3))
    (let*
        ((a3 (lr60-t2 a1))
         (a4 (lr60-shift a 0))
         (a5 (lr60-t2 a4))
         (a6 (lr60-t2 (lr60-shift a2 i2)))
         (x (+ i i1))
         (a7 (lr60-shift a2 0))
         (x1 (lr60-l-index-of a6 a2 i1 x))
         (update-value
          (lr60-t2 (lr60-shift a5 0))))
      (implies
       (and
        (not (equal a3 (lr60-null-address)))
        (not (equal a5 a3))
        (not (equal a6 (lr60-null-address)))
        (equal a6 a5)
        (<= 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= i1 i3)
        (< i2 x)
        (<= i3 x)
        (<= (lr60-region (lr60-address-base a1)) 0)
        (<= (lr60-region (lr60-address-base a2)) 0)
        (<= (lr60-region (lr60-address-base a5)) 0)
        (<= i 2147483645)
        (lr60-framed-p)
        (lr60-linked-p)
        (lr60-is-sint32-p i)
        (lr60-is-sint32-p i1)
        (lr60-is-sint32-p i3)
        (lr60-valid-rw-p a1 1)
        (lr60-valid-rw-p a7 2147483646)
        (lr60-separated-p a1 1 a7 2147483646)
        (lr60-separated-p a3 4 a7 2147483646)
        (lr60-p-linked-n-p
         a3 a2 i1 i (lr60-null-address))
        (lr60-reflexive-unchanged-p a2 i1 i3)
        (lr60-p-linked-n-p
         a a2 i3 1 a5)
        (lr60-is-sint32-p x1)
        (lr60-p-linked-n-p
         a3 a2 i1 (- i3 i1) a)
        (lr60-p-linked-n-p
         a5 a2 (+ 1 i3)
         (- (- (+ i i1) 1) i3)
         (lr60-null-address))
        (lr60-a5-absent-through-i3-p
         a5 a2 i1 i3)
        (lr60-a1-separated-from-range-p
         a1 a2 i1 x)
        (lr60-a5-separated-from-prefix-p
         a5 a2 i1 i3)
        (lr60-range-separated-from-array-p
         a2 i1 x a7)
        (lr60-a6-separated-from-other-range-p
         a6 a2 i1 x)
        (lr60-range-addresses-distinct-p
         a2 i1 x)
        (lr60-range-addresses-separated-p
         a2 i1 x))
       (lr60-unchanged-after-update-p
        a2 i1 (- x1 1) a4 update-value))))))

(value-triple :itpeval-statement-checked)

:q
