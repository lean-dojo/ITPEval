;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_ItemNotIn_part5_goal36:
;; exclusion of the removed linked-list item from a later updated pointer-array
;; position, under integer bounds, memory validity, framing, linked-segment,
;; separation, unchanged-memory, and uniqueness hypotheses. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lr36-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lr36-address-base (address)
  (car address))

(defun lr36-address-offset (address)
  (cdr address))

(defun lr36-shift (address amount)
  (cons
   (lr36-address-base address)
   (+ (lr36-address-offset address) amount)))

(defun lr36-null-address ()
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

(defstub lr36-t2 (address) t)
(defstub lr36-t3 (address) t)
(defstub lr36-t4 (address) t)
(defstub lr36-t (index) t)
(defstub lr36-t1 (address) t)
(defstub lr36-region (base) t)
(defstub lr36-linked-op () t)
(defstub lr36-l-index-of (item array down up) t)

(defun-sk lr36-function-types-p ()
  (forall (address index base item array down up)
    (implies
     (and
      (lr36-address-p address)
      (integerp index)
      (integerp base)
      (lr36-address-p item)
      (lr36-address-p array)
      (integerp down)
      (integerp up))
     (and
      (lr36-address-p (lr36-t2 address))
      (lr36-address-p (lr36-t3 address))
      (lr36-address-p (lr36-t4 address))
      (integerp (lr36-t index))
      (integerp (lr36-region base))
      (integerp
       (lr36-l-index-of item array down up))))))

(defun lr36-linked-p ()
  (if (lr36-linked-op) t nil))

(defun lr36-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lr36-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lr36-address-base address))
    (<= 0 (lr36-address-offset address))
    (<=
     (+ (lr36-address-offset address) length)
     (lr36-t (lr36-address-base address))))))

(defun lr36-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lr36-address-base left)
     (lr36-address-base right)))
   (<=
    (+ (lr36-address-offset right) right-length)
    (lr36-address-offset left))
   (<=
    (+ (lr36-address-offset left) left-length)
    (lr36-address-offset right))))

(defun-sk lr36-framed-p ()
  (forall (address)
    (implies
     (lr36-address-p address)
     (<=
      (lr36-region
       (lr36-address-base (lr36-t2 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lr36-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lr36-address-p item)
      (lr36-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lr36-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lr36-t2 (lr36-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lr36-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lr36-t2 (lr36-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lr36-l-index-of item array (+ 1 down) up)
        (lr36-l-index-of item array down up)))))))

;; This recursion is logically equivalent to the source inductive p_linked_n
;; relation: n = 0 is its bound constructor, and n > 0 is its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lr36-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lr36-address-p root)
   (lr36-address-p array)
   (integerp index)
   (integerp n)
   (lr36-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lr36-t2 (lr36-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lr36-valid-rw-p root 4)
      (lr36-p-linked-n-p
       (lr36-t2 (lr36-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

;; This unfolds the source p_unchanged premise at identical old and new
;; allocation, pointer, and scalar memories.

(defun-sk lr36-reflexive-unchanged-p (array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lr36-shift array index))
          (left-address (lr36-t2 slot))
          (right-address (lr36-t2 slot)))
       (and
        (equal left-address right-address)
        (equal
         (lr36-t2 (lr36-shift right-address 0))
         (lr36-t2 (lr36-shift left-address 0)))
        (equal
         (lr36-t1 (lr36-shift right-address 1))
         (lr36-t1 (lr36-shift left-address 1)))
        (equal
         (lr36-t1 (lr36-shift right-address 2))
         (lr36-t1 (lr36-shift left-address 2)))
        (equal
         (lr36-t1 (lr36-shift right-address 3))
         (lr36-t1 (lr36-shift left-address 3)))
        (implies
         (lr36-valid-rw-p right-address 4)
         (lr36-valid-rw-p left-address 4)))))))

(defun-sk lr36-a5-absent-through-i3-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (not
      (equal
       (lr36-t2 (lr36-shift array index))
       a5)))))

(defun-sk lr36-a1-separated-from-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr36-separated-p
      a1 1
      (lr36-t2 (lr36-shift array index)) 4))))

(defun-sk lr36-a5-separated-from-prefix-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr36-separated-p
      a5 4
      (lr36-t2 (lr36-shift array index)) 4))))

(defun-sk lr36-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr36-separated-p
      (lr36-t2 (lr36-shift array index)) 4
      array-base 2147483646))))

(defun-sk lr36-a6-separated-from-other-range-p
    (a6 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        a6
        (lr36-t2 (lr36-shift array index))))
      (<= lower index)
      (< index upper))
     (lr36-separated-p
      a6 4
      (lr36-t2 (lr36-shift array index)) 4))))

(defun-sk lr36-range-addresses-distinct-p
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
       (lr36-t2 (lr36-shift array left-index))
       (lr36-t2 (lr36-shift array right-index)))))))

(defun-sk lr36-range-addresses-separated-p
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
     (lr36-separated-p
     (lr36-t2 (lr36-shift array left-index)) 4
     (lr36-t2 (lr36-shift array right-index)) 4))))

;; Memory.havoc old outside start size keeps OUTSIDE outside the byte range
;; and OLD inside it. This is the pointwise form of the source equality
;;   havoc t_4 t_2 (shift a_2 (1 + i_3)) (i + i_1 - 2 - i_3) = t_3.

(defun-sk lr36-havoc-state-p (start length)
  (forall (address)
    (implies
     (lr36-address-p address)
     (equal
      (lr36-t3 address)
      (if (lr36-separated-p address 1 start length)
          (lr36-t2 address)
        (lr36-t4 address))))))

(defun-sk lr36-t3-range-excludes-a5-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (not
      (equal
       (lr36-t3 (lr36-shift array index))
       a5)))))

;; UPDATED-READ is the exact functional update of t_3 at update-address.

(defun lr36-updated-read
    (update-address update-value address)
  (if (equal address update-address)
      update-value
    (lr36-t3 address)))

(defun-sk
    ntp4vc-list-remove-contains-item-itemnotin-part5-goal36-statement ()
  (forall
   (a1 a a2 i2 i i1 i3 i4)
   (implies
    (and
     (lr36-function-types-p)
     (lr36-l-index-of-laws-p)
     (lr36-address-p a1)
     (lr36-address-p a)
     (lr36-address-p a2)
     (integerp i2)
     (integerp i)
     (integerp i1)
     (integerp i3)
     (integerp i4))
    (let*
        ((a3 (lr36-t2 a1))
         (a4 (lr36-shift a 0))
         (a5 (lr36-t2 a4))
         (a6 (lr36-t2 (lr36-shift a2 i2)))
         (x (+ i i1))
         (a7 (lr36-shift a2 0)))
      (implies
       (and
        (not (equal a3 (lr36-null-address)))
        (not (equal a5 a3))
        (not (equal a6 (lr36-null-address)))
        (equal a6 a5)
        (<= 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= i1 i3)
        (<= i1 i4)
        (< i2 x)
        (<= i3 x)
        (<= (lr36-region (lr36-address-base a1)) 0)
        (<= (lr36-region (lr36-address-base a2)) 0)
        (<= (lr36-region (lr36-address-base a5)) 0)
        (<= i 2147483645)
        (<= (+ 2 i4) x)
        (lr36-framed-p)
        (lr36-linked-p)
        (lr36-is-sint32-p i)
        (lr36-is-sint32-p i1)
        (lr36-is-sint32-p i3)
        (lr36-valid-rw-p a1 1)
        (lr36-valid-rw-p a7 2147483646)
        (lr36-separated-p a1 1 a7 2147483646)
        (lr36-separated-p a3 4 a7 2147483646)
        (lr36-p-linked-n-p
         a3 a2 i1 i (lr36-null-address))
        (lr36-reflexive-unchanged-p a2 i1 i3)
        (lr36-p-linked-n-p
         a a2 i3 1 a5)
        (lr36-is-sint32-p
         (lr36-l-index-of a6 a2 i1 x))
        (lr36-p-linked-n-p
         a3 a2 i1 (- i3 i1) a)
        (lr36-p-linked-n-p
         a5 a2 (+ 1 i3)
         (- (- (+ i i1) 1) i3)
         (lr36-null-address))
        (lr36-a5-absent-through-i3-p
         a5 a2 i1 i3)
        (lr36-a1-separated-from-range-p
         a1 a2 i1 x)
        (lr36-a5-separated-from-prefix-p
         a5 a2 i1 i3)
        (lr36-range-separated-from-array-p
         a2 i1 x a7)
        (lr36-a6-separated-from-other-range-p
         a6 a2 i1 x)
        (lr36-range-addresses-distinct-p
         a2 i1 x)
        (lr36-range-addresses-separated-p
         a2 i1 x)
        (lr36-havoc-state-p
         (lr36-shift a2 (+ 1 i3))
         (- (- (+ i i1) 2) i3))
        (lr36-t3-range-excludes-a5-p
         a5 a2 i1 (- (+ i i1) 1)))
       (not
        (equal
         (lr36-updated-read
          a4
          (lr36-t2 (lr36-shift a5 0))
          (lr36-shift a2 i4))
         a6)))))))

(value-triple :itpeval-statement-checked)

:q
