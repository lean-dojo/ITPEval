;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_Linked_part2_goal30:
;; preservation of an inductively defined linked-list segment after removing
;; an item by a single pointer-memory update, under the stated integer bounds,
;; validity, framing, separation, and uniqueness hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lr30-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lr30-address-base (address)
  (car address))

(defun lr30-address-offset (address)
  (cdr address))

(defun lr30-shift (address amount)
  (cons
   (lr30-address-base address)
   (+ (lr30-address-offset address) amount)))

(defun lr30-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_1 and t_2, allocation function t, fixed region operation,
;; linked proposition specialized to t, and imported l_index_of operation
;; specialized to t_1.

(defstub lr30-t1 (address) t)
(defstub lr30-t2 (address) t)
(defstub lr30-t (index) t)
(defstub lr30-region (base) t)
(defstub lr30-linked-op () t)
(defstub lr30-l-index-of (item array down up) t)

(defun-sk lr30-pointer-function-p ()
  (forall (address)
    (implies
     (lr30-address-p address)
     (and
      (lr30-address-p (lr30-t1 address))
      (lr30-address-p (lr30-t2 address))))))

(defun-sk lr30-integer-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lr30-t index)))))

(defun-sk lr30-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lr30-region base)))))

(defun-sk lr30-l-index-of-type-p ()
  (forall (item array down up)
    (implies
     (and
      (lr30-address-p item)
      (lr30-address-p array)
      (integerp down)
      (integerp up))
     (integerp
      (lr30-l-index-of item array down up)))))

(defun lr30-linked-p ()
  (if (lr30-linked-op) t nil))

(defun lr30-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lr30-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lr30-address-base address))
    (<= 0 (lr30-address-offset address))
    (<=
     (+ (lr30-address-offset address) length)
     (lr30-t (lr30-address-base address))))))

(defun lr30-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lr30-address-base left)
     (lr30-address-base right)))
   (<=
    (+ (lr30-address-offset right) right-length)
    (lr30-address-offset left))
   (<=
    (+ (lr30-address-offset left) left-length)
    (lr30-address-offset right))))

(defun-sk lr30-framed-p ()
  (forall (address)
    (implies
     (lr30-address-p address)
     (<=
      (lr30-region
       (lr30-address-base (lr30-t1 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lr30-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lr30-address-p item)
      (lr30-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lr30-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lr30-t1 (lr30-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lr30-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lr30-t1 (lr30-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lr30-l-index-of item array (+ 1 down) up)
        (lr30-l-index-of item array down up)))))))

;; POINTER-READ selects t_1, the independent source map t_2, or the exact
;; functional update of t_2 at one address.

(defun lr30-pointer-read
    (memory-kind update-address update-value address)
  (cond
   ((equal memory-kind :t2)
    (lr30-t2 address))
   ((equal memory-kind :updated-t2)
    (if (equal address update-address)
        update-value
      (lr30-t2 address)))
   (t
    (lr30-t1 address))))

;; This recursion is logically equivalent to the source inductive
;; p_linked_n relation: n = 0 is exactly the bound constructor, while n > 0
;; is exactly the cons constructor followed by its predecessor at n - 1.

(defun lr30-p-linked-n-p
    (memory-kind update-address update-value
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:t1 :t2 :updated-t2))
   (lr30-address-p root)
   (lr30-address-p array)
   (integerp index)
   (integerp n)
   (lr30-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lr30-pointer-read
        memory-kind update-address update-value
        (lr30-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lr30-valid-rw-p root 4)
      (lr30-p-linked-n-p
       memory-kind update-address update-value
       (lr30-pointer-read
        memory-kind update-address update-value
        (lr30-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lr30-a-separated-from-range-p
    (a array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr30-separated-p
      a 1
      (lr30-t1 (lr30-shift array index)) 4))))

(defun-sk lr30-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr30-separated-p
      (lr30-t1 (lr30-shift array index)) 4
      array-base 2147483646))))

(defun-sk lr30-item-separated-from-other-range-p
    (item array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        item
        (lr30-t1 (lr30-shift array index))))
      (<= lower index)
      (< index upper))
     (lr30-separated-p
      item 4
      (lr30-t1 (lr30-shift array index)) 4))))

(defun-sk lr30-range-addresses-distinct-p
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
       (lr30-t1 (lr30-shift array left-index))
       (lr30-t1 (lr30-shift array right-index)))))))

(defun-sk lr30-range-addresses-separated-p
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
     (lr30-separated-p
      (lr30-t1 (lr30-shift array left-index)) 4
      (lr30-t1 (lr30-shift array right-index)) 4))))

(defun-sk lr30-a-separated-from-t2-range-p
    (a array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr30-separated-p
      a 1
      (lr30-t2 (lr30-shift array index)) 4))))

(defun-sk
    ntp4vc-list-remove-contains-item-linked-part2-goal30-statement ()
  (forall
   (a a1 i2 i i1)
   (implies
    (and
     (lr30-pointer-function-p)
     (lr30-integer-function-p)
     (lr30-region-function-p)
     (lr30-l-index-of-type-p)
     (lr30-l-index-of-laws-p)
     (lr30-address-p a)
     (lr30-address-p a1)
     (integerp i2)
     (integerp i)
     (integerp i1))
    (let*
        ((a2 (lr30-t1 a))
         (a3 (lr30-t1 (lr30-shift a1 i2)))
         (x (+ i i1))
         (a4 (lr30-shift a1 0))
         (a5 (lr30-t1 (lr30-shift a2 0))))
      (implies
       (and
        (not (equal a2 (lr30-null-address)))
        (not (equal a3 (lr30-null-address)))
        (equal a3 a2)
        (<= 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (< i2 x)
        (<= (lr30-region (lr30-address-base a)) 0)
        (<= (lr30-region (lr30-address-base a1)) 0)
        (<= (lr30-region (lr30-address-base a2)) 0)
        (<= i 2147483645)
        (lr30-framed-p)
        (lr30-linked-p)
        (lr30-is-sint32-p i)
        (lr30-is-sint32-p i1)
        (lr30-valid-rw-p a 1)
        (lr30-valid-rw-p a4 2147483646)
        (lr30-separated-p a 1 a4 2147483646)
        (lr30-separated-p a2 4 a4 2147483646)
        (lr30-p-linked-n-p
         :t1 nil nil
         a2 a1 i1 i (lr30-null-address))
        (lr30-is-sint32-p
         (lr30-l-index-of a3 a1 i1 x))
        (lr30-a-separated-from-range-p
         a a1 i1 x)
        (lr30-range-separated-from-array-p
         a1 i1 x a4)
        (lr30-item-separated-from-other-range-p
         a3 a1 i1 x)
        (lr30-range-addresses-distinct-p
         a1 i1 x)
        (lr30-range-addresses-separated-p
         a1 i1 x)
        (lr30-p-linked-n-p
         :t2 nil nil
         a5 a1 i1 (- i 1) (lr30-null-address))
        (lr30-a-separated-from-t2-range-p
         a a1 i1 (- x 1)))
       (lr30-p-linked-n-p
        :updated-t2 a a5
        a5 a1 i1 (- i 1) (lr30-null-address)))))))

(value-triple :itpeval-statement-checked)

:q
