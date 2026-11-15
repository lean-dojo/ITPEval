;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_loop_inv_2_preserved_goal8:
;; preservation of an inductively defined linked-list segment loop invariant
;; under pointer-memory, allocation, framing, separation, and uniqueness
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lrg8-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lrg8-address-base (address)
  (car address))

(defun lrg8-address-offset (address)
  (cdr address))

(defun lrg8-shift (address amount)
  (cons
   (lrg8-address-base address)
   (+ (lrg8-address-offset address) amount)))

(defun lrg8-null-address ()
  (cons 0 0))

;; These conservative symbols represent the source pointer memory t_2,
;; allocation function t, real-valued memory t_1, region operation, linked
;; proposition specialized to t, and imported l_index_of operation.

(defstub lrg8-t2 (address) t)
(defstub lrg8-t (index) t)
(defstub lrg8-t1 (address) t)
(defstub lrg8-region (base) t)
(defstub lrg8-linked-op () t)
(defstub lrg8-l-index-of (item array down up) t)

(defun-sk lrg8-pointer-function-p ()
  (forall (address)
    (implies
     (lrg8-address-p address)
     (lrg8-address-p (lrg8-t2 address)))))

(defun-sk lrg8-integer-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lrg8-t index)))))

(defun-sk lrg8-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lrg8-region base)))))

(defun-sk lrg8-l-index-of-type-p ()
  (forall (item array down up)
    (implies
     (and
      (lrg8-address-p item)
      (lrg8-address-p array)
      (integerp down)
      (integerp up))
     (integerp
      (lrg8-l-index-of item array down up)))))

(defun lrg8-linked-p ()
  (if (lrg8-linked-op) t nil))

(defun lrg8-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lrg8-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lrg8-address-base address))
    (<= 0 (lrg8-address-offset address))
    (<=
     (+ (lrg8-address-offset address) length)
     (lrg8-t (lrg8-address-base address))))))

(defun lrg8-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lrg8-address-base left)
     (lrg8-address-base right)))
   (<=
    (+ (lrg8-address-offset right) right-length)
    (lrg8-address-offset left))
   (<=
    (+ (lrg8-address-offset left) left-length)
    (lrg8-address-offset right))))

(defun-sk lrg8-framed-p ()
  (forall (address)
    (implies
     (lrg8-address-p address)
     (<=
      (lrg8-region
       (lrg8-address-base (lrg8-t2 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lrg8-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lrg8-address-p item)
      (lrg8-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lrg8-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lrg8-t2 (lrg8-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lrg8-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lrg8-t2 (lrg8-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lrg8-l-index-of item array (+ 1 down) up)
        (lrg8-l-index-of item array down up)))))))

;; This recursion is logically equivalent to the source inductive p_linked_n
;; relation: n = 0 is exactly its bound constructor, while n > 0 is exactly
;; its cons constructor followed by the unique predecessor at n - 1.

(defun lrg8-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lrg8-address-p root)
   (lrg8-address-p array)
   (integerp index)
   (integerp n)
   (lrg8-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lrg8-t2 (lrg8-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lrg8-valid-rw-p root 4)
      (lrg8-p-linked-n-p
       (lrg8-t2 (lrg8-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

;; The source p_unchanged premise compares t, t_2, and t_1 with themselves.
;; The list payload values therefore occur only in reflexive equalities; using
;; arbitrary ACL2 values for t_1 is a definitional extension, not a restriction
;; of the source real-valued memory.

(defun lrg8-load-s1-list (address)
  (list
   (lrg8-t2 (lrg8-shift address 0))
   (lrg8-t1 (lrg8-shift address 1))
   (lrg8-t1 (lrg8-shift address 2))
   (lrg8-t1 (lrg8-shift address 3))))

(defun-sk lrg8-p-unchanged-self-p (array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (let*
         ((address (lrg8-shift array index))
          (old-node (lrg8-t2 address))
          (new-node (lrg8-t2 address)))
       (and
        (equal old-node new-node)
        (equal
         (lrg8-load-s1-list new-node)
         (lrg8-load-s1-list old-node))
        (implies
         (lrg8-valid-rw-p new-node 4)
         (lrg8-valid-rw-p old-node 4)))))))

(defun-sk lrg8-item-absent-through-p
    (item array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (not
      (equal
       (lrg8-t2 (lrg8-shift array index))
       item)))))

(defun-sk lrg8-address-separated-from-range-p
    (address address-length array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lrg8-separated-p
      address address-length
      (lrg8-t2 (lrg8-shift array index)) 4))))

(defun-sk lrg8-item-separated-from-range-p
    (item array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lrg8-separated-p
      item 4
      (lrg8-t2 (lrg8-shift array index)) 4))))

(defun-sk lrg8-range-separated-from-address-p
    (array lower upper address address-length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lrg8-separated-p
      (lrg8-t2 (lrg8-shift array index)) 4
      address address-length))))

(defun-sk lrg8-item-separated-when-distinct-p
    (item array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        (lrg8-t2 (lrg8-shift array index))
        item))
      (<= lower index)
      (< index upper))
     (lrg8-separated-p
      item 4
      (lrg8-t2 (lrg8-shift array index)) 4))))

(defun-sk lrg8-range-addresses-distinct-p
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
       (lrg8-t2 (lrg8-shift array left-index))
       (lrg8-t2 (lrg8-shift array right-index)))))))

(defun-sk lrg8-range-addresses-separated-p
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
     (lrg8-separated-p
      (lrg8-t2 (lrg8-shift array left-index)) 4
      (lrg8-t2 (lrg8-shift array right-index)) 4))))

(defun-sk
    ntp4vc-list-remove-loop-inv-2-preserved-goal8-statement ()
  (forall
   (a1 a i i1 i2 a3 a2)
   (implies
    (and
     (lrg8-pointer-function-p)
     (lrg8-integer-function-p)
     (lrg8-region-function-p)
     (lrg8-l-index-of-type-p)
     (lrg8-l-index-of-laws-p)
     (lrg8-address-p a1)
     (lrg8-address-p a)
     (integerp i)
     (integerp i1)
     (integerp i2)
     (lrg8-address-p a3)
     (lrg8-address-p a2))
    (let*
        ((a4 (lrg8-t2 a1))
         (a5 (lrg8-t2 (lrg8-shift a 0)))
         (x (+ i i1))
         (x1 (+ 1 i2))
         (a6 (lrg8-shift a3 0)))
      (implies
       (and
        (not (equal (lrg8-null-address) a2))
        (not (equal a4 a2))
        (not (equal a4 (lrg8-null-address)))
        (not (equal a5 a2))
        (not (equal a5 (lrg8-null-address)))
        (<= 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= i2 x)
        (<= (lrg8-region (lrg8-address-base a1)) 0)
        (<= (lrg8-region (lrg8-address-base a2)) 0)
        (<= (lrg8-region (lrg8-address-base a3)) 0)
        (<= i 2147483645)
        (lrg8-framed-p)
        (lrg8-linked-p)
        (lrg8-is-sint32-p i)
        (lrg8-is-sint32-p i1)
        (lrg8-is-sint32-p i2)
        (lrg8-valid-rw-p a1 1)
        (lrg8-is-sint32-p x1)
        (lrg8-valid-rw-p a6 2147483646)
        (lrg8-separated-p a1 1 a6 2147483646)
        (lrg8-separated-p a4 4 a6 2147483646)
        (lrg8-p-linked-n-p
         a4 a3 i1 i (lrg8-null-address))
        (lrg8-p-unchanged-self-p a3 i1 i2)
        (lrg8-is-sint32-p
         (lrg8-l-index-of a2 a3 i1 x))
        (lrg8-p-linked-n-p
         a a3 i2 1 a5)
        (lrg8-p-linked-n-p
         a4 a3 i1 (- i2 i1) a)
        (lrg8-p-linked-n-p
         a5 a3 x1 (- (- (+ i i1) 1) i2)
         (lrg8-null-address))
        (lrg8-item-absent-through-p
         a2 a3 i1 i2)
        (lrg8-address-separated-from-range-p
         a1 1 a3 i1 x)
        (lrg8-item-separated-from-range-p
         a2 a3 i1 i2)
        (lrg8-range-separated-from-address-p
         a3 i1 x a6 2147483646)
        (lrg8-item-separated-when-distinct-p
         a2 a3 i1 x)
        (lrg8-range-addresses-distinct-p
         a3 i1 x)
        (lrg8-range-addresses-separated-p
         a3 i1 x))
       (lrg8-p-linked-n-p
        a4 a3 i1 (- (+ 1 i2) i1) a5))))))

(value-triple :itpeval-statement-checked)

:q
