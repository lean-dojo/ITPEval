;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_Linked_part5_goal32:
;; preservation of an inductively defined linked-list segment after removing
;; an item by a single pointer-memory update, under the stated integer bounds,
;; validity, framing, unchanged-memory, separation, and uniqueness hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lr32-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lr32-address-base (address)
  (car address))

(defun lr32-address-offset (address)
  (cdr address))

(defun lr32-shift (address amount)
  (cons
   (lr32-address-base address)
   (+ (lr32-address-offset address) amount)))

(defun lr32-null-address ()
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

(defstub lr32-t2 (address) t)
(defstub lr32-t3 (address) t)
(defstub lr32-t4 (address) t)
(defstub lr32-t (index) t)
(defstub lr32-t1 (address) t)
(defstub lr32-region (base) t)
(defstub lr32-linked-op () t)
(defstub lr32-l-index-of (item array down up) t)

(defun-sk lr32-function-types-p ()
  (forall (address index base item array down up)
    (implies
     (and
      (lr32-address-p address)
      (integerp index)
      (integerp base)
      (lr32-address-p item)
      (lr32-address-p array)
      (integerp down)
      (integerp up))
     (and
      (lr32-address-p (lr32-t2 address))
      (lr32-address-p (lr32-t3 address))
      (lr32-address-p (lr32-t4 address))
      (integerp (lr32-t index))
      (integerp (lr32-region base))
      (integerp
       (lr32-l-index-of item array down up))))))

(defun lr32-linked-p ()
  (if (lr32-linked-op) t nil))

(defun lr32-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lr32-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lr32-address-base address))
    (<= 0 (lr32-address-offset address))
    (<=
     (+ (lr32-address-offset address) length)
     (lr32-t (lr32-address-base address))))))

(defun lr32-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lr32-address-base left)
     (lr32-address-base right)))
   (<=
    (+ (lr32-address-offset right) right-length)
    (lr32-address-offset left))
   (<=
    (+ (lr32-address-offset left) left-length)
    (lr32-address-offset right))))

(defun-sk lr32-framed-p ()
  (forall (address)
    (implies
     (lr32-address-p address)
     (<=
      (lr32-region
       (lr32-address-base (lr32-t2 address)))
      0))))

;; These are exactly the three imported source laws for l_index_of.

(defun-sk lr32-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lr32-address-p item)
      (lr32-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lr32-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lr32-t2 (lr32-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lr32-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lr32-t2 (lr32-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lr32-l-index-of item array (+ 1 down) up)
        (lr32-l-index-of item array down up)))))))

;; POINTER-READ selects t_2, the source havoc result t_3, or the exact
;; functional update of t_3 used by the conclusion.

(defun lr32-pointer-read
    (memory-kind update-address update-value address)
  (cond
   ((equal memory-kind :t2)
    (lr32-t2 address))
   ((equal memory-kind :t3)
    (lr32-t3 address))
   ((equal memory-kind :updated-t3)
    (if (equal address update-address)
        update-value
      (lr32-t3 address)))
   (t nil)))

;; This recursion is logically equivalent to the source inductive p_linked_n
;; relation: n = 0 is its bound constructor, and n > 0 is its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lr32-p-linked-n-p
    (memory-kind update-address update-value
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:t2 :t3 :updated-t3))
   (lr32-address-p root)
   (lr32-address-p array)
   (integerp index)
   (integerp n)
   (lr32-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lr32-pointer-read
        memory-kind update-address update-value
        (lr32-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lr32-valid-rw-p root 4)
      (lr32-p-linked-n-p
       memory-kind update-address update-value
       (lr32-pointer-read
        memory-kind update-address update-value
        (lr32-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

;; This unfolds the source p_unchanged premise at identical old and new
;; allocation, pointer, and scalar memories.

(defun-sk lr32-reflexive-unchanged-p (array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lr32-shift array index))
          (left-address (lr32-t2 slot))
          (right-address (lr32-t2 slot)))
       (and
        (equal left-address right-address)
        (equal
         (lr32-t2 (lr32-shift right-address 0))
         (lr32-t2 (lr32-shift left-address 0)))
        (equal
         (lr32-t1 (lr32-shift right-address 1))
         (lr32-t1 (lr32-shift left-address 1)))
        (equal
         (lr32-t1 (lr32-shift right-address 2))
         (lr32-t1 (lr32-shift left-address 2)))
        (equal
         (lr32-t1 (lr32-shift right-address 3))
         (lr32-t1 (lr32-shift left-address 3)))
        (implies
         (lr32-valid-rw-p right-address 4)
         (lr32-valid-rw-p left-address 4)))))))

(defun-sk lr32-a5-absent-through-i3-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (not
      (equal
       (lr32-t2 (lr32-shift array index))
       a5)))))

(defun-sk lr32-a1-separated-from-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr32-separated-p
      a1 1
      (lr32-t2 (lr32-shift array index)) 4))))

(defun-sk lr32-a5-separated-from-prefix-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr32-separated-p
      a5 4
      (lr32-t2 (lr32-shift array index)) 4))))

(defun-sk lr32-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr32-separated-p
      (lr32-t2 (lr32-shift array index)) 4
      array-base 2147483646))))

(defun-sk lr32-a6-separated-from-other-range-p
    (a6 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        a6
        (lr32-t2 (lr32-shift array index))))
      (<= lower index)
      (< index upper))
     (lr32-separated-p
      a6 4
      (lr32-t2 (lr32-shift array index)) 4))))

(defun-sk lr32-range-addresses-distinct-p
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
       (lr32-t2 (lr32-shift array left-index))
       (lr32-t2 (lr32-shift array right-index)))))))

(defun-sk lr32-range-addresses-separated-p
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
     (lr32-separated-p
      (lr32-t2 (lr32-shift array left-index)) 4
      (lr32-t2 (lr32-shift array right-index)) 4))))

;; Memory.havoc old outside start size keeps OUTSIDE outside the byte range
;; and OLD inside it. The source equality
;;   havoc t_4 t_2 (shift a_2 (1 + i_3)) (i + i_1 - 2 - i_3) = t_3
;; is therefore this pointwise equation.

(defun-sk lr32-havoc-state-p (start length)
  (forall (address)
    (implies
     (lr32-address-p address)
     (equal
      (lr32-t3 address)
      (if (lr32-separated-p address 1 start length)
          (lr32-t2 address)
        (lr32-t4 address))))))

(defun-sk lr32-t3-range-addresses-distinct-p
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
       (lr32-t3 (lr32-shift array left-index))
       (lr32-t3 (lr32-shift array right-index)))))))

(defun-sk
    ntp4vc-list-remove-contains-item-linked-part5-goal32-statement ()
  (forall
   (a1 a a2 i2 i i1 i3)
   (implies
    (and
     (lr32-function-types-p)
     (lr32-l-index-of-laws-p)
     (lr32-address-p a1)
     (lr32-address-p a)
     (lr32-address-p a2)
     (integerp i2)
     (integerp i)
     (integerp i1)
     (integerp i3))
    (let*
        ((a3 (lr32-t2 a1))
         (a4 (lr32-shift a 0))
         (a5 (lr32-t2 a4))
         (a6 (lr32-t2 (lr32-shift a2 i2)))
         (x (+ i i1))
         (a7 (lr32-shift a2 0))
         (update-value (lr32-t2 (lr32-shift a5 0))))
      (implies
       (and
        (not (equal a3 (lr32-null-address)))
        (not (equal a5 a3))
        (not (equal a6 (lr32-null-address)))
        (equal a6 a5)
        (<= 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= i1 i3)
        (< i2 x)
        (<= i3 x)
        (<= (lr32-region (lr32-address-base a1)) 0)
        (<= (lr32-region (lr32-address-base a2)) 0)
        (<= (lr32-region (lr32-address-base a5)) 0)
        (<= i 2147483645)
        (lr32-framed-p)
        (lr32-linked-p)
        (lr32-is-sint32-p i)
        (lr32-is-sint32-p i1)
        (lr32-is-sint32-p i3)
        (lr32-valid-rw-p a1 1)
        (lr32-valid-rw-p a7 2147483646)
        (lr32-separated-p a1 1 a7 2147483646)
        (lr32-separated-p a3 4 a7 2147483646)
        (lr32-p-linked-n-p
         :t2 nil nil
         a3 a2 i1 i (lr32-null-address))
        (lr32-reflexive-unchanged-p a2 i1 i3)
        (lr32-p-linked-n-p
         :t2 nil nil
         a a2 i3 1 a5)
        (lr32-is-sint32-p
        (lr32-l-index-of a6 a2 i1 x))
        (lr32-p-linked-n-p
         :t2 nil nil
         a3 a2 i1 (- i3 i1) a)
        (lr32-p-linked-n-p
         :t2 nil nil
         a5 a2 (+ 1 i3)
         (- (- (+ i i1) 1) i3)
         (lr32-null-address))
        (lr32-a5-absent-through-i3-p
         a5 a2 i1 i3)
        (lr32-a1-separated-from-range-p
         a1 a2 i1 x)
        (lr32-a5-separated-from-prefix-p
         a5 a2 i1 i3)
        (lr32-range-separated-from-array-p
         a2 i1 x a7)
        (lr32-a6-separated-from-other-range-p
         a6 a2 i1 x)
        (lr32-range-addresses-distinct-p
         a2 i1 x)
        (lr32-range-addresses-separated-p
         a2 i1 x)
        (lr32-havoc-state-p
         (lr32-shift a2 (+ 1 i3))
         (- (- (+ i i1) 2) i3))
        (lr32-p-linked-n-p
         :t3 nil nil
         (lr32-t2 (lr32-shift a2 i1))
         a2 i1 (- (+ 1 i3) i1) a5)
        (lr32-p-linked-n-p
         :t3 nil nil
         (lr32-t2 (lr32-shift a5 0))
         a2 (+ 1 i3)
         (- (- (+ i i1) 2) i3)
         (lr32-null-address))
        (lr32-t3-range-addresses-distinct-p
         a2 i1 (- (+ i i1) 1)))
       (lr32-p-linked-n-p
        :updated-t3 a4 update-value
        (lr32-pointer-read
         :updated-t3 a4 update-value a1)
        a2 i1 (- i 1) (lr32-null-address)))))))

(value-triple :itpeval-statement-checked)

:q
