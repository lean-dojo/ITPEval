;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_assign_part5_goal28:
;; a memory-safety disjunction for removing an indexed linked-list element,
;; under linked-segment, validity, framing, and separation hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lr28-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lr28-address-base (address)
  (car address))

(defun lr28-address-offset (address)
  (cdr address))

(defun lr28-shift (address amount)
  (cons
   (lr28-address-base address)
   (+ (lr28-address-offset address) amount)))

(defun lr28-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_2, allocation function t, real-valued memory t_1,
;; fixed region operation, linked proposition specialized to t, and the
;; imported l_index_of operation specialized to t_2.
;;
;; The values of t_1 occur only in equality tests inside a reflexive
;; p_unchanged premise.  An arbitrary ACL2 codomain therefore preserves all
;; equality observations of the source real-valued function without choosing
;; a smaller numeric domain.

(defstub lr28-t2 (address) t)
(defstub lr28-t (index) t)
(defstub lr28-t1 (address) t)
(defstub lr28-region (base) t)
(defstub lr28-linked-op () t)
(defstub lr28-l-index-of (item array down up) t)

(defun-sk lr28-function-types-p ()
  (forall (address index base item array down up)
    (implies
     (and
      (lr28-address-p address)
      (integerp index)
      (integerp base)
      (lr28-address-p item)
      (lr28-address-p array)
      (integerp down)
      (integerp up))
     (and
      (lr28-address-p (lr28-t2 address))
      (integerp (lr28-t index))
      (integerp (lr28-region base))
      (integerp
       (lr28-l-index-of item array down up))))))

(defun lr28-linked-p ()
  (if (lr28-linked-op) t nil))

(defun lr28-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lr28-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lr28-address-base address))
    (<= 0 (lr28-address-offset address))
    (<=
     (+ (lr28-address-offset address) length)
     (lr28-t (lr28-address-base address))))))

(defun lr28-invalid-p (address length)
  (implies
   (< 0 length)
   (or
    (<=
     (lr28-t (lr28-address-base address))
     (lr28-address-offset address))
    (<=
     (+ (lr28-address-offset address) length)
     0))))

(defun lr28-included-p
    (left left-length right right-length)
  (implies
   (< 0 left-length)
   (and
    (<= 0 right-length)
    (equal
     (lr28-address-base left)
     (lr28-address-base right))
    (<=
     (lr28-address-offset right)
     (lr28-address-offset left))
    (<=
     (+ (lr28-address-offset left) left-length)
     (+ (lr28-address-offset right) right-length)))))

(defun lr28-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lr28-address-base left)
     (lr28-address-base right)))
   (<=
    (+ (lr28-address-offset right) right-length)
    (lr28-address-offset left))
   (<=
    (+ (lr28-address-offset left) left-length)
    (lr28-address-offset right))))

(defun-sk lr28-framed-p ()
  (forall (address)
    (implies
     (lr28-address-p address)
     (<=
      (lr28-region
       (lr28-address-base (lr28-t2 address)))
      0))))

;; These are the three imported source laws for l_index_of: exhaustion of the
;; interval, discovery at the lower endpoint, and the recursive nonmatch step.

(defun-sk lr28-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lr28-address-p item)
      (lr28-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lr28-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lr28-t2 (lr28-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lr28-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lr28-t2 (lr28-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lr28-l-index-of item array (+ 1 down) up)
        (lr28-l-index-of item array down up)))))))

;; This recursion is logically equivalent to the source inductive p_linked_n
;; relation: n = 0 is its bound constructor, and n > 0 is its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lr28-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lr28-address-p root)
   (lr28-address-p array)
   (integerp index)
   (integerp n)
   (lr28-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lr28-t2 (lr28-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lr28-valid-rw-p root 4)
      (lr28-p-linked-n-p
       (lr28-t2 (lr28-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

;; This unfolds the source p_unchanged premise at identical old and new
;; allocation, pointer, and scalar memories.  Each compared load is retained,
;; although the specialization makes the predicate definitionally reflexive.

(defun-sk lr28-reflexive-unchanged-p (array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (lr28-shift array index))
          (left-address (lr28-t2 slot))
          (right-address (lr28-t2 slot)))
       (and
        (equal left-address right-address)
        (equal
         (lr28-t2 (lr28-shift right-address 0))
         (lr28-t2 (lr28-shift left-address 0)))
        (equal
         (lr28-t1 (lr28-shift right-address 1))
         (lr28-t1 (lr28-shift left-address 1)))
        (equal
         (lr28-t1 (lr28-shift right-address 2))
         (lr28-t1 (lr28-shift left-address 2)))
        (equal
         (lr28-t1 (lr28-shift right-address 3))
         (lr28-t1 (lr28-shift left-address 3)))
        (implies
         (lr28-valid-rw-p right-address 4)
         (lr28-valid-rw-p left-address 4)))))))

(defun-sk lr28-a5-absent-through-i2-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (not
      (equal
       (lr28-t2 (lr28-shift array index))
       a5)))))

(defun-sk lr28-a1-separated-from-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr28-separated-p
      a1 1
      (lr28-t2 (lr28-shift array index)) 4))))

(defun-sk lr28-a5-separated-from-prefix-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr28-separated-p
      a5 4
      (lr28-t2 (lr28-shift array index)) 4))))

(defun-sk lr28-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lr28-separated-p
      (lr28-t2 (lr28-shift array index)) 4
      array-base 2147483646))))

(defun-sk lr28-a5-separated-from-other-range-p
    (a5 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (not
       (equal
        (lr28-t2 (lr28-shift array index))
        a5))
      (<= lower index)
      (< index upper))
     (lr28-separated-p
      a5 4
      (lr28-t2 (lr28-shift array index)) 4))))

(defun-sk lr28-range-addresses-distinct-p
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
       (lr28-t2 (lr28-shift array left-index))
       (lr28-t2 (lr28-shift array right-index)))))))

(defun-sk lr28-range-addresses-separated-p
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
     (lr28-separated-p
      (lr28-t2 (lr28-shift array left-index)) 4
      (lr28-t2 (lr28-shift array right-index)) 4))))

(defun-sk
    ntp4vc-list-remove-assign-part5-goal28-statement ()
  (forall
   (a1 a i i1 a2 i2)
   (implies
    (and
     (lr28-function-types-p)
     (lr28-l-index-of-laws-p)
     (lr28-address-p a1)
     (lr28-address-p a)
     (integerp i)
     (integerp i1)
     (lr28-address-p a2)
     (integerp i2))
    (let*
        ((a3 (lr28-t2 a1))
         (a4 (lr28-shift a 0))
         (a5 (lr28-t2 a4))
         (x (+ i i1))
         (a6 (lr28-shift a2 0))
         (x1 (lr28-l-index-of a5 a2 i1 x)))
      (implies
       (and
        (not (equal a3 (lr28-null-address)))
        (not (equal a5 (lr28-null-address)))
        (not (equal a5 a3))
        (<= 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= i2 x)
        (<= (lr28-region (lr28-address-base a1)) 0)
        (<= (lr28-region (lr28-address-base a2)) 0)
        (<= (lr28-region (lr28-address-base a5)) 0)
        (<= i 2147483645)
        (lr28-framed-p)
        (lr28-linked-p)
        (lr28-is-sint32-p i)
        (lr28-is-sint32-p i1)
        (lr28-is-sint32-p i2)
        (lr28-valid-rw-p a1 1)
        (not (lr28-invalid-p a4 1))
        (lr28-valid-rw-p a6 2147483646)
        (lr28-separated-p a1 1 a6 2147483646)
        (lr28-separated-p a3 4 a6 2147483646)
        (lr28-p-linked-n-p
         a3 a2 i1 i (lr28-null-address))
        (lr28-reflexive-unchanged-p a2 i1 i2)
        (lr28-is-sint32-p x1)
        (lr28-p-linked-n-p
         a a2 i2 1 a5)
        (lr28-p-linked-n-p
         a3 a2 i1 (- i2 i1) a)
        (lr28-p-linked-n-p
         a5 a2 (+ 1 i2)
         (- (- (+ i i1) 1) i2)
         (lr28-null-address))
        (lr28-a5-absent-through-i2-p
         a5 a2 i1 i2)
        (lr28-a1-separated-from-range-p
         a1 a2 i1 x)
        (lr28-a5-separated-from-prefix-p
         a5 a2 i1 i2)
        (lr28-range-separated-from-array-p
         a2 i1 x a6)
        (lr28-a5-separated-from-other-range-p
         a5 a2 i1 x)
        (lr28-range-addresses-distinct-p
         a2 i1 x)
        (lr28-range-addresses-separated-p
         a2 i1 x))
       (or
        (equal a4 a1)
        (equal
         (lr28-shift
          (lr28-t2
           (lr28-shift a2 (- x1 1)))
          0)
         a4)
        (lr28-included-p
         a4 1
         (lr28-shift a2 x1)
         (- (+ i i1) x1))))))))

(value-triple :itpeval-statement-checked)

:q
