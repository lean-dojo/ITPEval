;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_pop_Why3_ide_VClist_pop_more_post_2_part1_goal14:
;; preservation of the pointer-array left-swipe relation after updating the
;; popped list head, under linked-list, validity, framing, and separation
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lpg14-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lpg14-address-base (address)
  (car address))

(defun lpg14-address-offset (address)
  (cdr address))

(defun lpg14-shift (address amount)
  (cons
   (lpg14-address-base address)
   (+ (lpg14-address-offset address) amount)))

(defun lpg14-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_1 and t_2, integer allocation function t, fixed region
;; operation, and the linked proposition specialized to t.

(defstub lpg14-t1 (address) t)
(defstub lpg14-t2 (address) t)
(defstub lpg14-t (index) t)
(defstub lpg14-region (base) t)
(defstub lpg14-linked-op () t)

(defun-sk lpg14-pointer-function-p ()
  (forall (address)
    (implies
     (lpg14-address-p address)
     (and
      (lpg14-address-p (lpg14-t1 address))
      (lpg14-address-p (lpg14-t2 address))))))

(defun-sk lpg14-integer-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lpg14-t index)))))

(defun-sk lpg14-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lpg14-region base)))))

(defun lpg14-linked-p ()
  (if (lpg14-linked-op) t nil))

(defun lpg14-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lpg14-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lpg14-address-base left)
     (lpg14-address-base right)))
   (<=
    (+ (lpg14-address-offset right) right-length)
    (lpg14-address-offset left))
   (<=
    (+ (lpg14-address-offset left) left-length)
    (lpg14-address-offset right))))

(defun lpg14-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lpg14-address-base address))
    (<= 0 (lpg14-address-offset address))
    (<=
     (+ (lpg14-address-offset address) length)
     (lpg14-t (lpg14-address-base address))))))

;; This recursion is logically equivalent to the source inductive
;; p_linked_n relation: n = 0 is exactly the bound constructor, while n > 0
;; is exactly the cons constructor followed by its predecessor at n - 1.

(defun lpg14-p-linked-n-p
    (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lpg14-address-p root)
   (lpg14-address-p array)
   (integerp index)
   (integerp n)
   (lpg14-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lpg14-t1 (lpg14-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lpg14-valid-rw-p root 4)
      (lpg14-p-linked-n-p
       (lpg14-t1 (lpg14-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lpg14-framed-p ()
  (forall (address)
    (implies
     (lpg14-address-p address)
     (<=
      (lpg14-region
       (lpg14-address-base (lpg14-t1 address)))
      0))))

(defun-sk lpg14-a-separated-from-range-p
    (a array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lpg14-separated-p
      a 1
      (lpg14-t1 (lpg14-shift array index)) 4))))

(defun-sk lpg14-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lpg14-separated-p
      (lpg14-t1 (lpg14-shift array index)) 4
      array-base 2147483646))))

(defun-sk lpg14-range-addresses-distinct-p
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
       (lpg14-t1 (lpg14-shift array left-index))
       (lpg14-t1 (lpg14-shift array right-index)))))))

(defun-sk lpg14-range-addresses-separated-p
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
     (lpg14-separated-p
      (lpg14-t1 (lpg14-shift array left-index)) 4
      (lpg14-t1 (lpg14-shift array right-index)) 4))))

;; UPDATED-READ is the exact functional update of t_2 at update-address.

(defun lpg14-updated-read
    (update-address update-value address)
  (if (equal address update-address)
      update-value
    (lpg14-t2 address)))

(defun-sk lpg14-array-swipe-left-before-p
    (array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lpg14-t1 (lpg14-shift array (+ 1 index)))
      (lpg14-t2 (lpg14-shift array index))))))

(defun-sk lpg14-array-swipe-left-after-update-p
    (array down up update-address update-value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (lpg14-t1 (lpg14-shift array (+ 1 index)))
      (lpg14-updated-read
       update-address update-value
       (lpg14-shift array index))))))

(defun-sk
    ntp4vc-list-pop-more-post-2-part1-goal14-statement ()
  (forall
   (a a1 i i1)
   (implies
    (and
     (lpg14-pointer-function-p)
     (lpg14-integer-function-p)
     (lpg14-region-function-p)
     (lpg14-address-p a)
     (lpg14-address-p a1)
     (integerp i)
     (integerp i1))
    (let*
        ((a2 (lpg14-t1 a))
         (a3 (lpg14-shift a1 0))
         (x (+ i i1)))
      (implies
       (and
        (not (equal a2 (lpg14-null-address)))
        (< 0 i)
        (<= 0 i1)
        (<= (lpg14-region (lpg14-address-base a)) 0)
        (<= (lpg14-region (lpg14-address-base a1)) 0)
        (lpg14-framed-p)
        (lpg14-linked-p)
        (lpg14-is-sint32-p i)
        (lpg14-is-sint32-p i1)
        (lpg14-valid-rw-p a 1)
        (lpg14-valid-rw-p a3 2147483646)
        (lpg14-separated-p a 1 a3 2147483646)
        (lpg14-separated-p a2 4 a3 2147483646)
        (lpg14-p-linked-n-p
         a2 a1 i1 i (lpg14-null-address))
        (lpg14-a-separated-from-range-p
         a a1 i1 x)
        (lpg14-range-separated-from-array-p
         a1 i1 x a3)
        (lpg14-range-addresses-distinct-p
         a1 i1 x)
        (lpg14-range-addresses-separated-p
         a1 i1 x)
        (lpg14-array-swipe-left-before-p
         a1 i1 (- (+ i i1) 1)))
       (lpg14-array-swipe-left-after-update-p
        a1 i1 (- (+ i i1) 1)
        a
        (lpg14-t1 (lpg14-shift a2 0))))))))

(value-triple :itpeval-statement-checked)

:q
