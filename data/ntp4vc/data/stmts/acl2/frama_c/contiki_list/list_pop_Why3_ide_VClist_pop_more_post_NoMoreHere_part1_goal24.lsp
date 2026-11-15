;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_pop_Why3_ide_VClist_pop_more_post_NoMoreHere_part1_goal24:
;; disequality of the updated pointer-array entry and the popped list head,
;; under linked-list, integer-bound, memory-validity, framing, and separation
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lpg24-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lpg24-address-base (address)
  (car address))

(defun lpg24-address-offset (address)
  (cdr address))

(defun lpg24-shift (address amount)
  (cons
   (lpg24-address-base address)
   (+ (lpg24-address-offset address) amount)))

(defun lpg24-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_1 and t_2, integer allocation function t, fixed region
;; operation, and the linked proposition specialized to t.

(defstub lpg24-t1 (address) t)
(defstub lpg24-t2 (address) t)
(defstub lpg24-t (index) t)
(defstub lpg24-region (base) t)
(defstub lpg24-linked-op () t)

(defun-sk lpg24-pointer-function-p ()
  (forall (address)
    (implies
     (lpg24-address-p address)
     (lpg24-address-p (lpg24-t1 address)))))

(defun-sk lpg24-post-pointer-function-p ()
  (forall (address)
    (implies
     (lpg24-address-p address)
     (lpg24-address-p (lpg24-t2 address)))))

(defun-sk lpg24-integer-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lpg24-t index)))))

(defun-sk lpg24-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lpg24-region base)))))

(defun lpg24-linked-p ()
  (if (lpg24-linked-op) t nil))

(defun lpg24-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lpg24-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lpg24-address-base left)
     (lpg24-address-base right)))
   (<=
    (+ (lpg24-address-offset right) right-length)
    (lpg24-address-offset left))
   (<=
    (+ (lpg24-address-offset left) left-length)
    (lpg24-address-offset right))))

(defun lpg24-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lpg24-address-base address))
    (<= 0 (lpg24-address-offset address))
    (<=
     (+ (lpg24-address-offset address) length)
     (lpg24-t (lpg24-address-base address))))))

;; This recursion is logically equivalent to the source inductive
;; p_linked_n relation: n = 0 is exactly the bound constructor, while n > 0
;; is exactly the cons constructor followed by its predecessor at n - 1.

(defun lpg24-p-linked-n-p
    (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lpg24-address-p root)
   (lpg24-address-p array)
   (integerp index)
   (integerp n)
   (lpg24-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lpg24-t1 (lpg24-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lpg24-valid-rw-p root 4)
      (lpg24-p-linked-n-p
       (lpg24-t1 (lpg24-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lpg24-framed-p ()
  (forall (address)
    (implies
     (lpg24-address-p address)
     (<=
      (lpg24-region
       (lpg24-address-base (lpg24-t1 address)))
      0))))

(defun-sk lpg24-a-separated-from-range-p
    (a array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lpg24-separated-p
      a 1
      (lpg24-t1 (lpg24-shift array index)) 4))))

(defun-sk lpg24-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lpg24-separated-p
      (lpg24-t1 (lpg24-shift array index)) 4
      array-base 2147483646))))

(defun-sk lpg24-range-addresses-distinct-p
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
       (lpg24-t1 (lpg24-shift array left-index))
       (lpg24-t1 (lpg24-shift array right-index)))))))

(defun-sk lpg24-range-addresses-separated-p
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
     (lpg24-separated-p
      (lpg24-t1 (lpg24-shift array left-index)) 4
      (lpg24-t1 (lpg24-shift array right-index)) 4))))

(defun-sk lpg24-root-distinct-from-post-range-p
    (root array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (not
      (equal
       (lpg24-t2 (lpg24-shift array index))
       root)))))

;; UPDATED-READ is the exact functional update of t_2 at update-address.

(defun lpg24-updated-read
    (update-address update-value address)
  (if (equal address update-address)
      update-value
    (lpg24-t2 address)))

(defun-sk
    ntp4vc-list-pop-more-post-nomorehere-part1-goal24-statement ()
  (forall
   (a a1 i i1 i2)
   (implies
    (and
     (lpg24-pointer-function-p)
     (lpg24-post-pointer-function-p)
     (lpg24-integer-function-p)
     (lpg24-region-function-p)
     (lpg24-address-p a)
     (lpg24-address-p a1)
     (integerp i)
     (integerp i1)
     (integerp i2))
    (let*
        ((a2 (lpg24-t1 a))
         (x (+ i i1))
         (a3 (lpg24-shift a1 0)))
      (implies
       (and
        (not (equal a2 (lpg24-null-address)))
        (< 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= (lpg24-region (lpg24-address-base a)) 0)
        (<= (lpg24-region (lpg24-address-base a1)) 0)
        (<= (+ 2 i2) x)
        (lpg24-framed-p)
        (lpg24-linked-p)
        (lpg24-is-sint32-p i)
        (lpg24-is-sint32-p i1)
        (lpg24-valid-rw-p a 1)
        (lpg24-valid-rw-p a3 2147483646)
        (lpg24-separated-p a 1 a3 2147483646)
        (lpg24-separated-p a2 4 a3 2147483646)
        (lpg24-p-linked-n-p
         a2 a1 i1 i (lpg24-null-address))
        (lpg24-a-separated-from-range-p
         a a1 i1 x)
        (lpg24-range-separated-from-array-p
         a1 i1 x a3)
        (lpg24-range-addresses-distinct-p
         a1 i1 x)
        (lpg24-range-addresses-separated-p
         a1 i1 x)
        (lpg24-root-distinct-from-post-range-p
         a2 a1 i1 (- x 1)))
       (not
        (equal
         (lpg24-updated-read
          a
          (lpg24-t1 (lpg24-shift a2 0))
          (lpg24-shift a1 i2))
         a2)))))))

(value-triple :itpeval-statement-checked)

:q
