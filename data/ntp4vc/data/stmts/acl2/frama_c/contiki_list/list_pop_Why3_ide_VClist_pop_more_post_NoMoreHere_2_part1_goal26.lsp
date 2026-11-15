;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_pop_Why3_ide_VClist_pop_more_post_NoMoreHere_2_part1_goal26:
;; separation of an updated pointer-array entry from the popped list head,
;; under linked-list, integer-bound, memory-validity, framing, and separation
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lpg26-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lpg26-address-base (address)
  (car address))

(defun lpg26-address-offset (address)
  (cdr address))

(defun lpg26-shift (address amount)
  (cons
   (lpg26-address-base address)
   (+ (lpg26-address-offset address) amount)))

(defun lpg26-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_1 and t_2, integer allocation function t, fixed region
;; operation, and the linked proposition specialized to t.

(defstub lpg26-t1 (address) t)
(defstub lpg26-t2 (address) t)
(defstub lpg26-t (index) t)
(defstub lpg26-region (base) t)
(defstub lpg26-linked-op () t)

(defun-sk lpg26-pointer-function-p ()
  (forall (address)
    (implies
     (lpg26-address-p address)
     (lpg26-address-p (lpg26-t1 address)))))

(defun-sk lpg26-post-pointer-function-p ()
  (forall (address)
    (implies
     (lpg26-address-p address)
     (lpg26-address-p (lpg26-t2 address)))))

(defun-sk lpg26-integer-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lpg26-t index)))))

(defun-sk lpg26-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lpg26-region base)))))

(defun lpg26-linked-p ()
  (if (lpg26-linked-op) t nil))

(defun lpg26-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lpg26-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lpg26-address-base left)
     (lpg26-address-base right)))
   (<=
    (+ (lpg26-address-offset right) right-length)
    (lpg26-address-offset left))
   (<=
    (+ (lpg26-address-offset left) left-length)
    (lpg26-address-offset right))))

(defun lpg26-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lpg26-address-base address))
    (<= 0 (lpg26-address-offset address))
    (<=
     (+ (lpg26-address-offset address) length)
     (lpg26-t (lpg26-address-base address))))))

;; This recursion is logically equivalent to the source inductive
;; p_linked_n relation: n = 0 is exactly the bound constructor, while n > 0
;; is exactly the cons constructor followed by its predecessor at n - 1.

(defun lpg26-p-linked-n-p
    (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lpg26-address-p root)
   (lpg26-address-p array)
   (integerp index)
   (integerp n)
   (lpg26-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lpg26-t1 (lpg26-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lpg26-valid-rw-p root 4)
      (lpg26-p-linked-n-p
       (lpg26-t1 (lpg26-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lpg26-framed-p ()
  (forall (address)
    (implies
     (lpg26-address-p address)
     (<=
      (lpg26-region
       (lpg26-address-base (lpg26-t1 address)))
      0))))

(defun-sk lpg26-a-separated-from-range-p
    (a array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lpg26-separated-p
      a 1
      (lpg26-t1 (lpg26-shift array index)) 4))))

(defun-sk lpg26-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lpg26-separated-p
      (lpg26-t1 (lpg26-shift array index)) 4
      array-base 2147483646))))

(defun-sk lpg26-range-addresses-distinct-p
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
       (lpg26-t1 (lpg26-shift array left-index))
       (lpg26-t1 (lpg26-shift array right-index)))))))

(defun-sk lpg26-range-addresses-separated-p
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
     (lpg26-separated-p
      (lpg26-t1 (lpg26-shift array left-index)) 4
      (lpg26-t1 (lpg26-shift array right-index)) 4))))

(defun-sk lpg26-root-separated-from-post-range-p
    (root array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lpg26-separated-p
      root 4
      (lpg26-t2 (lpg26-shift array index)) 4))))

;; UPDATED-READ is the exact functional update of t_2 at update-address.

(defun lpg26-updated-read
    (update-address update-value address)
  (if (equal address update-address)
      update-value
    (lpg26-t2 address)))

(defun-sk
    ntp4vc-list-pop-more-post-nomorehere-2-part1-goal26-statement ()
  (forall
   (a a1 i i1 i2)
   (implies
    (and
     (lpg26-pointer-function-p)
     (lpg26-post-pointer-function-p)
     (lpg26-integer-function-p)
     (lpg26-region-function-p)
     (lpg26-address-p a)
     (lpg26-address-p a1)
     (integerp i)
     (integerp i1)
     (integerp i2))
    (let*
        ((a2 (lpg26-t1 a))
         (x (+ i i1))
         (a3 (lpg26-shift a1 0)))
      (implies
       (and
        (not (equal a2 (lpg26-null-address)))
        (< 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= (lpg26-region (lpg26-address-base a)) 0)
        (<= (lpg26-region (lpg26-address-base a1)) 0)
        (<= (+ 2 i2) x)
        (lpg26-framed-p)
        (lpg26-linked-p)
        (lpg26-is-sint32-p i)
        (lpg26-is-sint32-p i1)
        (lpg26-valid-rw-p a 1)
        (lpg26-valid-rw-p a3 2147483646)
        (lpg26-separated-p a 1 a3 2147483646)
        (lpg26-separated-p a2 4 a3 2147483646)
        (lpg26-p-linked-n-p
         a2 a1 i1 i (lpg26-null-address))
        (lpg26-a-separated-from-range-p
         a a1 i1 x)
        (lpg26-range-separated-from-array-p
         a1 i1 x a3)
        (lpg26-range-addresses-distinct-p
         a1 i1 x)
        (lpg26-range-addresses-separated-p
         a1 i1 x)
        (lpg26-root-separated-from-post-range-p
         a2 a1 i1 (- x 1)))
       (lpg26-separated-p
        (lpg26-updated-read
         a
         (lpg26-t1 (lpg26-shift a2 0))
         (lpg26-shift a1 i2))
        4
        a2
        4))))))

(value-triple :itpeval-statement-checked)

:q
