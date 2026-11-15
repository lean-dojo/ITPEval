;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_pop_Why3_ide_VClist_pop_more_post_3_part1_goal16:
;; preservation of an indexed linked-list segment after updating the popped
;; list head, under integer bounds, memory validity, framing, and separation
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lpg16-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lpg16-address-base (address)
  (car address))

(defun lpg16-address-offset (address)
  (cdr address))

(defun lpg16-shift (address amount)
  (cons
   (lpg16-address-base address)
   (+ (lpg16-address-offset address) amount)))

(defun lpg16-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_1 and t_2, integer allocation function t, fixed
;; region operation, and the linked proposition specialized to t.

(defstub lpg16-t1 (address) t)
(defstub lpg16-t2 (address) t)
(defstub lpg16-t (index) t)
(defstub lpg16-region (base) t)
(defstub lpg16-linked-op () t)

(defun-sk lpg16-pointer-function-p ()
  (forall (address)
    (implies
     (lpg16-address-p address)
     (and
      (lpg16-address-p (lpg16-t1 address))
      (lpg16-address-p (lpg16-t2 address))))))

(defun-sk lpg16-integer-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lpg16-t index)))))

(defun-sk lpg16-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lpg16-region base)))))

(defun lpg16-linked-p ()
  (if (lpg16-linked-op) t nil))

(defun lpg16-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lpg16-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lpg16-address-base left)
     (lpg16-address-base right)))
   (<=
    (+ (lpg16-address-offset right) right-length)
    (lpg16-address-offset left))
   (<=
    (+ (lpg16-address-offset left) left-length)
    (lpg16-address-offset right))))

(defun lpg16-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lpg16-address-base address))
    (<= 0 (lpg16-address-offset address))
    (<=
     (+ (lpg16-address-offset address) length)
     (lpg16-t (lpg16-address-base address))))))

;; UPDATED-READ is the exact functional update of t_2 at update-address.

(defun lpg16-updated-read
    (update-address update-value address)
  (if (equal address update-address)
      update-value
    (lpg16-t2 address)))

(defun lpg16-pointer-read
    (memory-kind update-address update-value address)
  (if (equal memory-kind :original)
      (lpg16-t1 address)
    (if (equal memory-kind :post)
        (lpg16-t2 address)
      (if (equal memory-kind :updated-post)
          (lpg16-updated-read
           update-address update-value address)
        nil))))

;; This recursion is logically equivalent to the source inductive
;; p_linked_n relation: n = 0 is exactly the bound constructor, while n > 0
;; is exactly the cons constructor followed by its predecessor at n - 1.

(defun lpg16-p-linked-n-p
    (memory-kind update-address update-value
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:original :post :updated-post))
   (lpg16-address-p root)
   (lpg16-address-p array)
   (integerp index)
   (integerp n)
   (lpg16-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lpg16-pointer-read
        memory-kind update-address update-value
        (lpg16-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lpg16-valid-rw-p root 4)
      (lpg16-p-linked-n-p
       memory-kind update-address update-value
       (lpg16-pointer-read
        memory-kind update-address update-value
        (lpg16-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lpg16-framed-p ()
  (forall (address)
    (implies
     (lpg16-address-p address)
     (<=
      (lpg16-region
       (lpg16-address-base (lpg16-t1 address)))
      0))))

(defun-sk lpg16-a-separated-from-range-p
    (a array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lpg16-separated-p
      a 1
      (lpg16-t1 (lpg16-shift array index)) 4))))

(defun-sk lpg16-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lpg16-separated-p
      (lpg16-t1 (lpg16-shift array index)) 4
      array-base 2147483646))))

(defun-sk lpg16-range-addresses-distinct-p
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
       (lpg16-t1 (lpg16-shift array left-index))
       (lpg16-t1 (lpg16-shift array right-index)))))))

(defun-sk lpg16-range-addresses-separated-p
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
     (lpg16-separated-p
      (lpg16-t1 (lpg16-shift array left-index)) 4
      (lpg16-t1 (lpg16-shift array right-index)) 4))))

(defun-sk lpg16-post-a-separated-from-range-p
    (a array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lpg16-separated-p
      a 1
      (lpg16-t2 (lpg16-shift array index)) 4))))

(defun-sk
    ntp4vc-list-pop-more-post-3-part1-goal16-statement ()
  (forall
   (a a1 i i1)
   (implies
    (and
     (lpg16-pointer-function-p)
     (lpg16-integer-function-p)
     (lpg16-region-function-p)
     (lpg16-address-p a)
     (lpg16-address-p a1)
     (integerp i)
     (integerp i1))
    (let*
        ((a2 (lpg16-t1 a))
         (a3 (lpg16-shift a1 0))
         (x (+ i i1))
         (a4 (lpg16-t1 (lpg16-shift a2 0))))
      (implies
       (and
        (not (equal a2 (lpg16-null-address)))
        (< 0 i)
        (<= 0 i1)
        (<= (lpg16-region (lpg16-address-base a)) 0)
        (<= (lpg16-region (lpg16-address-base a1)) 0)
        (lpg16-framed-p)
        (lpg16-linked-p)
        (lpg16-is-sint32-p i)
        (lpg16-is-sint32-p i1)
        (lpg16-valid-rw-p a 1)
        (lpg16-valid-rw-p a3 2147483646)
        (lpg16-separated-p a 1 a3 2147483646)
        (lpg16-separated-p a2 4 a3 2147483646)
        (lpg16-p-linked-n-p
         :original a a4
         a2 a1 i1 i (lpg16-null-address))
        (lpg16-a-separated-from-range-p
         a a1 i1 x)
        (lpg16-range-separated-from-array-p
         a1 i1 x a3)
        (lpg16-range-addresses-distinct-p
         a1 i1 x)
        (lpg16-range-addresses-separated-p
         a1 i1 x)
        (lpg16-p-linked-n-p
         :post a a4
         a4 a1 i1 (- i 1)
         (lpg16-null-address))
        (lpg16-post-a-separated-from-range-p
         a a1 i1 (+ i1 (- i 1))))
       (lpg16-p-linked-n-p
        :updated-post a a4
        a4 a1 i1 (- i 1)
        (lpg16-null-address)))))))

(value-triple :itpeval-statement-checked)

:q
