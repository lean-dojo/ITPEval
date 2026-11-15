;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_chop_Why3_ide_VClist_chop_more_post_3_part3_goal54:
;; preservation of an indexed linked-list segment after updating one pointer,
;; under integer bounds, memory validity, framing, and separation hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lcm54-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lcm54-address-base (address)
  (car address))

(defun lcm54-address-offset (address)
  (cdr address))

(defun lcm54-shift (address amount)
  (cons
   (lcm54-address-base address)
   (+ (lcm54-address-offset address) amount)))

(defun lcm54-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer allocation function t, fixed region
;; operation, and the linked proposition specialized to t.

(defstub lcm54-t1 (address) t)
(defstub lcm54-t (index) t)
(defstub lcm54-region (base) t)
(defstub lcm54-linked-op () t)

(defun-sk lcm54-pointer-function-p ()
  (forall (address)
    (implies
     (lcm54-address-p address)
     (lcm54-address-p (lcm54-t1 address)))))

(defun-sk lcm54-integer-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lcm54-t index)))))

(defun-sk lcm54-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lcm54-region base)))))

(defun lcm54-linked-p ()
  (if (lcm54-linked-op) t nil))

(defun lcm54-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lcm54-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lcm54-address-base left)
     (lcm54-address-base right)))
   (<=
    (+ (lcm54-address-offset right) right-length)
    (lcm54-address-offset left))
   (<=
    (+ (lcm54-address-offset left) left-length)
    (lcm54-address-offset right))))

(defun lcm54-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lcm54-address-base address))
    (<= 0 (lcm54-address-offset address))
    (<=
     (+ (lcm54-address-offset address) length)
     (lcm54-t (lcm54-address-base address))))))

;; UPDATED-READ is the exact functional update of t_1 at update-address.

(defun lcm54-updated-read
    (update-address update-value address)
  (if (equal address update-address)
      update-value
    (lcm54-t1 address)))

(defun lcm54-pointer-read
    (memory-kind update-address update-value address)
  (if (equal memory-kind :original)
      (lcm54-t1 address)
    (if (equal memory-kind :updated)
        (lcm54-updated-read
         update-address update-value address)
      nil)))

;; This recursion is logically equivalent to the source inductive
;; p_linked_n relation: n = 0 is exactly the bound constructor, while n > 0
;; is exactly the cons constructor followed by its predecessor at n - 1.

(defun lcm54-p-linked-n-p
    (memory-kind update-address update-value
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:original :updated))
   (lcm54-address-p root)
   (lcm54-address-p array)
   (integerp index)
   (integerp n)
   (lcm54-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lcm54-pointer-read
        memory-kind update-address update-value
        (lcm54-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lcm54-valid-rw-p root 4)
      (lcm54-p-linked-n-p
       memory-kind update-address update-value
       (lcm54-pointer-read
        memory-kind update-address update-value
        (lcm54-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lcm54-framed-p ()
  (forall (address)
    (implies
     (lcm54-address-p address)
     (<=
      (lcm54-region
       (lcm54-address-base (lcm54-t1 address)))
      0))))

(defun-sk lcm54-a-separated-from-range-p
    (a array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lcm54-separated-p
      a 1
      (lcm54-t1 (lcm54-shift array index)) 4))))

(defun-sk lcm54-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lcm54-separated-p
      (lcm54-t1 (lcm54-shift array index)) 4
      array-base 2147483646))))

(defun-sk lcm54-range-addresses-distinct-p
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
       (lcm54-t1 (lcm54-shift array left-index))
       (lcm54-t1 (lcm54-shift array right-index)))))))

(defun-sk lcm54-range-addresses-separated-p
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
     (lcm54-separated-p
      (lcm54-t1 (lcm54-shift array left-index)) 4
      (lcm54-t1 (lcm54-shift array right-index)) 4))))

(defun-sk ntp4vc-list-chop-more-post-3-part3-goal54-statement ()
  (forall
   (i1 i2 a1 a i)
   (implies
    (and
     (lcm54-pointer-function-p)
     (lcm54-integer-function-p)
     (lcm54-region-function-p)
     (integerp i1)
     (integerp i2)
     (lcm54-address-p a1)
     (lcm54-address-p a)
     (integerp i))
    (let*
        ((x (+ i1 i2))
         (a2 (lcm54-t1 (lcm54-shift a1 x)))
         (a3 (lcm54-shift a2 0))
         (a4 (lcm54-t1 a3))
         (a5 (lcm54-t1 (lcm54-shift a4 0)))
         (a6 (lcm54-t1 a))
         (a7 (lcm54-shift a1 0))
         (x1 (- i 1))
         (x2 (+ i i1)))
      (implies
       (and
        (equal a5 (lcm54-null-address))
        (not (equal a5 a6))
        (not
         (equal
          a5
          (lcm54-t1 (lcm54-shift a6 0))))
        (<= 0 i1)
        (<= (lcm54-region (lcm54-address-base a)) 0)
        (<= (lcm54-region (lcm54-address-base a1)) 0)
        (<= 2 i)
        (<= (+ 2 i2) i)
        (lcm54-framed-p)
        (lcm54-linked-p)
        (lcm54-is-sint32-p i)
        (lcm54-is-sint32-p i1)
        (lcm54-is-sint32-p i2)
        (lcm54-valid-rw-p a 1)
        (lcm54-valid-rw-p a7 2147483646)
        (lcm54-separated-p a 1 a7 2147483646)
        (lcm54-separated-p a6 4 a7 2147483646)
        (lcm54-valid-rw-p a4 4)
        (lcm54-p-linked-n-p
         :original a3 a5
         a6 a1 i1 (- i 2)
         (lcm54-t1
          (lcm54-shift a1 (- (+ i i1) 2))))
        (lcm54-p-linked-n-p
         :original a3 a5
         a6 a1 i1 x1
         (lcm54-t1
          (lcm54-shift a1 (- (+ i i1) 1))))
        (lcm54-p-linked-n-p
         :original a3 a5
         a6 a1 i1 i a5)
        (lcm54-p-linked-n-p
         :original a3 a5
         a2 a1 x (- i i2) a5)
        (lcm54-a-separated-from-range-p
         a a1 i1 x2)
        (lcm54-range-separated-from-array-p
         a1 i1 x2 a7)
        (lcm54-range-addresses-distinct-p
         a1 i1 x2)
        (lcm54-range-addresses-separated-p
         a1 i1 x2))
       (lcm54-p-linked-n-p
        :updated a3 a5
        (lcm54-updated-read a3 a5 a)
        a1 i1 x1 a5))))))

(value-triple :itpeval-statement-checked)

:q
