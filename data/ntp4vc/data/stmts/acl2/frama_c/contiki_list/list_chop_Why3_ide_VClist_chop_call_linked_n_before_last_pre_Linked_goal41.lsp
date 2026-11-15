;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_chop_Why3_ide_VClist_chop_call_linked_n_before_last_pre_Linked_goal41:
;; derivation of the linked-list segment ending at the before-last array
;; pointer from linked-segment, validity, framing, and separation hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lcg41-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lcg41-address-base (address)
  (car address))

(defun lcg41-address-offset (address)
  (cdr address))

(defun lcg41-shift (address amount)
  (cons
   (lcg41-address-base address)
   (+ (lcg41-address-offset address) amount)))

(defun lcg41-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer allocation function t, fixed region
;; operation, and the linked proposition specialized to t.

(defstub lcg41-t1 (address) t)
(defstub lcg41-t (index) t)
(defstub lcg41-region (base) t)
(defstub lcg41-linked-op () t)

(defun-sk lcg41-pointer-function-p ()
  (forall (address)
    (implies
     (lcg41-address-p address)
     (lcg41-address-p (lcg41-t1 address)))))

(defun-sk lcg41-integer-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lcg41-t index)))))

(defun-sk lcg41-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lcg41-region base)))))

(defun lcg41-linked-p ()
  (if (lcg41-linked-op) t nil))

(defun lcg41-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lcg41-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lcg41-address-base left)
     (lcg41-address-base right)))
   (<=
    (+ (lcg41-address-offset right) right-length)
    (lcg41-address-offset left))
   (<=
    (+ (lcg41-address-offset left) left-length)
    (lcg41-address-offset right))))

(defun lcg41-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lcg41-address-base address))
    (<= 0 (lcg41-address-offset address))
    (<=
     (+ (lcg41-address-offset address) length)
     (lcg41-t (lcg41-address-base address))))))

;; This recursion is logically equivalent to the source inductive
;; p_linked_n relation: n = 0 is exactly the bound constructor, while n > 0
;; is exactly the cons constructor followed by its predecessor at n - 1.

(defun lcg41-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lcg41-address-p root)
   (lcg41-address-p array)
   (integerp index)
   (integerp n)
   (lcg41-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lcg41-t1 (lcg41-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lcg41-valid-rw-p root 4)
      (lcg41-p-linked-n-p
       (lcg41-t1 (lcg41-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lcg41-framed-p ()
  (forall (address)
    (implies
     (lcg41-address-p address)
     (<=
      (lcg41-region
       (lcg41-address-base (lcg41-t1 address)))
      0))))

(defun-sk lcg41-a-separated-from-range-p
    (a array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lcg41-separated-p
      a 1
      (lcg41-t1 (lcg41-shift array index)) 4))))

(defun-sk lcg41-range-separated-from-array-p
    (array lower upper array-base)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lcg41-separated-p
      (lcg41-t1 (lcg41-shift array index)) 4
      array-base 2147483646))))

(defun-sk lcg41-range-addresses-distinct-p
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
       (lcg41-t1 (lcg41-shift array left-index))
       (lcg41-t1 (lcg41-shift array right-index)))))))

(defun-sk lcg41-range-addresses-separated-p
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
     (lcg41-separated-p
      (lcg41-t1 (lcg41-shift array left-index)) 4
      (lcg41-t1 (lcg41-shift array right-index)) 4))))

(defun-sk
    ntp4vc-list-chop-call-linked-n-before-last-pre-linked-goal41-statement ()
  (forall
   (i1 i2 a1 a i)
   (implies
    (and
     (lcg41-pointer-function-p)
     (lcg41-integer-function-p)
     (lcg41-region-function-p)
     (integerp i1)
     (integerp i2)
     (lcg41-address-p a1)
     (lcg41-address-p a)
     (integerp i))
    (let*
        ((x (+ i1 i2))
         (a2 (lcg41-t1 (lcg41-shift a1 x)))
         (a3 (lcg41-t1 (lcg41-shift a2 0)))
         (a4 (lcg41-t1 (lcg41-shift a3 0)))
         (a5 (lcg41-t1 a))
         (a6 (lcg41-shift a1 0))
         (x1 (+ i i1)))
      (implies
       (and
        (equal a4 (lcg41-null-address))
        (not (equal a4 a5))
        (not
         (equal
          a4
          (lcg41-t1 (lcg41-shift a5 0))))
        (<= (lcg41-region (lcg41-address-base a)) 0)
        (<= (lcg41-region (lcg41-address-base a1)) 0)
        (<= (+ 2 i2) i)
        (lcg41-framed-p)
        (lcg41-linked-p)
        (lcg41-is-sint32-p i)
        (lcg41-is-sint32-p i1)
        (lcg41-is-sint32-p i2)
        (lcg41-valid-rw-p a 1)
        (lcg41-valid-rw-p a6 2147483646)
        (lcg41-separated-p a 1 a6 2147483646)
        (lcg41-separated-p a5 4 a6 2147483646)
        (lcg41-valid-rw-p a3 4)
        (lcg41-p-linked-n-p
         a5 a1 i1 i a4)
        (lcg41-p-linked-n-p
         a2 a1 x (- i i2) a4)
        (lcg41-a-separated-from-range-p
         a a1 i1 x1)
        (lcg41-range-separated-from-array-p
         a1 i1 x1 a6)
        (lcg41-range-addresses-distinct-p
         a1 i1 x1)
        (lcg41-range-addresses-separated-p
         a1 i1 x1))
       (lcg41-p-linked-n-p
        a5 a1 i1 (- i 1)
        (lcg41-t1
         (lcg41-shift a1 (- (+ i i1) 1)))))))))

(value-triple :itpeval-statement-checked)

:q
