;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/klibc_string/memchr_Why3_ide_VCmemchr_loop_inv_5_preserved_goal6:
;; preservation of the memchr loop invariant excluding the sought signed byte
;; from a memory read, under the stated integer bounds, memory validity,
;; address-order, linkedness, constancy, and universally quantified exclusion
;; hypothesis. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mc6-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mc6-address-base (address)
  (car address))

(defun mc6-address-offset (address)
  (cdr address))

(defun mc6-shift (address amount)
  (cons
   (mc6-address-base address)
   (+ (mc6-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1, allocation map t, region function, address order,
;; integer conversions, and the linked and sconst predicates specialized
;; respectively to t and t_1.

(defstub mc6-t1 (address) t)
(defstub mc6-allocation (index) t)
(defstub mc6-region (base) t)
(defstub mc6-addr-le-op (left right) t)
(defstub mc6-to-sint8 (value) t)
(defstub mc6-to-uint32 (value) t)
(defstub mc6-linked-op () t)
(defstub mc6-sconst-op () t)

(defun-sk mc6-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (mc6-address-p address)
      (integerp (mc6-t1 address)))
     (implies
      (integerp index)
      (integerp (mc6-allocation index)))
     (implies
      (integerp base)
      (integerp (mc6-region base)))
     (implies
      (integerp value)
      (and
       (integerp (mc6-to-sint8 value))
       (integerp (mc6-to-uint32 value)))))))

(defun mc6-addr-le-p (left right)
  (if (mc6-addr-le-op left right) t nil))

;; This is the exact source law for address order: for addresses with the same
;; base, addr_le is precisely integer order on offsets.

(defun-sk mc6-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (mc6-address-p left)
      (mc6-address-p right)
      (equal
       (mc6-address-base left)
       (mc6-address-base right)))
     (equal
      (mc6-addr-le-p left right)
      (<=
       (mc6-address-offset left)
       (mc6-address-offset right))))))

(defun mc6-linked-p ()
  (if (mc6-linked-op) t nil))

(defun mc6-sconst-p ()
  (if (mc6-sconst-op) t nil))

(defun mc6-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun mc6-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mc6-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; These are the imported Cint identity laws relevant to the bounded
;; conversion arguments in this verification condition.

(defun-sk mc6-cint-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (implies
       (mc6-is-sint8-p value)
       (equal (mc6-to-sint8 value) value))
      (implies
       (mc6-is-uint32-p value)
       (equal (mc6-to-uint32 value) value))))))

;; Exact unfolding of Memory.valid_rw.

(defun mc6-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mc6-address-base address))
    (<= 0 (mc6-address-offset address))
    (<=
     (+ (mc6-address-offset address) length)
     (mc6-allocation (mc6-address-base address))))))

;; The source loop invariant remains universally quantified over every
;; mathematical integer i_4.

(defun-sk mc6-prefix-excludes-p (a i i1 i3)
  (forall (i4)
    (implies
     (integerp i4)
     (implies
      (and
       (<= 0 i4)
       (< (+ i4 i) i1))
      (not
       (equal
        (mc6-t1 (mc6-shift a i4))
        (mc6-to-sint8 i3)))))))

(defun-sk ntp4vc-memchr-loop-inv-5-preserved-goal6-statement ()
  (forall
   (a i1 i i3 i2)
   (implies
    (and
     (mc6-address-p a)
     (integerp i1)
     (integerp i)
     (integerp i3)
     (integerp i2)
     (mc6-function-types-p)
     (mc6-address-order-law-p)
     (mc6-cint-laws-p))
    (let*
        ((a1 (mc6-shift a (- i1 i)))
         (x (mc6-t1 a1))
         (x1 (mc6-to-sint8 i3)))
      (implies
       (and
        (not (equal i 0))
        (not (equal x x1))
        (< 0 i1)
        (<= 0 i)
        (<= i i1)
        (<= 0 i2)
        (<= (mc6-region (mc6-address-base a)) 0)
        (< (+ i2 (mc6-to-uint32 (- i 1))) i1)
        (<= -128 i3)
        (<= i3 127)
        (mc6-linked-p)
        (mc6-sconst-p)
        (mc6-is-uint32-p i)
        (mc6-is-uint32-p i1)
        (mc6-is-sint32-p i3)
        (mc6-valid-rw-p (mc6-shift a 0) i1)
        (mc6-addr-le-p a a1)
        (mc6-addr-le-p a1 (mc6-shift a i1))
        (mc6-is-sint8-p x)
        (mc6-prefix-excludes-p a i i1 i3))
       (not
        (equal
         (mc6-t1 (mc6-shift a i2))
         x1)))))))

(value-triple :itpeval-statement-checked)

:q
