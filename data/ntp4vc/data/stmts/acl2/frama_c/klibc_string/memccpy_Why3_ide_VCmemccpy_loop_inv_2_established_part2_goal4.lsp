;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/klibc_string/memccpy_Why3_ide_VCmemccpy_loop_inv_2_established_part2_goal4:
;; address ordering from the destination pointer to its positive-length shift,
;; under the stated memory-region, byte-bound, linkedness, constancy, integer
;; range, writable-memory, and separation hypotheses. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mcc4-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mcc4-address-base (address)
  (car address))

(defun mcc4-address-offset (address)
  (cdr address))

(defun mcc4-shift (address amount)
  (cons
   (mcc4-address-base address)
   (+ (mcc4-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; allocation map t, region function, address order, and the linked and sconst
;; predicates specialized respectively to t and t_1.

(defstub mcc4-allocation (index) t)
(defstub mcc4-region (base) t)
(defstub mcc4-addr-le-op (left right) t)
(defstub mcc4-linked-op () t)
(defstub mcc4-sconst-op () t)

(defun-sk mcc4-function-types-p ()
  (forall (index base)
    (and
     (implies
      (integerp index)
      (integerp (mcc4-allocation index)))
     (implies
      (integerp base)
      (integerp (mcc4-region base))))))

(defun mcc4-addr-le-p (left right)
  (if (mcc4-addr-le-op left right) t nil))

;; This is the exact source law for address order: for addresses with the same
;; base, addr_le is precisely integer order on offsets.

(defun-sk mcc4-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (mcc4-address-p left)
      (mcc4-address-p right)
      (equal
       (mcc4-address-base left)
       (mcc4-address-base right)))
     (equal
      (mcc4-addr-le-p left right)
      (<=
       (mcc4-address-offset left)
       (mcc4-address-offset right))))))

(defun mcc4-linked-p ()
  (if (mcc4-linked-op) t nil))

(defun mcc4-sconst-p ()
  (if (mcc4-sconst-op) t nil))

(defun mcc4-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mcc4-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun mcc4-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mcc4-address-base address))
    (<= 0 (mcc4-address-offset address))
    (<=
     (+ (mcc4-address-offset address) length)
     (mcc4-allocation (mcc4-address-base address))))))

(defun mcc4-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mcc4-address-base left)
     (mcc4-address-base right)))
   (<=
    (+ (mcc4-address-offset right) right-length)
    (mcc4-address-offset left))
   (<=
    (+ (mcc4-address-offset left) left-length)
    (mcc4-address-offset right))))

(defun-sk
    ntp4vc-memccpy-loop-inv-2-established-part2-goal4-statement ()
  (forall
   (a a1 i i1)
   (implies
    (and
     (mcc4-address-p a)
     (mcc4-address-p a1)
     (integerp i)
     (integerp i1)
     (mcc4-function-types-p)
     (mcc4-address-order-law-p))
    (let*
        ((a2 (mcc4-shift a 0))
         (a3 (mcc4-shift a1 0)))
      (implies
       (and
        (< 0 i)
        (<= (mcc4-region (mcc4-address-base a)) 0)
        (<= (mcc4-region (mcc4-address-base a1)) 0)
        (<= -128 i1)
        (<= i1 127)
        (mcc4-linked-p)
        (mcc4-sconst-p)
        (mcc4-is-uint32-p i)
        (mcc4-is-sint32-p i1)
        (mcc4-valid-rw-p a2 i)
        (mcc4-valid-rw-p a3 i)
        (mcc4-separated-p a2 i a3 i))
       (mcc4-addr-le-p
        a1
        (mcc4-shift a1 i)))))))

(value-triple :itpeval-statement-checked)

:q
